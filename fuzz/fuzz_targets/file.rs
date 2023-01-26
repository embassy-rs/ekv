#![no_main]

use std::cmp::Ordering;

use ekv::config::{FileID, PAGE_COUNT, PAGE_SIZE};
use ekv::file::{FileManager, FileSearcher, ReadError, SeekDirection};
use ekv::flash::MemFlash;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

const MAX_LEN: usize = 1024;

fuzz_target!(|data: Input| { fuzz(data) });

#[derive(Arbitrary, Debug)]
struct Input {
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
enum Op {
    Append { len: usize },
    Search { id: u32 },
    Commit,
    Truncate { i: usize },
}

struct Record {
    id: u32,
    len: usize,
    offs: usize,
}

fn fuzz(ops: Input) {
    let logging = std::env::var_os("RUST_LOG").is_some();
    if logging {
        env_logger::init();
    }

    let mut f = MemFlash::new();
    let mut m = FileManager::new(&mut f);
    m.format();
    m.mount().unwrap();

    const FILE_ID: FileID = 1;

    let mut w = None;
    let mut buf = [0; MAX_LEN];

    let mut records = Vec::new();
    let mut write_offs: usize = 0;
    let mut trunc_offs: usize = 0;

    for op in ops.ops {
        match op {
            Op::Append { len } => {
                if len > MAX_LEN {
                    continue;
                }

                if (m.used_pages() + 3) * PAGE_SIZE + len >= PAGE_COUNT * PAGE_SIZE {
                    continue;
                }

                // Open file if not open already.
                let w = w.get_or_insert_with(|| m.write(FILE_ID).unwrap());

                let id = (records.len() * 2 + 1) as u32;
                records.push(Record {
                    id,
                    len,
                    offs: write_offs,
                });

                w.write(&mut m, &id.to_le_bytes()).unwrap();
                buf[..len].fill(id as u8);
                w.write(&mut m, &buf[..len]).unwrap();
                w.record_end();

                write_offs += 4 + len;
            }
            Op::Commit => {
                if let Some(w) = &mut w {
                    m.commit(w).unwrap();
                }
                w = None;
            }
            Op::Search { id } => {
                if let Some(w) = &mut w {
                    m.commit(w).unwrap();
                }
                w = None;

                if logging {
                    m.dump();
                }

                let mut s = FileSearcher::new(m.read(FILE_ID));
                let mut ok = s.start(&mut m).unwrap();
                let mut found = false;

                // Binary search.
                while ok {
                    let mut got_id = [0u8; 4];
                    s.reader().read(&mut m, &mut got_id).unwrap();
                    let got_id = u32::from_le_bytes(got_id);
                    assert!(got_id % 2 == 1);

                    let dir = match got_id.cmp(&id) {
                        Ordering::Equal => {
                            found = true;
                            break;
                        }
                        Ordering::Less => SeekDirection::Right,
                        Ordering::Greater => SeekDirection::Left,
                    };

                    // Not found, do a binary search step.
                    ok = s.seek(&mut m, dir).unwrap();
                }

                // Linear search
                loop {
                    let mut got_id = [0u8; 4];
                    match s.reader().read(&mut m, &mut got_id) {
                        Ok(()) => {}
                        Err(ReadError::Corrupted) => panic!("corrupted!!"),
                        Err(ReadError::Eof) => break,
                        Err(ReadError::Flash(e)) => match e {},
                    }
                    let got_id = u32::from_le_bytes(got_id);
                    assert!(got_id % 2 == 1);

                    match got_id.cmp(&id) {
                        Ordering::Equal => {
                            found = true;
                            break;
                        }
                        Ordering::Less => {}
                        Ordering::Greater => break,
                    }

                    let r = &records[got_id as usize / 2];
                    s.reader().skip(&mut m, r.len).unwrap();
                }

                let i = id as usize / 2;
                let should_found = id % 2 == 1 && i < records.len() && records[i].offs >= trunc_offs;
                assert_eq!(found, should_found);
            }
            Op::Truncate { i } => {
                if i >= records.len() {
                    continue;
                }

                let offs = records[i].offs;
                if offs <= trunc_offs {
                    continue;
                }

                if let Some(w) = &mut w {
                    m.commit(w).unwrap();
                }
                w = None;

                let mut tx = m.transaction();
                tx.truncate(FILE_ID, offs - trunc_offs).unwrap();
                tx.commit().unwrap();

                trunc_offs = offs;
            }
        }
    }
}
