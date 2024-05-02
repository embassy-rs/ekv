#![no_main]

use std::collections::BTreeMap;
use std::ops::Bound;

use ekv::config::{MAX_KEY_SIZE, MAX_VALUE_SIZE};
use ekv::flash::MemFlash;
use ekv::{Config, Database, ReadError, WriteError};
use embassy_sync::blocking_mutex::raw::NoopRawMutex;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: Input| fuzz(data));

#[derive(Arbitrary, Debug)]
struct Input {
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
enum Op {
    Insert(InsertOp),
    Delete(DeleteOp),
    Read(ReadOp),
    ReadRange(ReadRangeOp),
}

#[derive(Arbitrary, Debug)]
struct InsertOp {
    key: u16,
    value_len: usize,
}

#[derive(Arbitrary, Debug)]
struct DeleteOp {
    key: u16,
}

#[derive(Arbitrary, Debug)]
struct ReadOp {
    key: u16,
}

#[derive(Arbitrary, Debug)]
struct ReadRangeOp {
    lower_bound: Bound<u16>,
    upper_bound: Bound<u16>,
}

fn fuzz(ops: Input) {
    if std::env::var_os("RUST_LOG").is_some() {
        env_logger::init();
    }
    let dump = std::env::var("DUMP") == Ok("1".to_string());

    tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap()
        .block_on(fuzz_inner(ops, dump))
}

async fn fuzz_inner(ops: Input, dump: bool) {
    let mut f = MemFlash::new();
    let config = Config::default();
    let db = Database::<_, NoopRawMutex>::new(&mut f, config);
    db.format().await.unwrap();

    // Mirror hashmap. Should always match F
    let mut m = BTreeMap::new();

    let mut kbuf = [0; MAX_KEY_SIZE];
    let mut buf = [0; MAX_VALUE_SIZE];

    for (i, op) in ops.ops.into_iter().enumerate() {
        log::info!("==================================================== op: {:?}", op);

        match op {
            Op::Insert(mut op) => {
                op.value_len %= MAX_VALUE_SIZE + 1;

                let key = op.key.to_be_bytes();
                let mut val = vec![0; op.value_len];
                let val_num = i.to_be_bytes();
                let n = val_num.len().min(val.len());
                val[..n].copy_from_slice(&val_num[..n]);

                // Write to DB
                let mut wtx = db.write_transaction().await;
                match wtx.write(&key, &val).await {
                    Ok(()) => {}
                    Err(WriteError::Full) => continue,
                    Err(e) => panic!("write error: {:?}", e),
                }
                wtx.commit().await.unwrap();

                // Write to mirror
                m.insert(key.to_vec(), val);
            }
            Op::Delete(op) => {
                let key = op.key.to_be_bytes();

                // Write to DB
                let mut wtx = db.write_transaction().await;
                match wtx.delete(&key).await {
                    Ok(()) => {}
                    Err(WriteError::Full) => continue,
                    Err(e) => panic!("write error: {:?}", e),
                }
                wtx.commit().await.unwrap();

                // Write to mirror
                m.remove(&key[..]);
            }
            Op::Read(op) => {
                let key = op.key.to_be_bytes();

                // Read from DB
                let rtx = db.read_transaction().await;
                let got_val = match rtx.read(&key, &mut buf).await {
                    Ok(n) => Some(&buf[..n]),
                    Err(ReadError::KeyNotFound) => None,
                    Err(e) => panic!("write error: {:?}", e),
                };

                // Write to mirror
                let want_val = m.get(&key[..]).map(|v| &v[..]);

                assert_eq!(got_val, want_val);
            }
            Op::ReadRange(op) => {
                // ignore reversed ranges, otherwise BTreeMap::range panics.
                if let (Bound::Excluded(l) | Bound::Included(l), Bound::Excluded(u) | Bound::Included(u)) =
                    (op.lower_bound, op.upper_bound)
                {
                    if l > u {
                        continue;
                    }
                }
                // Tis also panics....
                if let (Bound::Excluded(l), Bound::Excluded(u)) = (op.lower_bound, op.upper_bound) {
                    if l == u {
                        continue;
                    }
                }

                let mut lower_buf = [0; 2];
                let lower_bound = op.lower_bound.map(|k| {
                    lower_buf = k.to_be_bytes();
                    &lower_buf[..]
                });
                let mut upper_buf = [0; 2];
                let upper_bound = op.upper_bound.map(|k| {
                    upper_buf = k.to_be_bytes();
                    &upper_buf[..]
                });

                // Get cursor from DB
                let rtx = db.read_transaction().await;
                let mut cur = match rtx.read_range((lower_bound, upper_bound)).await {
                    Ok(cur) => cur,
                    Err(e) => panic!("read_range error: {:?}", e),
                };

                // iterate the mirror map.
                for (want_k, want_v) in m.range((
                    op.lower_bound.map(|k| k.to_be_bytes().to_vec()),
                    op.upper_bound.map(|k| k.to_be_bytes().to_vec()),
                )) {
                    match cur.next(&mut kbuf, &mut buf).await {
                        Err(e) => panic!("Cursor::next error: {:?}", e),
                        Ok(None) => panic!("Cursor returned None too early."),
                        Ok(Some((klen, vlen))) => {
                            let got_k = &kbuf[..klen];
                            let got_v = &buf[..vlen];
                            assert_eq!(want_k, got_k);
                            assert_eq!(want_v, got_v);
                        }
                    }
                }

                match cur.next(&mut kbuf, &mut buf).await {
                    Err(e) => panic!("Cursor::next error: {:?}", e),
                    Ok(None) => {}
                    Ok(Some(_)) => panic!("Cursor::next didn't return None when it should."),
                }
            }
        }

        if dump {
            db.dump().await;
        }

        // Check everything
        for (key, val) in &m {
            let rtx = db.read_transaction().await;
            let n = rtx.read(key, &mut buf).await.unwrap();
            let got_val = &buf[..n];

            if val != got_val {
                panic!(
                    "mismatch found!\nkey={:02x?}\nwant val={:02x?}\ngot val={:02x?}",
                    key, val, got_val
                );
            }
        }
    }
}
