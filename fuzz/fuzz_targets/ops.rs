#![no_main]

use std::collections::HashMap;

use ekv::flash::MemFlash;
use ekv::{Config, Database, WriteError};
use embassy_sync::blocking_mutex::raw::NoopRawMutex;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;

const VAL_MAX_LEN: usize = 2500;

fuzz_target!(|data: Input| { fuzz(data) });

#[derive(Arbitrary, Debug)]
struct Input {
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
enum Op {
    Insert(InsertOp),
}

#[derive(Arbitrary, Debug)]
struct InsertOp {
    key: u16,
    value_len: usize,
}

fn fuzz(ops: Input) {
    let logging = std::env::var_os("RUST_LOG").is_some();
    if logging {
        env_logger::init();
    }

    tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap()
        .block_on(fuzz_inner(ops))
}

async fn fuzz_inner(ops: Input) {
    let mut f = MemFlash::new();
    let config = Config::default();
    let db = Database::<_, NoopRawMutex>::new(&mut f, config);
    db.format().await.unwrap();

    // Mirror hashmap. Should always match F
    let mut m = HashMap::new();

    let mut buf = [0; VAL_MAX_LEN];

    for (i, op) in ops.ops.into_iter().enumerate() {
        log::info!("==================================================== op: {:?}", op);

        match op {
            Op::Insert(op) => {
                if op.value_len > VAL_MAX_LEN {
                    continue;
                }
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
        }

        db.dump().await;

        // Check everything
        for (key, val) in &m {
            let mut rtx = db.read_transaction().await;
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
