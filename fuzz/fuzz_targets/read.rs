#![no_main]
use ekv::flash::MemFlash;
use ekv::Database;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| { fuzz(data) });

fn fuzz(data: &[u8]) {
    let logging = std::env::var_os("RUST_LOG").is_some();
    if logging {
        env_logger::init();
    }

    tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap()
        .block_on(fuzz_inner(data, logging))
}

async fn fuzz_inner(data: &[u8], logging: bool) {
    let mut f = MemFlash::new();
    let n = f.data.len().min(data.len());
    f.data[..n].copy_from_slice(&data[..n]);

    let Ok(mut db) = Database::new(&mut f).await else { return };

    if logging {
        db.dump().await;
    }

    let mut buf = [0; 64];
    let Ok(mut rtx) = db.read_transaction().await else { return };
    _ = rtx.read(b"foo", &mut buf).await;

    for _ in 0..100 {
        let Ok(mut wtx) = db.write_transaction().await else { return };
        _ = wtx.write(b"foo", b"blah").await;
        _ = wtx.commit().await;
    }

    let Ok(mut rtx) = db.read_transaction().await else { return };
    _ = rtx.read(b"foo", &mut buf).await;
}
