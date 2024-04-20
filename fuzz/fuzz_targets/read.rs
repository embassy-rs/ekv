#![no_main]
use ekv::flash::MemFlash;
use ekv::{Config, Database};
use embassy_sync::blocking_mutex::raw::NoopRawMutex;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| fuzz(data));

fn fuzz(data: &[u8]) {
    if std::env::var_os("RUST_LOG").is_some() {
        env_logger::init();
    }
    let dump = std::env::var("DUMP") == Ok("1".to_string());

    tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap()
        .block_on(fuzz_inner(data, dump))
}

async fn fuzz_inner(data: &[u8], dump: bool) {
    let mut f = MemFlash::new();
    let n = f.data.len().min(data.len());
    f.data[..n].copy_from_slice(&data[..n]);

    let config = Config::default();
    let db = Database::<_, NoopRawMutex>::new(&mut f, config);

    if dump {
        db.dump().await;
    }

    let mut buf = [0; 64];
    let rtx = db.read_transaction().await;
    _ = rtx.read(b"foo", &mut buf).await;
    drop(rtx);

    for _ in 0..100 {
        let mut wtx = db.write_transaction().await;
        _ = wtx.write(b"foo", b"blah").await;
        _ = wtx.commit().await;
    }

    let rtx = db.read_transaction().await;
    _ = rtx.read(b"foo", &mut buf).await;
    drop(rtx);
}
