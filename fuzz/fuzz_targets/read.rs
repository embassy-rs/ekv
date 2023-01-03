#![no_main]
use ekv::flash::MemFlash;
use ekv::Database;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| { fuzz(data) });

fn fuzz(data: &[u8]) {
    //pretty_env_logger::init();

    let mut f = MemFlash::new();
    let n = f.data.len().min(data.len());
    f.data[..n].copy_from_slice(&data[..n]);

    let Ok(mut db) = Database::new(&mut f) else { return };

    let mut buf = [0; 64];
    let Ok(mut rtx) = db.read_transaction() else { return };
    _ = rtx.read(b"foo", &mut buf);

    for _ in 0..100 {
        let Ok(mut wtx) = db.write_transaction() else { return };
        _ = wtx.write(b"foo", b"blah");
        _ = wtx.commit();
    }

    let Ok(mut rtx) = db.read_transaction() else { return };
    _ = rtx.read(b"foo", &mut buf);
}
