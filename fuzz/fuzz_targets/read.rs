#![no_main]
use ekv::flash::MemFlash;
use ekv::Database;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| { fuzz(data) });

fn fuzz(data: &[u8]) {
    let mut f = MemFlash::new();
    let n = f.data.len().min(data.len());
    f.data[..n].copy_from_slice(&data[..n]);

    let mut db = Database::new(&mut f);
    let mut buf = [0; 64];
    db.read_transaction().read(b"foo", &mut buf);
}
