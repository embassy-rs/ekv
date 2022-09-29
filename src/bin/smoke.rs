use std::collections::HashMap;

use ekv::flash::MemFlash;
use ekv::Database;
use rand::Rng;

const KEY_COUNT: usize = 100;
const KEY_MIN_LEN: usize = 1;
const KEY_MAX_LEN: usize = 10;
const VAL_MIN_LEN: usize = 1;
const VAL_MAX_LEN: usize = 100;

fn rand(max: usize) -> usize {
    rand::thread_rng().gen_range(0..max)
}

fn rand_between(from: usize, to: usize) -> usize {
    rand::thread_rng().gen_range(from..=to)
}

fn rand_data(len: usize) -> Vec<u8> {
    let mut res = vec![0; len];
    rand::thread_rng().fill(&mut res[..]);
    res
}

fn main() {
    println!("Hi there!");

    // Generate keys
    let mut keys = Vec::new();
    while keys.len() < KEY_COUNT {
        let key = rand_data(rand_between(KEY_MIN_LEN, KEY_MAX_LEN));
        if !keys.contains(&key) {
            keys.push(key)
        }
    }

    let mut f = MemFlash::new();
    Database::format(&mut f);
    let db = Database::new(&mut f);

    // Mirror hashmap. Should always match F
    let mut m = HashMap::new();

    let mut buf = [0; VAL_MAX_LEN];

    for _ in 0..1000000 {
        let key = &keys[rand(KEY_COUNT)];
        let value = rand_data(rand_between(VAL_MIN_LEN, VAL_MAX_LEN));

        //println!("write {:?} = {:?}", key, value);

        // Write to DB
        let mut wtx = db.write_transaction();
        wtx.write(key, &value);
        wtx.commit();

        // Write to mirror
        m.insert(key.clone(), value);

        // Check everything
        for i in 0..KEY_COUNT {
            let key = &keys[i];

            let mut rtx = db.read_transaction();
            let n = rtx.read(key, &mut buf);
            let val1 = &buf[..n];
            let val2 = m.get(key).map(|v| &v[..]).unwrap_or(&[]);

            assert_eq!(val1, val2);
        }
    }
}
