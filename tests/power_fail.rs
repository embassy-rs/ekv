#![cfg(all(
    feature = "crc",
    feature = "max-page-count-384",
    feature = "max-key-size-16",
    feature = "max-value-size-512",
    feature = "max-chunk-size-512"
))]

use std::{
    cell::RefCell,
    future::Future,
    rc::Rc,
    task::{Context, Poll, Waker},
};

use ekv::{
    config::{ALIGN, CRC, ERASE_VALUE, MAX_PAGE_COUNT, PAGE_SIZE},
    flash::{Flash, PageID},
    Config, Database,
};
use embassy_sync::blocking_mutex::raw::NoopRawMutex;

const PAGES: usize = MAX_PAGE_COUNT - 1;
type Db = Database<Nor, NoopRawMutex>;

#[derive(Clone, Debug)]
struct Operation {
    erase: bool,
    page: usize,
    offset: usize,
    data: Vec<u8>,
}

struct State {
    bytes: Vec<u8>,
    operations: Vec<Operation>,
    cut: Option<(usize, usize)>,
}

#[derive(Clone)]
struct Nor(Rc<RefCell<State>>);

impl Nor {
    fn new(bytes: Vec<u8>) -> Self {
        Self(Rc::new(RefCell::new(State {
            bytes,
            operations: Vec::new(),
            cut: None,
        })))
    }

    async fn mutate(&mut self, operation: Operation) {
        let cut = {
            let mut state = self.0.borrow_mut();
            let prefix = state
                .cut
                .filter(|(index, _)| *index == state.operations.len())
                .map(|(_, prefix)| prefix);
            let start = operation.page * PAGE_SIZE + operation.offset;
            let target = &mut state.bytes[start..][..operation.data.len()];
            if !operation.erase {
                assert!(target.iter().all(|&byte| byte == ERASE_VALUE));
            }
            for (index, (target, source)) in target.iter_mut().zip(&operation.data).enumerate() {
                if prefix.is_none_or(|prefix| index < prefix) {
                    *target = *source;
                }
            }
            state.operations.push(operation);
            prefix.is_some()
        };
        if cut {
            std::future::pending::<()>().await;
        }
    }
}

impl Flash for Nor {
    type Error = std::convert::Infallible;

    fn page_count(&self) -> usize {
        PAGES
    }

    async fn erase(&mut self, page: PageID) -> Result<(), Self::Error> {
        self.mutate(Operation {
            erase: true,
            page: page.index(),
            offset: 0,
            data: vec![ERASE_VALUE; PAGE_SIZE],
        })
        .await;
        Ok(())
    }

    async fn read(&mut self, page: PageID, offset: usize, data: &mut [u8]) -> Result<(), Self::Error> {
        assert!(offset.is_multiple_of(ALIGN) && data.len().is_multiple_of(ALIGN));
        let start = page.index() * PAGE_SIZE + offset;
        data.copy_from_slice(&self.0.borrow().bytes[start..][..data.len()]);
        Ok(())
    }

    async fn write(&mut self, page: PageID, offset: usize, data: &[u8]) -> Result<(), Self::Error> {
        assert!(offset.is_multiple_of(ALIGN) && data.len().is_multiple_of(ALIGN));
        self.mutate(Operation {
            erase: false,
            page: page.index(),
            offset,
            data: data.to_vec(),
        })
        .await;
        Ok(())
    }
}

fn complete<F: Future>(future: F) -> F::Output {
    let mut future = std::pin::pin!(future);
    match future.as_mut().poll(&mut Context::from_waker(Waker::noop())) {
        Poll::Ready(output) => output,
        Poll::Pending => panic!("unexpected pending flash operation"),
    }
}

async fn update(db: &Db, version: u64) {
    let value = version.to_le_bytes();
    let mut transaction = db.write_transaction().await;
    transaction.write(b"a", &value).await.unwrap();
    transaction.write(b"b", &value).await.unwrap();
    transaction.commit().await.unwrap();
}

fn baseline() -> Vec<u8> {
    assert!(CRC);
    let flash = Nor::new(vec![ERASE_VALUE; PAGES * PAGE_SIZE]);
    let db = Db::new(flash.clone(), Config::default());
    complete(db.format()).unwrap();
    complete(update(&db, 1));
    let bytes = flash.0.borrow().bytes.clone();
    bytes
}

fn commit_reproduction() -> (Vec<u8>, u64, u64, Vec<Operation>) {
    let baseline = baseline();
    let (reference_flash, reference_db) = mounted(baseline.clone());
    complete(update(&reference_db, 2));
    let operations = reference_flash.0.borrow().operations.clone();

    (baseline, 1, 2, operations)
}

fn metadata_rollover_reproduction() -> (Vec<u8>, u64, u64, Vec<Operation>) {
    let mut baseline = baseline();
    let metadata_magic = 0x1d81bcde_u32.to_le_bytes();

    for version in 2..=500 {
        let (flash, db) = mounted(baseline.clone());
        complete(update(&db, version));
        let state = flash.0.borrow();
        if state
            .operations
            .iter()
            .any(|operation| !operation.erase && operation.offset == 0 && operation.data.starts_with(&metadata_magic))
        {
            return (baseline, version - 1, version, state.operations.clone());
        }
        baseline.clone_from(&state.bytes);
    }

    panic!("test did not reach metadata page replacement");
}

fn read_version(db: &Db) -> Result<u64, String> {
    complete(async {
        let transaction = db.read_transaction().await;
        let mut a = [0; 8];
        let mut b = [0; 8];
        let a_len = transaction
            .read(b"a", &mut a)
            .await
            .map_err(|error| format!("{error:?}"))?;
        let b_len = transaction
            .read(b"b", &mut b)
            .await
            .map_err(|error| format!("{error:?}"))?;
        if a_len != 8 || b_len != 8 {
            return Err(format!("unexpected value lengths: {a_len}, {b_len}"));
        }
        if a != b {
            return Err("transaction exposed mixed versions".into());
        }
        Ok(u64::from_le_bytes(a))
    })
}

fn mount_after_cut(
    baseline: &[u8],
    old_version: u64,
    new_version: u64,
    cut_at: usize,
    prefix: usize,
) -> Result<(), String> {
    let (flash, db) = mounted(baseline.to_vec());
    flash.0.borrow_mut().cut = Some((cut_at, prefix));

    let mut commit = Box::pin(update(&db, new_version));
    assert!(matches!(
        commit.as_mut().poll(&mut Context::from_waker(Waker::noop())),
        Poll::Pending
    ));
    drop(commit);
    drop(db);

    let rebooted = Db::new(Nor::new(flash.0.borrow().bytes.clone()), Config::default());
    complete(rebooted.mount()).map_err(|error| format!("{error:?}"))?;
    let recovered_version = read_version(&rebooted)?;
    if recovered_version != old_version && recovered_version != new_version {
        return Err(format!("unexpected recovered version {recovered_version}"));
    }
    Ok(())
}

fn exercise_each_write(baseline: &[u8], old_version: u64, new_version: u64, operations: &[Operation]) {
    let mut failure_report = Vec::new();

    for (cut_at, operation) in operations.iter().enumerate() {
        if operation.erase {
            continue;
        }

        let mut working = Vec::new();
        let mut failing = Vec::new();
        for prefix in 0..=operation.data.len() {
            match mount_after_cut(baseline, old_version, new_version, cut_at, prefix) {
                Ok(()) => working.push(prefix),
                Err(error) => failing.push(format!("{prefix} ({error})")),
            }
        }

        println!(
            "write {cut_at}: page={} offset={} len={} working={working:?} failing={failing:?}",
            operation.page,
            operation.offset,
            operation.data.len()
        );

        if !failing.is_empty() {
            failure_report.push(format!(
                "write {cut_at} ({operation:?})\n  working prefixes: {working:?}\n  failing prefixes: {failing:?}"
            ));
        }
    }

    assert!(
        failure_report.is_empty(),
        "power-loss failures:\n{}",
        failure_report.join("\n")
    );
}

#[test]
fn mount_survives_each_interrupted_write_during_commit() {
    let (baseline, old_version, new_version, operations) = commit_reproduction();
    exercise_each_write(&baseline, old_version, new_version, &operations);
}

#[test]
fn mount_survives_each_interrupted_write_during_metadata_rollover() {
    let (baseline, old_version, new_version, operations) = metadata_rollover_reproduction();
    exercise_each_write(&baseline, old_version, new_version, &operations);
}

fn mounted(bytes: Vec<u8>) -> (Nor, Db) {
    let flash = Nor::new(bytes);
    let db = Db::new(flash.clone(), Config::default());
    complete(db.mount()).unwrap();
    flash.0.borrow_mut().operations.clear();
    (flash, db)
}
