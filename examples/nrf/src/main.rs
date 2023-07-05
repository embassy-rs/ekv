#![no_std]
#![no_main]
#![feature(type_alias_impl_trait)]
#![feature(async_fn_in_trait)]
#![feature(impl_trait_projections)]
#![allow(incomplete_features)]
#![recursion_limit = "256"]

// must go first
mod fmt;

use core::convert::Infallible;

#[cfg(feature = "defmt")]
use defmt_rtt as _;
use ekv::flash::PageID;
use ekv::{config, Config, Database};
use embassy_executor::Spawner;
use embassy_nrf::rng::Rng;
use embassy_nrf::{bind_interrupts, pac, peripherals, qspi, rng};
use embassy_sync::blocking_mutex::raw::NoopRawMutex;
use embassy_time::Instant;
use heapless::Vec;
use panic_probe as _;
use rand_core::RngCore;

bind_interrupts!(struct Irqs {
    QSPI => qspi::InterruptHandler<peripherals::QSPI>;
    RNG => rng::InterruptHandler<peripherals::RNG>;
});

struct Flash<'a> {
    qspi: qspi::Qspi<'a, peripherals::QSPI>,
}

// Workaround for alignment requirements.
#[repr(C, align(4))]
struct AlignedBuf([u8; 4096]);

static mut BUF: AlignedBuf = AlignedBuf([0; 4096]);

impl<'a> ekv::flash::Flash for Flash<'a> {
    type Error = Infallible;

    fn page_count(&self) -> usize {
        config::MAX_PAGE_COUNT
    }

    async fn erase(&mut self, page_id: PageID) -> Result<(), Self::Error> {
        self.qspi
            .erase((page_id.index() * config::PAGE_SIZE) as u32)
            .await
            .unwrap();
        Ok(())
    }

    async fn read(&mut self, page_id: PageID, offset: usize, data: &mut [u8]) -> Result<(), Self::Error> {
        let address = page_id.index() * config::PAGE_SIZE + offset;
        unsafe {
            self.qspi.read(address as u32, &mut BUF.0[..data.len()]).await.unwrap();
            data.copy_from_slice(&BUF.0[..data.len()])
        }
        Ok(())
    }

    async fn write(&mut self, page_id: PageID, offset: usize, data: &[u8]) -> Result<(), Self::Error> {
        let address = page_id.index() * config::PAGE_SIZE + offset;
        unsafe {
            BUF.0[..data.len()].copy_from_slice(data);
            self.qspi.write(address as u32, &BUF.0[..data.len()]).await.unwrap();
        }
        Ok(())
    }
}


pub struct FakeFlash {}

impl ekv::flash::Flash for FakeFlash {
    type Error = core::convert::Infallible;

    fn page_count(&self) -> usize {
        ekv::config::MAX_PAGE_COUNT
    }

    async fn erase(&mut self, page_id: PageID) -> Result<(), Self::Error> {
        Ok(())
    }

    async fn read(&mut self, page_id: PageID, offset: usize, data: &mut [u8]) -> Result<(), Self::Error> {
        Ok(())
    }

    async fn write(&mut self, page_id: PageID, offset: usize, data: &[u8]) -> Result<(), Self::Error> {
        Ok(())
    }
}



#[embassy_executor::main]
async fn main(_spawner: Spawner) { main0(_spawner).await; main1(_spawner).await; }
async fn main0(_spawner: Spawner) { main1(_spawner).await; main2(_spawner).await; }
async fn main1(_spawner: Spawner) { main2(_spawner).await; main3(_spawner).await; }
async fn main2(_spawner: Spawner) { main3(_spawner).await; main4(_spawner).await; }
async fn main3(_spawner: Spawner) { main4(_spawner).await; main5(_spawner).await; }
async fn main4(_spawner: Spawner) { main5(_spawner).await; main6(_spawner).await; }
async fn main5(_spawner: Spawner) { main6(_spawner).await; main7(_spawner).await; }
async fn main6(_spawner: Spawner) { main7(_spawner).await; main8(_spawner).await; }
async fn main7(_spawner: Spawner) { main8(_spawner).await; main9(_spawner).await; }
async fn main8(_spawner: Spawner) { main9(_spawner).await; main10(_spawner).await; }
async fn main9(_spawner: Spawner) { main10(_spawner).await; main11(_spawner).await; }
async fn main10(_spawner: Spawner) { main11(_spawner).await; main12(_spawner).await; }
async fn main11(_spawner: Spawner) { main12(_spawner).await; main13(_spawner).await; }
async fn main12(_spawner: Spawner) { main13(_spawner).await; main14(_spawner).await; }
async fn main13(_spawner: Spawner) { main14(_spawner).await; main15(_spawner).await; }
async fn main14(_spawner: Spawner) { main15(_spawner).await; main16(_spawner).await; }
async fn main15(_spawner: Spawner) { main16(_spawner).await; main17(_spawner).await; }
async fn main16(_spawner: Spawner) { main17(_spawner).await; main18(_spawner).await; }
async fn main17(_spawner: Spawner) { main18(_spawner).await; main19(_spawner).await; }
async fn main18(_spawner: Spawner) { main19(_spawner).await; main20(_spawner).await; }
async fn main19(_spawner: Spawner) { main20(_spawner).await; }
async fn main20(_spawner: Spawner) {
    let random_seed = 0;

    let mut f = FakeFlash{};

    let mut config = Config::default();
    config.random_seed = random_seed;
    let db = Database::<_, NoopRawMutex>::new(&mut f, config);

    unwrap!(db.format().await);

    const KEY_COUNT: usize = 100;
    const TX_SIZE: usize = 10;

    info!("Writing {} keys...", KEY_COUNT);
    for k in 0..KEY_COUNT / TX_SIZE {
        let mut wtx = db.write_transaction().await;
        for j in 0..TX_SIZE {
            let i = k * TX_SIZE + j;
            let key = make_key(i);
            let val = make_value(i);

            wtx.write(&key, &val).await.unwrap();
        }
        wtx.commit().await.unwrap();
    }
}

fn make_key(i: usize) -> [u8; 2] {
    (i as u16).to_be_bytes()
}

fn make_value(i: usize) -> Vec<u8, 16> {
    let len = (i * 7) % 16;
    let mut v = Vec::new();
    v.resize(len, 0).unwrap();

    let val = i.to_le_bytes();
    let n = val.len().min(len);
    v[..n].copy_from_slice(&val[..n]);
    v
}
