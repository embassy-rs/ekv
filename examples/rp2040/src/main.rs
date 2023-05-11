#![no_std]
#![no_main]
#![feature(type_alias_impl_trait)]
#![feature(async_fn_in_trait)]
#![allow(incomplete_features)]

use defmt::*;
use ekv::flash::{self, PageID};
use ekv::{config, Database};
use embassy_executor::Spawner;
use embassy_rp::flash::Flash;
use embassy_rp::peripherals::FLASH;
use embassy_sync::blocking_mutex::raw::NoopRawMutex;
use embassy_time::Duration;
use embedded_storage::nor_flash::{NorFlash, ReadNorFlash};
use {defmt_rtt as _, panic_probe as _};

const FLASH_SIZE: usize = 2 * 1024 * 1024;
extern "C" {
    // Flash storage used for configuration
    static __config_start: u32;
}

// Workaround for alignment requirements.
#[repr(C, align(4))]
struct AlignedBuf<const N: usize>([u8; N]);

struct DbFlash<T: NorFlash + ReadNorFlash> {
    start: usize,
    flash: T,
}

impl<T: NorFlash + ReadNorFlash> flash::Flash for DbFlash<T> {
    type Error = T::Error;

    fn page_count(&self) -> usize {
        config::MAX_PAGE_COUNT
    }

    async fn erase(&mut self, page_id: PageID) -> Result<(), <DbFlash<T> as flash::Flash>::Error> {
        self.flash.erase(
            (self.start + page_id.index() * config::PAGE_SIZE) as u32,
            (self.start + page_id.index() * config::PAGE_SIZE + config::PAGE_SIZE) as u32,
        )
    }

    async fn read(
        &mut self,
        page_id: PageID,
        offset: usize,
        data: &mut [u8],
    ) -> Result<(), <DbFlash<T> as flash::Flash>::Error> {
        let address = self.start + page_id.index() * config::PAGE_SIZE + offset;
        let mut buf = AlignedBuf([0; config::PAGE_SIZE]);
        self.flash.read(address as u32, &mut buf.0[..data.len()])?;
        data.copy_from_slice(&buf.0[..data.len()]);
        Ok(())
    }

    async fn write(
        &mut self,
        page_id: PageID,
        offset: usize,
        data: &[u8],
    ) -> Result<(), <DbFlash<T> as flash::Flash>::Error> {
        let address = self.start + page_id.index() * config::PAGE_SIZE + offset;
        let mut buf = AlignedBuf([0; config::PAGE_SIZE]);
        buf.0[..data.len()].copy_from_slice(data);
        self.flash.write(address as u32, &buf.0[..data.len()])
    }
}

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_rp::init(Default::default());

    let flash: DbFlash<Flash<FLASH, FLASH_SIZE>> = DbFlash {
        flash: Flash::new(p.FLASH),
        start: unsafe { &__config_start as *const u32 as usize },
    };
    let db = Database::<_, NoopRawMutex>::new(flash, ekv::Config::default());

    if db.mount().await.is_err() {
        info!("Formatting...");
        db.format().await.unwrap();
    }

    let mut wtx = db.write_transaction().await;
    wtx.write(b"HELLO", b"WORLD").await.unwrap();
    wtx.commit().await.unwrap();

    let mut rtx = db.read_transaction().await;
    let mut buf = [0u8; 32];
    let hello = rtx.read(b"HELLO", &mut buf).await.map(|n| &buf[..n]).ok();
    if let Some(s) = hello {
        info!("HELLO: {:a}", s);
    }

    info!("Bye!");
    embassy_time::Timer::after(Duration::from_secs(1)).await;
    cortex_m::asm::bkpt();
}
