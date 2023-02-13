#![no_std]
#![no_main]
#![feature(type_alias_impl_trait)]
#![feature(async_fn_in_trait)]
#![feature(impl_trait_projections)]
#![allow(incomplete_features)]

use core::convert::Infallible;

use defmt::{assert_eq, info, unwrap};
use ekv::flash::PageID;
use ekv::{config, Config, Database, FormatConfig};
use embassy_executor::Spawner;
use embassy_nrf::{interrupt, pac, peripherals, qspi};
use embassy_sync::blocking_mutex::raw::NoopRawMutex;
use embassy_time::Instant;
use heapless::Vec;
use {defmt_rtt as _, panic_probe as _};

const FLASH_SIZE: usize = config::PAGE_SIZE * config::MAX_PAGE_COUNT;

struct Flash<'a> {
    qspi: qspi::Qspi<'a, peripherals::QSPI, FLASH_SIZE>,
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
        self.qspi.erase(page_id.index() * config::PAGE_SIZE).await.unwrap();
        Ok(())
    }

    async fn read(&mut self, page_id: PageID, offset: usize, data: &mut [u8]) -> Result<(), Self::Error> {
        let address = page_id.index() * config::PAGE_SIZE + offset;
        unsafe {
            self.qspi.read(address, &mut BUF.0[..data.len()]).await.unwrap();
            data.copy_from_slice(&BUF.0[..data.len()])
        }
        Ok(())
    }

    async fn write(&mut self, page_id: PageID, offset: usize, data: &[u8]) -> Result<(), Self::Error> {
        let address = page_id.index() * config::PAGE_SIZE + offset;
        unsafe {
            BUF.0[..data.len()].copy_from_slice(data);
            self.qspi.write(address, &BUF.0[..data.len()]).await.unwrap();
        }
        Ok(())
    }
}

#[embassy_executor::main]
async fn main(_spawner: Spawner) -> ! {
    unsafe {
        let nvmc = &*pac::NVMC::ptr();
        let power = &*pac::POWER::ptr();

        // Enable DC-DC
        power.dcdcen.write(|w| w.dcdcen().enabled());

        // Enable flash cache
        nvmc.icachecnf.write(|w| w.cacheen().enabled());
    }

    let p = embassy_nrf::init(Default::default());

    // Config for the MX25R64 present in the nRF52840 DK
    let mut config = qspi::Config::default();
    config.read_opcode = qspi::ReadOpcode::READ4IO;
    config.write_opcode = qspi::WriteOpcode::PP4IO;
    config.write_page_size = qspi::WritePageSize::_256BYTES;
    config.frequency = qspi::Frequency::M32;

    let irq = interrupt::take!(QSPI);
    let mut q: qspi::Qspi<_, FLASH_SIZE> = qspi::Qspi::new(
        p.QSPI, irq, p.P0_19, p.P0_17, p.P0_20, p.P0_21, p.P0_22, p.P0_23, config,
    );

    let mut id = [1; 3];
    unwrap!(q.custom_instruction(0x9F, &[], &mut id).await);
    info!("id: {}", id);

    // Read status register
    let mut status = [4; 1];
    unwrap!(q.custom_instruction(0x05, &[], &mut status).await);

    info!("status: {:?}", status[0]);

    if status[0] & 0x40 == 0 {
        status[0] |= 0x40;

        unwrap!(q.custom_instruction(0x01, &status, &mut []).await);

        info!("enabled quad in status");
    }

    let mut f = Flash { qspi: q };

    info!("Mounting...");
    let start = Instant::now();
    let mut config = Config::default();
    config.format = FormatConfig::Format;
    let db = unwrap!(Database::<_, NoopRawMutex>::new(&mut f, config).await);
    let ms = Instant::now().duration_since(start).as_millis();
    info!("Done in {} ms!", ms);

    const KEY_COUNT: usize = 1000;
    const TX_SIZE: usize = 100;

    info!("Writing {} keys...", KEY_COUNT);
    let start = Instant::now();
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
    let ms = Instant::now().duration_since(start).as_millis();
    info!("Done in {} ms! {}ms/key", ms, ms / KEY_COUNT as u64);

    info!("Reading {} keys...", KEY_COUNT);
    let mut buf = [0u8; 32];
    let start = Instant::now();
    for i in 0..KEY_COUNT {
        let key = make_key(i);
        let val = make_value(i);

        let mut rtx = db.read_transaction().await;
        let n = rtx.read(&key, &mut buf).await.unwrap();
        assert_eq!(&buf[..n], &val[..]);
    }
    let ms = Instant::now().duration_since(start).as_millis();
    info!("Done in {} ms! {}ms/key", ms, ms / KEY_COUNT as u64);

    info!("ALL DONE");

    loop {}
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
