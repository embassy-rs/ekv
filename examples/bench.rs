use ekv::flash::MemFlash;
use ekv::{Config, Database, FormatConfig};
use plotters::prelude::*;
use rand::Rng;

struct Params {
    key_count: usize,
    key_len: usize,
    val_len: usize,
}

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

fn print_counters(f: &mut MemFlash, baseline: usize) {
    println!(
        "    read:  {}, {} bytes ({:.1}%)",
        f.read_count,
        f.read_bytes,
        100.0 * f.read_bytes as f64 / baseline as f64
    );
    println!(
        "    write: {}, {} bytes ({:.1}%)",
        f.write_count,
        f.write_bytes,
        100.0 * f.write_bytes as f64 / baseline as f64
    );
    println!(
        "    erase: {}, {} bytes ({:.1}%)",
        f.erase_count,
        f.erase_bytes,
        100.0 * f.erase_bytes as f64 / baseline as f64
    );
}

async fn run(p: Params) -> f64 {
    // Generate keys
    let mut keys = Vec::new();
    keys.push(b"foo".to_vec());
    while keys.len() < p.key_count {
        let key = rand_data(p.key_len);
        if !keys.contains(&key) {
            keys.push(key)
        }
    }

    let mut f = MemFlash::new();
    let mut config = Config::default();
    config.format = FormatConfig::Format;
    let db = Database::new(&mut f, config).await.unwrap();

    for key in &keys {
        let mut wtx = db.write_transaction().await;
        wtx.write(key, &rand_data(p.val_len)).await.unwrap();
        wtx.commit().await.unwrap();
    }

    db.lock_flash().await.reset_counters();

    let mut buf = [0; 1024];

    for key in &keys {
        let mut rtx = db.read_transaction().await;
        rtx.read(key, &mut buf).await.unwrap();
    }

    let baseline = p.key_count * (p.key_len + p.val_len);
    let read_bytes = db.lock_flash().await.read_bytes;
    read_bytes as f64 / baseline as f64
}

const OUT_FILE_NAME: &str = "area-chart.png";

#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    env_logger::init();

    let max = 500;

    let mut data = Vec::new();
    for count in (10..max).step_by(1) {
        let amplification = run(Params {
            key_count: count,
            key_len: 4,
            val_len: 10,
        })
        .await;
        data.push((count as f64, amplification));
    }

    let max_y = data
        .iter()
        .map(|(_, y)| *y)
        .max_by(|a, b| a.partial_cmp(b).unwrap())
        .unwrap();

    let root = BitMapBackend::new(OUT_FILE_NAME, (1920, 768)).into_drawing_area();

    root.fill(&WHITE)?;

    let mut chart = ChartBuilder::on(&root)
        .set_label_area_size(LabelAreaPosition::Left, 60)
        .set_label_area_size(LabelAreaPosition::Bottom, 60)
        .build_cartesian_2d(0.0..(max as f64), 0.0..max_y)?;

    chart.configure_mesh().disable_x_mesh().disable_y_mesh().draw()?;

    chart.draw_series(AreaSeries::new(data, 0.0, RED.mix(0.2)).border_style(RED))?;

    root.present()?;
    Ok(())
}
