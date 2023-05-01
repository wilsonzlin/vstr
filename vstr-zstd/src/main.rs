use clap::Parser;
use std::fs::File;
use std::io::stdin;
use std::io::Read;
use std::io::Write;
use std::path::PathBuf;
use tracing::info;
use zstd::dict::from_continuous;
use zstd::dict::EncoderDictionary;
use zstd::Encoder;

#[derive(Debug, Parser)]
#[command(version)]
struct Cli {
  /// Split stdin bytes by this delimiter to get entries.
  #[arg(short, long)]
  delimiter: String,

  /// File to write prepacked dictionary to.
  #[arg(short, long)]
  out: PathBuf,

  /// Zstd compression level.
  #[arg(short, long, default_value_t = 3)]
  level: i32,
}

fn main() {
  tracing_subscriber::fmt::init();

  let cli = Cli::parse();
  assert_eq!(cli.delimiter.len(), 1);
  let delim = cli.delimiter.as_bytes()[0] as u8;

  let mut input_raw = Vec::new();
  stdin().read_to_end(&mut input_raw).unwrap();

  info!(raw_length = input_raw.len(), "reading samples");
  let mut sample_data_combined = Vec::new();
  let mut sample_sizes = Vec::new();
  for uncompressed in input_raw.split(|c| *c == delim) {
    sample_data_combined.extend_from_slice(uncompressed);
    sample_sizes.push(uncompressed.len());
  }

  info!(samples = sample_sizes.len(), "building zstd dictionary");
  let zstd_dict_data =
    from_continuous(&sample_data_combined, &sample_sizes, 1024 * 1024 * 1024).unwrap();
  let zstd_dict = EncoderDictionary::copy(&zstd_dict_data, cli.level);

  info!(size = zstd_dict_data.len(), "writing dictionary");
  File::create(cli.out)
    .unwrap()
    .write_all(&zstd_dict_data)
    .unwrap();

  info!("evaluating performance on samples");
  let mut total_uncompressed_len = 0;
  let mut total_zstd_compressed_len = 0;
  for uncompressed in input_raw.split(|c| *c == delim) {
    total_uncompressed_len += uncompressed.len();
    let mut zstd_compressed = Vec::new();
    let mut zstd_encoder =
      Encoder::with_prepared_dictionary(&mut zstd_compressed, &zstd_dict).unwrap();
    zstd_encoder.write_all(uncompressed).unwrap();
    zstd_encoder.finish().unwrap();
    total_zstd_compressed_len += zstd_compressed.len();
  }
  info!(
    total_uncompressed_len,
    total_zstd_compressed_len,
    zstd_compression_ratio = total_uncompressed_len as f64 / total_zstd_compressed_len as f64,
    "compression performance evaluated",
  );
}
