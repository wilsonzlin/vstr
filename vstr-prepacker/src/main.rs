use clap::Parser;
use serde::Serialize;
use std::fs::File;
use std::io::stdin;
use std::io::BufRead;
use std::io::BufReader;
use std::io::Write;
use std::path::PathBuf;
use tracing::info;
use vstr::Dictionary;
use vstr::DictionaryBuilder;

#[derive(Debug, Parser)]
#[command(version)]
struct Cli {
  /// Split stdin bytes by this delimiter to get entries.
  #[arg(short, long)]
  delimiter: String,

  /// File to write prepacked dictionary to.
  #[arg(short, long)]
  out: PathBuf,
}

fn main() {
  tracing_subscriber::fmt::init();

  let cli = Cli::parse();
  assert_eq!(cli.delimiter.len(), 1);
  let delim = cli.delimiter.as_bytes()[0] as u8;

  let mut uncompressed_entries = Vec::new();
  let mut stdin = BufReader::new(stdin());
  let mut builder = DictionaryBuilder::new();
  loop {
    let mut buf = Vec::new();
    let offset = buf.len();
    let n = stdin.read_until(delim, &mut buf).unwrap();
    assert_eq!(offset + n, buf.len());
    if n == 0 {
      break;
    };
    // If there's no trailing `delim`, then `buf` won't end with it for the last entry.
    let uncompressed = buf
      .strip_suffix(&[delim])
      .unwrap_or(&buf[offset..offset + n]);
    builder.add_sample(uncompressed);
    uncompressed_entries.push(uncompressed.to_vec());
  }
  info!(
    samples = uncompressed_entries.len(),
    "finalising dictionary"
  );
  let dict_data = builder.finalise();
  let mut dict_data_raw = Vec::new();
  dict_data
    .serialize(&mut rmp_serde::Serializer::new(&mut dict_data_raw))
    .unwrap();
  info!(size = dict_data_raw.len(), "writing dictionary");
  File::create(cli.out)
    .unwrap()
    .write_all(&dict_data_raw)
    .unwrap();
  let dict = Dictionary::new(dict_data);
  info!("evaluating performance on samples");
  let mut total_uncompressed_len = 0;
  let mut total_compressed_len = 0;
  for uncompressed in uncompressed_entries.iter() {
    total_uncompressed_len += uncompressed.len();
    total_compressed_len += dict.compress(uncompressed).len();
  }
  info!(
    total_uncompressed_len,
    total_compressed_len,
    compression_ratio = total_uncompressed_len as f64 / total_compressed_len as f64,
    "compression performance evaluated",
  );
}
