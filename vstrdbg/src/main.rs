use clap::Parser;
use std::fs::File;
use std::io::Read;
use std::path::PathBuf;
use vstr::DictionaryData;

#[derive(Debug, Parser)]
#[command(version)]
struct Cli {
  /// Path to the dictionary file.
  dict_file: PathBuf,
}

fn main() {
  tracing_subscriber::fmt::init();

  let cli = Cli::parse();

  let mut raw = Vec::new();
  File::open(cli.dict_file)
    .unwrap()
    .read_to_end(&mut raw)
    .unwrap();
  let dict_data: DictionaryData = rmp_serde::from_slice(&raw).unwrap();

  println!("{}", dict_data.generate_inspection_message());
}
