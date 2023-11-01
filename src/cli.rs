use clap::Parser;

#[derive(Parser)]
#[command(about, version, author)] // keeps the cli synced with Cargo.toml
#[command(allow_hyphen_values(true))]
pub struct CLI {
  /// The BTOR2 file to run. stdin is assumed if file is not provided
  #[arg(short, long, action)]
  pub file: String,

  /// Arguments for the main function
  #[arg(action)]
  pub args: Vec<String>,
}
