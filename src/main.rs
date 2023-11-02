use btor2tools::Btor2Parser;
use clap::Parser;
use std::path::Path;

mod cli;

fn main() {
  let args = cli::CLI::parse();

  let btor2_file = Path::new(args.file.as_str());

  Btor2Parser::new()
    .read_lines(&btor2_file)
    .unwrap() // ignore parser error
    .for_each(|line| {
      // print every parsed line
      println!("{:?}", line.id());
      println!("{:?}", line);
    });
}
