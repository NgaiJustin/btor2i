use btor2i::cli;
use btor2tools::Btor2Parser;
use clap::Parser;
use std::io;
use std::path::Path;
use tempfile::NamedTempFile;

fn main() {
  let args = cli::CLI::parse();

  let btor2_file = match args.file.clone() {
    None => {
      // If no file is provided, we assume stdin
      let mut tmp = NamedTempFile::new().unwrap();
      io::copy(&mut io::stdin(), &mut tmp).unwrap();
      tmp.path().to_path_buf()
    }
    Some(input_file_path) => Path::new(input_file_path.as_str()).to_path_buf(),
  };

  Btor2Parser::new()
    .read_lines(&btor2_file)
    .unwrap() // ignore parser error
    .for_each(|line| {
      // print every parsed line
      println!("{:?}", line.id());
      println!("{:?}", line);
    });
}
