use btor2i::cli;
use btor2i::error::InterpResult;
use btor2i::interp;
use btor2tools::Btor2Parser;
use clap::Parser;
use std::fs::read_to_string;
use std::io;
use std::path::Path;
use std::time::Instant;
use tempfile::NamedTempFile;

fn main() -> InterpResult<()> {
  let start = Instant::now();
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

  // get number of lines in btor2_file
  let line_nums = read_to_string(&btor2_file).unwrap().lines().count();

  // Flag inputs
  let arg_names = Btor2Parser::new()
    .read_lines(&btor2_file)
    .unwrap()
    .filter(|line| matches!(line.tag(), btor2tools::Btor2Tag::Input))
    .filter_map(|line| match line.symbol() {
      Some(symbol_cstr) => Some(symbol_cstr.to_string_lossy().into_owned()),
      None => None, // skip unnamed inputs (default to undef)
    })
    .collect::<Vec<_>>();

  // Init environment
  let mut env = interp::Environment::new(line_nums + 1);

  // Parse inputs
  env = match interp::parse_inputs(env, &arg_names, &args.inputs) {
    Ok(env) => env,
    Err(e) => {
      eprintln!("{}", e);
      std::process::exit(1);
    }
  };

  // Main interpreter loop
  let mut parser = Btor2Parser::new();
  let prog_iterator = parser.read_lines(&btor2_file).unwrap();

  interp::interpret(prog_iterator, &mut env)?;

  // Print result of execution
  println!("{}", env);

  // print to stderr the time it took to run
  let duration = start.elapsed();
  eprintln!("Time elapsed: {} us", duration.as_micros());

  Ok(())
}
