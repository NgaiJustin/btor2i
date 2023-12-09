use btor2i::cli;
use btor2i::error::InterpResult;
use btor2i::interp;
use btor2tools::Btor2Parser;
use clap::Parser;
use std::io;
use std::path::Path;
use std::time::Instant;
use tempfile::NamedTempFile;

fn main() -> InterpResult<()> {
  let start = Instant::now();
  let args = cli::CLI::parse();

  let btor2_file = match args.file {
    None => {
      // If no file is provided, we assume stdin
      let mut tmp = NamedTempFile::new().unwrap();
      io::copy(&mut io::stdin(), &mut tmp).unwrap();
      tmp.path().to_path_buf()
    }
    Some(input_file_path) => Path::new(input_file_path.as_str()).to_path_buf(),
  };

  // Parse and store the btor2 file as Vec<Btor2Line>
  let mut parser = Btor2Parser::new();
  let btor2_lines = parser.read_lines(&btor2_file).unwrap().collect::<Vec<_>>();

  // Flag inputs
  let arg_names = btor2_lines
    .iter()
    .filter(|line| matches!(line.tag(), btor2tools::Btor2Tag::Input))
    .filter_map(|line| {
      line
        .symbol()
        .map(|symbol_cstr| symbol_cstr.to_string_lossy().into_owned())
    })
    .collect::<Vec<_>>();

  // Init environment
  let mut env = interp::Environment::new(btor2_lines.len() + 1);

  // Parse inputs
  match interp::parse_inputs(&mut env, &arg_names, &args.inputs) {
    Ok(()) => {}
    Err(e) => {
      eprintln!("{}", e);
      std::process::exit(1);
    }
  };

  // Main interpreter loop
  interp::interpret(btor2_lines.iter(), &mut env)?;

  // Print result of execution
  println!("{}", env);

  // print to stderr the time it took to run
  let duration = start.elapsed();
  eprintln!("Time elapsed: {} µs", duration.as_micros());

  Ok(())
}
