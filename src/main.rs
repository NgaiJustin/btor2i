use btor2tools::Btor2Parser;
use clap::Parser;
use std::path::Path;

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    // /// Name of the person to greet
    // #[arg(short, long)]
    // name: String,

    /// The BTOR2 file to run. stdin is assumed if file is not provided
    #[arg(short, long, action)]
    pub file: String,

    // /// Number of times to greet
    // #[arg(short, long, default_value_t = 1)]
    // count: u8,
}

fn main() {
    let args = Args::parse();

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
