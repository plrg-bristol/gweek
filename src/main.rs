use std::env;
use std::process;
use std::fs::File;
use std::io::{self, Read};

use crate::machine::translate::translate;

mod parser;
mod machine;

fn main() {
    let args: Vec<String> = env::args().collect();

     if args.len() != 2 {
        eprintln!("Error: Expected one argument, but got {}.", args.len() - 1);
        eprintln!("Usage: {} source_file", args[0]);
        process::exit(1);
    }

    let file_name = &args[1];

    let mut file = match File::open(file_name) {
        Ok(file) => file,
        Err(error) => {
            eprintln!("Error: Could not open file '{}': {}", file_name, error);
            process::exit(1);
        }
    };

    let mut src = String::new();

    // Try to read the file contents
    match file.read_to_string(&mut src) {
        Ok(_) => { interpret(&mut src); }
        Err(error) => {
            eprintln!("Error: Could not read file '{}': {}", file_name, error);
            process::exit(1);
        }
    };
}

fn interpret(src: &mut String) {

    let ast = parser::parse(src).unwrap_or_else(|errs| {
        for err in errs {
            eprintln!("Parse error: {}", err);
        }
        process::exit(1);
    });
    let (main, env) = translate(ast);
    machine::eval(main, env.into());
}
