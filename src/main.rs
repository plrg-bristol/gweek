use std::env;
use std::process;
use std::fs::File;
use std::io::{self, Read};

use crate::machine::translate::translate;
use crate::machine::Strategy;

mod parser;
mod machine;

fn main() {
    let args: Vec<String> = env::args().collect();

    let mut strategy = Strategy::Bfs;
    let mut file_name = None;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--bfs" => strategy = Strategy::Bfs,
            "--dfs" => strategy = Strategy::Dfs,
            "--iddfs" => strategy = Strategy::Iddfs,
            other if other.starts_with("--") => {
                eprintln!("Error: Unknown flag '{}'", other);
                eprintln!("Usage: {} [--bfs|--dfs|--iddfs] source_file", args[0]);
                process::exit(1);
            }
            _ => {
                if file_name.is_some() {
                    eprintln!("Error: Multiple source files provided.");
                    eprintln!("Usage: {} [--bfs|--dfs|--iddfs] source_file", args[0]);
                    process::exit(1);
                }
                file_name = Some(&args[i]);
            }
        }
        i += 1;
    }

    let file_name = match file_name {
        Some(f) => f,
        None => {
            eprintln!("Error: No source file provided.");
            eprintln!("Usage: {} [--bfs|--dfs|--iddfs] source_file", args[0]);
            process::exit(1);
        }
    };

    let mut file = match File::open(file_name) {
        Ok(file) => file,
        Err(error) => {
            eprintln!("Error: Could not open file '{}': {}", file_name, error);
            process::exit(1);
        }
    };

    let mut src = String::new();

    match file.read_to_string(&mut src) {
        Ok(_) => { interpret(&mut src, strategy); }
        Err(error) => {
            eprintln!("Error: Could not read file '{}': {}", file_name, error);
            process::exit(1);
        }
    };
}

fn interpret(src: &mut String, strategy: Strategy) {

    let ast = parser::parse(src).unwrap_or_else(|errs| {
        for err in errs {
            eprintln!("Parse error: {}", err);
        }
        process::exit(1);
    });
    let (main, env) = translate(ast);
    machine::eval(main, env.into(), strategy);
}
