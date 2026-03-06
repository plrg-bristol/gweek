use std::fs;
use std::process;

use crate::machine::{translate::translate, Strategy};

mod machine;
mod parser;

const USAGE: &str = "\
Usage: gweek [OPTIONS] <source_file>

Options:
  --bfs     Breadth-first search (default)
  --dfs     Depth-first search (fast, but incomplete on infinite branches)
  --iddfs   Iterative deepening DFS (complete, re-explores)
  --fair    Fair round-robin DFS (complete, no re-exploration)
  --help    Show this help message";

fn main() {
    let mut strategy = Strategy::Bfs;
    let mut file_path = None;

    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--bfs" => strategy = Strategy::Bfs,
            "--dfs" => strategy = Strategy::Dfs,
            "--iddfs" => strategy = Strategy::Iddfs,
            "--fair" => strategy = Strategy::Fair,
            "--help" | "-h" => {
                println!("{USAGE}");
                return;
            }
            s if s.starts_with('-') => {
                eprintln!("Unknown option: {s}\n{USAGE}");
                process::exit(1);
            }
            _ => {
                if file_path.is_some() {
                    eprintln!("Error: multiple source files provided.\n{USAGE}");
                    process::exit(1);
                }
                file_path = Some(arg);
            }
        }
    }

    let file_path = file_path.unwrap_or_else(|| {
        eprintln!("Error: no source file provided.\n{USAGE}");
        process::exit(1);
    });

    let src = fs::read_to_string(&file_path).unwrap_or_else(|e| {
        eprintln!("Error: could not read '{file_path}': {e}");
        process::exit(1);
    });

    let ast = parser::parse(&src).unwrap_or_else(|errs| {
        for err in errs {
            eprintln!("Parse error: {err}");
        }
        process::exit(1);
    });

    let (main_comp, env) = translate(ast);
    machine::eval(main_comp, env.into(), strategy);
}
