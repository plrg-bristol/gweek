use std::fs;
use std::process;

use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::prelude::Simple;

use crate::machine::{translate::translate, Strategy};

mod machine;
mod parser;
mod type_check;

const USAGE: &str = "\
Usage: gweek [OPTIONS] <source_file>

Options:
  --bfs     Breadth-first search (default)
  --dfs     Depth-first search (fast, but incomplete on infinite branches)
  --iddfs   Iterative deepening DFS (complete, re-explores)
  --fair    Fair round-robin DFS (complete, no re-exploration)
  -o        Enable peephole optimizer
  --help    Show this help message";

fn main() {
    let mut strategy = Strategy::Bfs;
    let mut file_path = None;
    let mut opt = false;

    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--bfs" => strategy = Strategy::Bfs,
            "--dfs" => strategy = Strategy::Dfs,
            "--iddfs" => strategy = Strategy::Iddfs,
            "--fair" => strategy = Strategy::Fair,
            "-o" => opt = true,
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
        report_errors(&file_path, &src, errs);
        process::exit(1);
    });

    if let Err(errs) = type_check::type_check(&ast) {
        for e in errs {
            eprintln!("Type error: {e}");
        }
        process::exit(1);
    }

    let (main_comp, env) = translate(ast);
    let (main_comp, env) = if opt {
        let comp = machine::optimize::optimize(main_comp);
        let env = machine::map_env_vals(&env, &machine::optimize::optimize_val);
        (comp, env)
    } else {
        (main_comp, env)
    };
    machine::eval(main_comp, env, strategy);
}

fn report_errors(filename: &str, src: &str, errs: Vec<Simple<char>>) {
    let source = Source::from(src);
    for err in errs {
        let span = err.span();
        let msg = match err.reason() {
            chumsky::error::SimpleReason::Unexpected => {
                let found = err
                    .found()
                    .map(|c| format!("'{c}'"))
                    .unwrap_or_else(|| "end of input".to_string());
                let expected: Vec<_> = err
                    .expected()
                    .map(|e| match e {
                        Some(c) => format!("'{c}'"),
                        None => "end of input".to_string(),
                    })
                    .collect();
                if expected.is_empty() {
                    format!("unexpected {found}")
                } else {
                    format!("found {found}, expected {}", expected.join(", "))
                }
            }
            chumsky::error::SimpleReason::Unclosed { span: _, delimiter } => {
                format!("unclosed delimiter '{delimiter}'")
            }
            chumsky::error::SimpleReason::Custom(msg) => msg.clone(),
        };

        Report::build(ReportKind::Error, filename, span.start)
            .with_message(&msg)
            .with_label(
                Label::new((filename, span))
                    .with_message(&msg)
                    .with_color(Color::Red),
            )
            .finish()
            .eprint((filename, source.clone()))
            .unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::{map_env_vals, run, Strategy};

    fn run_example(path: &str, strategy: Strategy) -> usize {
        run_example_inner(path, strategy, false)
    }

    fn run_example_opt(path: &str, strategy: Strategy) -> usize {
        run_example_inner(path, strategy, true)
    }

    fn run_example_inner(path: &str, strategy: Strategy, opt: bool) -> usize {
        let src = fs::read_to_string(path).unwrap();
        let ast = parser::parse(&src).unwrap();
        let (comp, env) = translate(ast);
        if opt {
            let comp = machine::optimize::optimize(comp);
            let env = map_env_vals(&env, &machine::optimize::optimize_val);
            run(comp, env, strategy, false)
        } else {
            run(comp, env, strategy, false)
        }
    }

    #[test]
    fn perm_bfs() {
        assert_eq!(run_example("examples/perm.gwk", Strategy::Bfs), 720);
    }

    #[test]
    fn perm_fair() {
        assert_eq!(run_example("examples/perm.gwk", Strategy::Fair), 720);
    }

    #[test]
    fn find_list_bfs() {
        assert_eq!(run_example("examples/find_list.gwk", Strategy::Bfs), 462);
    }

    #[test]
    fn find_list_fair() {
        assert_eq!(run_example("examples/find_list.gwk", Strategy::Fair), 462);
    }

    #[test]
    fn nqueens_bfs() {
        assert_eq!(run_example("examples/nqueens.gwk", Strategy::Bfs), 92);
    }

    #[test]
    fn nqueens_fair() {
        assert_eq!(run_example("examples/nqueens.gwk", Strategy::Fair), 92);
    }

    // Optimized variants — same results expected
    #[test]
    fn perm_bfs_opt() {
        assert_eq!(run_example_opt("examples/perm.gwk", Strategy::Bfs), 720);
    }

    #[test]
    fn find_list_bfs_opt() {
        assert_eq!(run_example_opt("examples/find_list.gwk", Strategy::Bfs), 462);
    }

    #[test]
    fn nqueens_bfs_opt() {
        assert_eq!(run_example_opt("examples/nqueens.gwk", Strategy::Bfs), 92);
    }
}
