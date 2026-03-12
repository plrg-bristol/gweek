use std::fs;
use std::process;

use ariadne::{Color, Label, Report, ReportKind, Source};
use bumpalo::Bump;
use chumsky::prelude::Simple;

use gweek::machine::{self, translate::translate, Config, Strategy};
use gweek::parser;
use gweek::type_check;

const USAGE: &str = "\
Usage: gweek [OPTIONS] <source_file>

Options:
  --bfs              Breadth-first search (default)
  --dfs              Depth-first search (fast, but incomplete on infinite branches)
  --iddfs            Iterative deepening DFS (complete, re-explores)
  --fair             Fair round-robin DFS (complete, no re-exploration)
  -o                 Enable peephole optimizer
  --timeout <N>      Timeout in seconds (default: 60)
  --no-occurs-check  Skip occurs check in unification (unsound but faster)
  --eager-vars       Eagerly resolve variable indirections in env
  --strict           Strict bind: evaluate RHS before binding (no suspensions)
  --first            Stop after finding the first solution
  --help             Show this help message";

fn main() {
    let mut strategy = Strategy::Bfs;
    let mut file_path = None;
    let mut optimize = false;
    let mut timeout_secs: u64 = 60;
    let mut occurs_check = true;
    let mut eager_vars = false;
    let mut strict = false;
    let mut first_only = false;

    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--bfs" => strategy = Strategy::Bfs,
            "--dfs" => strategy = Strategy::Dfs,
            "--iddfs" => strategy = Strategy::Iddfs,
            "--fair" => strategy = Strategy::Fair,
            "-o" => optimize = true,
            "--no-occurs-check" => occurs_check = false,
            "--eager-vars" => eager_vars = true,
            "--strict" => strict = true,
            "--first" => first_only = true,
            "--timeout" => {
                timeout_secs = args.next().unwrap_or_else(|| {
                    eprintln!("Error: --timeout requires a value\n{USAGE}");
                    process::exit(1);
                }).parse().unwrap_or_else(|_| {
                    eprintln!("Error: --timeout value must be a positive integer\n{USAGE}");
                    process::exit(1);
                });
            }
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

    machine::config::init(Config {
        strategy,
        optimize,
        timeout_secs,
        occurs_check,
        eager_vars,
        strict,
        first_only,
    });

    let arena = Bump::new();
    let (main_comp, env) = translate(&arena, ast);
    let (main_comp, env) = if optimize {
        let comp = machine::optimize::optimize(&arena, main_comp);
        #[cfg(feature = "opt-stats")]
        let env = machine::optimize::optimize_env_with_stats(&arena, &env, &|a, v| machine::optimize::optimize_val(a, v));
        #[cfg(not(feature = "opt-stats"))]
        let env: Vec<_> = env.iter().map(|v| machine::optimize::optimize_val(&arena, v)).collect();
        (comp, env)
    } else {
        (main_comp, env)
    };
    machine::eval(main_comp, &env);
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
    use bumpalo::Bump;
    use gweek::machine::{self, translate::translate, run, Strategy};
    use gweek::parser;
    use std::fs;

    fn run_example(path: &str, strategy: Strategy) -> usize {
        run_example_inner(path, strategy, false)
    }

    fn run_example_opt(path: &str, strategy: Strategy) -> usize {
        run_example_inner(path, strategy, true)
    }

    fn run_example_inner(path: &str, strategy: Strategy, opt: bool) -> usize {
        let arena = Bump::new();
        let src = fs::read_to_string(path).unwrap();
        let ast = parser::parse(&src).unwrap();
        let (comp, env) = translate(&arena, ast);
        if opt {
            let comp = machine::optimize::optimize(&arena, comp);
            let env: Vec<_> = env.iter().map(|v| machine::optimize::optimize_val(&arena, v)).collect();
            run(comp, &env, strategy, false)
        } else {
            run(comp, &env, strategy, false)
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
