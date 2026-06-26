//! # The gweek command-line interface
//!
//! The command-line entry point. It parses the flags into a [`Config`](gweek::machine::Config),
//! then runs the pipeline — parse, type-check, elaborate, optionally optimise, evaluate — printing
//! each solution as it is found; parse and type errors are rendered with `ariadne`. See [`gweek`]
//! for the library proper and its WASM entry points, which run the very same pipeline.

use std::fs;
use std::process;

use ariadne::{Color, Label, Report, ReportKind, Source};
use chumsky::prelude::Simple;

use gweek::machine::{self, elaborate::elaborate, Config, Heap, Strategy};
use gweek::parser;
use gweek::type_check;

const USAGE: &str = "\
Usage: gweek [OPTIONS] <source_file>

Runs an existential search over a gweek program and prints each solution.
Pass /dev/stdin as the source file to read a program from stdin (e.g. a heredoc).

Options:
  --bfs              Breadth-first search (default). Complete, but memory-heavy.
  --dfs              Depth-first search. Lean, but incomplete on infinite branches.
  --iddfs            Iterative deepening DFS. Complete, low memory; re-explores.
  --fair             Fair round-robin DFS. Complete, lean, no re-exploration. (recommended)
  --first            Stop after finding the first solution.
  --timeout <N>      Wall-clock timeout in seconds (default: 60).
  -o                 Enable peephole optimizer.
  --strict           Strict bind: evaluate RHS before binding (no suspensions).
  --no-occurs-check  Skip occurs check in unification (unsound but faster).
  --help             Show this help message.

Output:
  > <value>          one line per solution, in source syntax.
  >>> N solutions    search ran to completion: these are ALL solutions.
  >>> timed out ...  inconclusive: stopped at the deadline, more may exist.
Parse/type errors print to stderr and exit 1. A completed run and a timeout
both exit 0, so read the final >>> line to tell them apart.

Example:
  gweek --fair --first --timeout 5 /dev/stdin <<'EOF'
  add :: Nat -> Nat -> Nat
  add n m = case m of Z -> n | S z -> S (add n z).
  exists a :: Nat. exists b :: Nat. add a b =:= 5. (a, b).
  EOF";

fn main() {
    let mut strategy = Strategy::Bfs;
    let mut file_path = None;
    let mut optimize = false;
    let mut timeout_secs: u64 = 60;
    let mut occurs_check = true;
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
            "--strict" => strict = true,
            "--first" => first_only = true,
            "--timeout" => {
                timeout_secs = args
                    .next()
                    .unwrap_or_else(|| {
                        eprintln!("Error: --timeout requires a value\n{USAGE}");
                        process::exit(1);
                    })
                    .parse()
                    .unwrap_or_else(|_| {
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

    let cfg = Config {
        strategy,
        optimize,
        timeout_secs,
        occurs_check,
        strict,
        first_only,
    };

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

    let mut heap = Heap::new();
    let (main_comp, env) = elaborate(&mut heap, ast);
    let (main_comp, env) = if optimize {
        let comp = machine::optimize::optimize(&mut heap, main_comp);
        #[cfg(feature = "opt-stats")]
        let env = machine::optimize::optimize_env_with_stats(&mut heap, &env, &|h, v| {
            machine::optimize::optimize_val(h, v)
        });
        #[cfg(not(feature = "opt-stats"))]
        let env: Vec<_> = env
            .iter()
            .map(|v| machine::optimize::optimize_val(&mut heap, *v))
            .collect();
        (comp, env)
    } else {
        (main_comp, env)
    };
    machine::eval(&cfg, &mut heap, main_comp, &env);
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
    use gweek::machine::{self, elaborate::elaborate, run, Config, Heap, Strategy};
    use gweek::{parser, type_check};
    use std::fs;

    /// Build a deterministic config for tests with the given strategy.
    fn test_config(strategy: Strategy) -> Config {
        Config {
            strategy,
            optimize: false,
            timeout_secs: 60,
            occurs_check: true,
            strict: false,
            first_only: false,
        }
    }

    // Full pipeline (parse -> type-check -> elaborate -> evaluate) returning the
    // collected output, for asserting the value a program produces.
    fn collect_source(src: &str) -> String {
        let mut heap = Heap::new();
        let ast = parser::parse(src).expect("should parse");
        type_check::type_check(&ast).expect("should type-check");
        let (comp, env) = elaborate(&mut heap, ast);
        machine::eval_collect(&test_config(Strategy::Bfs), &mut heap, comp, &env)
    }

    // B2: `if`/`then`/`else` and `==` on Nat elaborate and evaluate correctly.
    #[test]
    fn if_then_else_and_nat_eq() {
        assert!(collect_source("if (2 == 2) then 7 else 9.\n").contains("> 7"));
        assert!(collect_source("if (1 == 2) then 7 else 9.\n").contains("> 9"));
    }

    // B10: a pair function argument is destructured and projected.
    #[test]
    fn pair_argument_projection() {
        assert!(
            collect_source("f :: Nat * Nat -> Nat\nf (x,y) = y.\n\nf (3,4).\n").contains("> 4")
        );
        assert!(
            collect_source("g :: Nat * Nat -> Nat\ng (x,y) = x.\n\ng (3,4).\n").contains("> 3")
        );
    }

    // B3: mutually recursive top-level functions elaborate and evaluate.
    #[test]
    fn mutual_recursion() {
        let prog = |n: u32| {
            format!(
                "isEven :: Nat -> Bool\nisEven n = case n of Z -> true | S m -> isOdd m.\n\n\
             isOdd :: Nat -> Bool\nisOdd n = case n of Z -> false | S m -> isEven m.\n\n\
             isEven {n}.\n"
            )
        };
        assert!(collect_source(&prog(4)).contains("> true"));
        assert!(collect_source(&prog(3)).contains("> false"));
    }

    fn run_example(path: &str, strategy: Strategy) -> usize {
        run_example_inner(path, strategy, false)
    }

    fn run_example_opt(path: &str, strategy: Strategy) -> usize {
        run_example_inner(path, strategy, true)
    }

    fn run_example_inner(path: &str, strategy: Strategy, opt: bool) -> usize {
        let mut heap = Heap::new();
        let src = fs::read_to_string(path).unwrap();
        let ast = parser::parse(&src).unwrap();
        let (comp, env) = elaborate(&mut heap, ast);
        let cfg = test_config(strategy);
        if opt {
            let comp = machine::optimize::optimize(&mut heap, comp);
            let env: Vec<_> = env
                .iter()
                .map(|v| machine::optimize::optimize_val(&mut heap, *v))
                .collect();
            run(&cfg, &mut heap, comp, &env, false)
        } else {
            run(&cfg, &mut heap, comp, &env, false)
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
        assert_eq!(
            run_example_opt("examples/find_list.gwk", Strategy::Bfs),
            462
        );
    }

    #[test]
    fn nqueens_bfs_opt() {
        assert_eq!(run_example_opt("examples/nqueens.gwk", Strategy::Bfs), 92);
    }
}
