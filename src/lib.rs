pub mod machine;
pub mod parser;
pub mod type_check;

#[cfg(target_arch = "wasm32")]
use wasm_bindgen::prelude::*;

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub fn run_gweek(
    source: &str,
    strategy: &str,
    optimize: bool,
    no_occurs_check: bool,
    eager_vars: bool,
    strict: bool,
    first_only: bool,
    timeout_secs: u64,
    on_line: &js_sys::Function,
) -> String {
    console_error_panic_hook::set_once();

    let strategy = match strategy {
        "dfs" => machine::Strategy::Dfs,
        "iddfs" => machine::Strategy::Iddfs,
        "fair" => machine::Strategy::Fair,
        _ => machine::Strategy::Bfs,
    };

    machine::config::init(machine::Config {
        strategy,
        optimize,
        timeout_secs,
        occurs_check: !no_occurs_check,
        eager_vars,
        strict,
        first_only,
    });

    let ast = match parser::parse(source) {
        Ok(ast) => ast,
        Err(errs) => {
            let mut msgs = Vec::new();
            for err in &errs {
                let span = err.span();
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
                let msg = if expected.is_empty() {
                    format!("Parse error at {}: unexpected {}", span.start, found)
                } else {
                    format!(
                        "Parse error at {}: found {}, expected {}",
                        span.start,
                        found,
                        expected.join(", ")
                    )
                };
                msgs.push(msg);
            }
            return msgs.join("\n");
        }
    };

    if let Err(errs) = type_check::type_check(&ast) {
        let msgs: Vec<String> = errs.iter().map(|e| format!("Type error: {e}")).collect();
        return msgs.join("\n");
    }

    let arena = bumpalo::Bump::new();
    let (main_comp, env) = machine::translate::translate(&arena, ast);
    let (main_comp, env) = if optimize {
        let comp = machine::optimize::optimize(&arena, main_comp);
        let env: Vec<_> = env
            .iter()
            .map(|v| machine::optimize::optimize_val(&arena, v))
            .collect();
        (comp, env)
    } else {
        (main_comp, env)
    };

    machine::eval_streaming(main_comp, &env, |line| {
        let _ = on_line.call1(&JsValue::NULL, &JsValue::from_str(line));
    })
}

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen]
pub fn run_gweek_batch(
    source: &str,
    strategy: &str,
    optimize: bool,
    no_occurs_check: bool,
    eager_vars: bool,
    strict: bool,
    first_only: bool,
    timeout_secs: u64,
) -> String {
    console_error_panic_hook::set_once();

    let strategy = match strategy {
        "dfs" => machine::Strategy::Dfs,
        "iddfs" => machine::Strategy::Iddfs,
        "fair" => machine::Strategy::Fair,
        _ => machine::Strategy::Bfs,
    };

    machine::config::init(machine::Config {
        strategy,
        optimize,
        timeout_secs,
        occurs_check: !no_occurs_check,
        eager_vars,
        strict,
        first_only,
    });

    let ast = match parser::parse(source) {
        Ok(ast) => ast,
        Err(errs) => {
            let mut msgs = Vec::new();
            for err in &errs {
                let span = err.span();
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
                let msg = if expected.is_empty() {
                    format!("Parse error at {}: unexpected {}", span.start, found)
                } else {
                    format!(
                        "Parse error at {}: found {}, expected {}",
                        span.start,
                        found,
                        expected.join(", ")
                    )
                };
                msgs.push(msg);
            }
            return msgs.join("\n");
        }
    };

    if let Err(errs) = type_check::type_check(&ast) {
        let msgs: Vec<String> = errs.iter().map(|e| format!("Type error: {e}")).collect();
        return msgs.join("\n");
    }

    let arena = bumpalo::Bump::new();
    let (main_comp, env) = machine::translate::translate(&arena, ast);
    let (main_comp, env) = if optimize {
        let comp = machine::optimize::optimize(&arena, main_comp);
        let env: Vec<_> = env
            .iter()
            .map(|v| machine::optimize::optimize_val(&arena, v))
            .collect();
        (comp, env)
    } else {
        (main_comp, env)
    };

    machine::eval_collect(main_comp, &env)
}
