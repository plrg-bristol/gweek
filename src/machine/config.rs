//! # Runtime configuration
//!
//! [`Config`] holds the run-time knobs — search [`Strategy`], `optimize`, `timeout_secs`,
//! `occurs_check`, `strict`, `first_only` — the in-memory form of the CLI flags. It is a plain
//! struct passed **by reference**: the evaluator, the machine's step loop, and unification all
//! take `cfg: &Config` explicitly (no thread-local), and the timeout deadline is computed once
//! and threaded down as an absolute `Instant`.

use super::eval::Strategy;

#[derive(Debug, Clone, Copy)]
pub struct Config {
    pub strategy: Strategy,
    pub optimize: bool,
    pub timeout_secs: u64,
    pub occurs_check: bool,
    pub strict: bool,
    pub first_only: bool,
}
