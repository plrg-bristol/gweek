//! # Runtime configuration
//!
//! [`Config`] collects the run-time knobs — the search [`Strategy`], `optimize`, `timeout_secs`,
//! `occurs_check`, `first_only` — viz. the in-memory form of the CLI flags. It is a
//! plain record, passed by reference everywhere rather than stashed in a thread-local, so that the
//! one source of truth travels down the pipeline explicitly.

use super::eval::Strategy;

#[derive(Debug, Clone, Copy)]
pub struct Config {
    pub strategy: Strategy,
    pub optimize: bool,
    pub timeout_secs: u64,
    pub occurs_check: bool,
    pub first_only: bool,
}
