use std::cell::Cell;

use super::eval::Strategy;

thread_local! {
    static CONFIG: Cell<Config> = Cell::new(Config {
        strategy: Strategy::Bfs,
        optimize: false,
        timeout_secs: 60,
        occurs_check: true,
        eager_vars: false,
        strict: false,
        first_only: false,
    });
}

#[derive(Debug, Clone, Copy)]
pub struct Config {
    pub strategy: Strategy,
    pub optimize: bool,
    pub timeout_secs: u64,
    pub occurs_check: bool,
    pub eager_vars: bool,
    pub strict: bool,
    pub first_only: bool,
}

pub fn init(cfg: Config) {
    CONFIG.with(|c| c.set(cfg));
}

pub fn config() -> Config {
    CONFIG.with(|c| c.get())
}
