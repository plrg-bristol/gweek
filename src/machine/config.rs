use std::cell::Cell;

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

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
    static DEADLINE: Cell<Option<Instant>> = Cell::new(None);
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
    DEADLINE.with(|d| d.set(Some(Instant::now() + std::time::Duration::from_secs(cfg.timeout_secs))));
    CONFIG.with(|c| c.set(cfg));
}

pub fn config() -> Config {
    CONFIG.with(|c| c.get())
}

pub fn deadline() -> Instant {
    DEADLINE.with(|d| d.get().unwrap_or_else(|| Instant::now() + std::time::Duration::from_secs(3600)))
}
