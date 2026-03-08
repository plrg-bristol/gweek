use std::sync::OnceLock;

use super::eval::Strategy;

static CONFIG: OnceLock<Config> = OnceLock::new();

#[derive(Debug)]
pub struct Config {
    pub strategy: Strategy,
    pub optimize: bool,
    pub timeout_secs: u64,
    pub occurs_check: bool,
    pub eager_vars: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            strategy: Strategy::Bfs,
            optimize: false,
            timeout_secs: 60,
            occurs_check: true,
            eager_vars: false,
        }
    }
}

pub fn init(cfg: Config) {
    CONFIG.set(cfg).expect("config already initialized");
}

pub fn config() -> &'static Config {
    CONFIG.get_or_init(Config::default)
}
