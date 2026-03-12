pub mod config;
pub mod mterms;
pub mod optimize;
pub mod translate;
mod env;
mod eval;
mod lvar;
mod senv;
mod step;
mod unify;
mod union_find;
mod value_type;
mod vclosure;

pub(crate) use env::Env;
pub(crate) use vclosure::VClosure;
pub use config::Config;
pub use eval::{eval, eval_collect, eval_streaming, run, Strategy};

pub type Ident = usize;

/// A computation closure: a computation paired with its environment.
pub type CClosure<'a> = (&'a mterms::MComputation<'a>, env::Env<'a>);
