//! # The abstract machine
//!
//! Evaluation here is not a recursive function but a machine. A program is elaborated to a
//! Call-By-Push-Value term ([`mterms`]) and run on an explicit-state machine — the `step` module —
//! whose every state is an ordinary value. The idea is simple: at a branch point the machine is
//! *cloned*, each clone exploring one alternative, and a [`Strategy`] ([`eval()`]) chooses the
//! order. Everything lives in one `bumpalo` arena behind thin pointers, so a clone is cheap. The
//! logic engine is `unify`/`lvar`/`union_find`, laziness is `senv`/`vclosure`/`env`, and
//! [`Config`] is threaded by reference throughout.

pub mod config;
pub mod elaborate;
mod env;
mod eval;
mod lvar;
pub mod mterms;
pub mod optimize;
mod senv;
mod step;
mod unify;
mod union_find;
mod value_type;
mod vclosure;

pub use config::Config;
pub(crate) use env::Env;
pub use eval::{eval, eval_collect, eval_streaming, run, Strategy};
pub(crate) use vclosure::VClosure;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct LVar(pub usize);
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SuspId(pub usize);

/// A computation closure: a computation paired with its environment.
pub type CClosure<'a> = (&'a mterms::MComputation<'a>, env::Env<'a>);
