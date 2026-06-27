//! # The abstract machine
//!
//! Evaluation here is not a recursive function but a machine. A program is elaborated to a
//! Call-By-Push-Value term ([`mterms`]) and run on an explicit-state machine — the `step` module —
//! whose every state is an ordinary value. The idea is simple: at a branch point the machine is
//! *cloned*, each clone exploring one alternative, and a [`Strategy`] ([`eval()`]) chooses the
//! order. Every cell lives in one [`Heap`] named by an integer handle, so a clone copies only ids,
//! and a Cheney copying collector reclaims dead cells at the safe points between branches. The
//! logic engine is `unify`/`lvar`/`union_find`, laziness is `senv`/`vclosure`/`env`, and
//! [`Config`] is threaded by reference throughout.

pub mod branch;
pub mod config;
pub mod elaborate;
mod env;
mod eval;
pub mod heap;
mod lvar;
pub mod mterms;
pub mod optimize;
mod senv;
pub mod step;
mod unify;
mod union_find;
mod value_type;
mod vclosure;

pub use config::Config;
pub use eval::{eval, eval_collect, eval_streaming, run, Strategy};
pub use heap::Heap;
pub(crate) use env::Env;
pub(crate) use heap::{CompId, NodeId};
pub(crate) use vclosure::VClosure;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct LVar(pub usize);
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SuspId(pub usize);

/// A computation closure: a computation paired with its environment.
pub type CClosure = (CompId, env::Env);

