//! # The abstract machine
//!
//! The runtime core. A program is lowered to a Call-By-Push-Value term ([`mterms`]) and run on
//! an explicit-state machine (the private `step` module) whose every transition is one `step`.
//! Because the machine state is an ordinary value, it can be **cloned** at a branch point so
//! each clone explores one alternative; a search strategy ([`eval()`], [`Strategy`]) decides the
//! order. A recursive evaluator could not be paused, copied, and resumed this way.
//!
//! Everything — terms, environments, stacks — lives in a single `bumpalo` arena and is held by
//! thin reference, so cloning a machine is a handful of pointer copies.
//!
//! - [`mterms`] — the CBPV term language: values ([`MValue`](mterms::MValue)) vs. computations
//!   ([`MComputation`](mterms::MComputation)).
//! - `step` — the `Machine` state and its transition function.
//! - [`eval()`] / [`eval_collect`] / [`eval_streaming`] / [`run`] — the four search schedulers.
//! - [`translate`] — surface AST → CBPV; [`optimize`] — optional equational rewriting.
//! - `unify`, `lvar`, `union_find` — the logic engine; `senv`, `vclosure`, `env` — laziness.
//! - [`Config`] — the runtime knobs, threaded by reference throughout.

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

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct LVar(pub usize);
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct SuspId(pub usize);

/// A computation closure: a computation paired with its environment.
pub type CClosure<'a> = (&'a mterms::MComputation<'a>, env::Env<'a>);
