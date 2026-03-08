use bumpalo::Bump;

use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::MValue;
use super::senv::{SuspAt, SuspEnv};
use super::Ident;

#[derive(Clone, Copy, Debug)]
pub enum VClosure<'a> {
    Clos { val: &'a MValue<'a>, env: Env<'a> },
    LogicVar { ident: Ident },
    Susp { ident: Ident },
}

impl<'a> VClosure<'a> {
    pub fn mk_clos(val: &'a MValue<'a>, env: Env<'a>) -> VClosure<'a> {
        VClosure::Clos { val, env }
    }

    pub fn occurs_lvar(
        &self,
        lenv: &LogicEnv<'a>,
        senv: &SuspEnv<'a>,
        ident: Ident,
    ) -> Result<bool, SuspAt<'a>> {
        match self.close_head(lenv, senv)? {
            VClosure::Clos { val, env } => match val {
                MValue::Succ(v) => VClosure::mk_clos(v, env).occurs_lvar(lenv, senv, ident),
                MValue::Cons(v, w) => Ok(
                    VClosure::mk_clos(v, env).occurs_lvar(lenv, senv, ident)?
                        || VClosure::mk_clos(w, env).occurs_lvar(lenv, senv, ident)?,
                ),
                MValue::Var(_) => unreachable!("value should be head-closed in occurs check"),
                MValue::Thunk(_) => panic!("occurs check on a computation"),
                _ => Ok(false),
            },
            VClosure::LogicVar { ident: ident2 } => Ok(ident == ident2),
            VClosure::Susp { .. } => todo!("occurs check on suspension"),
        }
    }

    pub fn close_head(self, lenv: &LogicEnv<'a>, senv: &SuspEnv<'a>) -> Result<VClosure<'a>, SuspAt<'a>> {
        let mut vclos = self;
        loop {
            vclos = match &vclos {
                VClosure::Clos { val, env } => match val {
                    MValue::Var(i) => env.lookup(*i).expect("index undefined in env"),
                    _ => break,
                },
                VClosure::LogicVar { ident } => match lenv.lookup(*ident) {
                    Some(vclos) => vclos,
                    None => break,
                },
                VClosure::Susp { ident } => senv.lookup(ident)?,
            }
        }
        Ok(vclos)
    }

    pub fn close(&self, arena: &'a Bump, lenv: &LogicEnv<'a>, senv: &SuspEnv<'a>) -> Option<&'a MValue<'a>> {
        match self {
            VClosure::Clos { val, env } => match val {
                MValue::Var(i) => env.lookup(*i)?.close(arena, lenv, senv),
                MValue::Zero => Some(arena.alloc(MValue::Zero)),
                MValue::Succ(v) => {
                    let inner = VClosure::mk_clos(v, *env).close(arena, lenv, senv)?;
                    Some(arena.alloc(MValue::Succ(inner)))
                }
                MValue::Nil => Some(arena.alloc(MValue::Nil)),
                MValue::Cons(v, w) => Some(arena.alloc(MValue::Cons(
                    VClosure::mk_clos(v, *env).close(arena, lenv, senv)?,
                    VClosure::mk_clos(w, *env).close(arena, lenv, senv)?,
                ))),
                MValue::Pair(fst, snd) => Some(arena.alloc(MValue::Pair(
                    VClosure::mk_clos(fst, *env).close(arena, lenv, senv)?,
                    VClosure::mk_clos(snd, *env).close(arena, lenv, senv)?,
                ))),
                MValue::Inl(v) => {
                    let inner = VClosure::mk_clos(v, *env).close(arena, lenv, senv)?;
                    Some(arena.alloc(MValue::Inl(inner)))
                }
                MValue::Inr(v) => {
                    let inner = VClosure::mk_clos(v, *env).close(arena, lenv, senv)?;
                    Some(arena.alloc(MValue::Inr(inner)))
                }
                MValue::Thunk(t) => panic!("tried to close thunk: {}", t),
            },
            VClosure::LogicVar { ident } => lenv.lookup(*ident)?.close(arena, lenv, senv),
            VClosure::Susp { ident } => senv
                .lookup(ident)
                .expect("unexpected suspension")
                .close(arena, lenv, senv),
        }
    }
}
