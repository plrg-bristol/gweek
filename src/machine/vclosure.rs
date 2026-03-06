use std::rc::Rc;

use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::{MComputation, MValue};
use super::senv::{SuspAt, SuspEnv};
use super::Ident;

#[derive(Clone, Debug)]
pub enum VClosure {
    Clos { val: Rc<MValue>, env: Rc<Env> },
    LogicVar { ident: Ident },
    Susp { ident: Ident },
}

impl VClosure {
    pub fn mk_clos(val: &Rc<MValue>, env: &Rc<Env>) -> VClosure {
        VClosure::Clos {
            val: val.clone(),
            env: env.clone(),
        }
    }

    pub fn occurs_lvar(
        &self,
        lenv: &LogicEnv,
        senv: &SuspEnv,
        ident: Ident,
    ) -> Result<bool, SuspAt> {
        match self.clone().close_head(lenv, senv)? {
            VClosure::Clos { val, env } => match &*val {
                MValue::Succ(v) => VClosure::mk_clos(v, &env).occurs_lvar(lenv, senv, ident),
                MValue::Cons(v, w) => Ok(
                    VClosure::mk_clos(v, &env).occurs_lvar(lenv, senv, ident)?
                        || VClosure::mk_clos(w, &env).occurs_lvar(lenv, senv, ident)?,
                ),
                MValue::Var(_) => unreachable!("value should be head-closed in occurs check"),
                MValue::Thunk(_) => panic!("occurs check on a computation"),
                _ => Ok(false),
            },
            VClosure::LogicVar { ident: ident2 } => Ok(ident == ident2),
            VClosure::Susp { .. } => todo!("occurs check on suspension"),
        }
    }

    pub fn close_head(self, lenv: &LogicEnv, senv: &SuspEnv) -> Result<VClosure, SuspAt> {
        let mut vclos = self;
        loop {
            vclos = match &vclos {
                VClosure::Clos { val, env } => match &**val {
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

    pub fn close(&self, lenv: &LogicEnv, senv: &SuspEnv) -> Option<MValue> {
        match self {
            VClosure::Clos { val, env } => match &**val {
                MValue::Var(i) => env.lookup(*i)?.close(lenv, senv),
                MValue::Zero => Some(MValue::Zero),
                MValue::Succ(v) => {
                    Some(MValue::Succ(VClosure::mk_clos(v, env).close(lenv, senv)?.into()))
                }
                MValue::Nil => Some(MValue::Nil),
                MValue::Cons(v, w) => Some(MValue::Cons(
                    VClosure::mk_clos(v, env).close(lenv, senv)?.into(),
                    VClosure::mk_clos(w, env).close(lenv, senv)?.into(),
                )),
                MValue::Pair(fst, snd) => Some(MValue::Pair(
                    VClosure::mk_clos(fst, env).close(lenv, senv)?.into(),
                    VClosure::mk_clos(snd, env).close(lenv, senv)?.into(),
                )),
                MValue::Inl(v) => {
                    Some(MValue::Inl(VClosure::mk_clos(v, env).close(lenv, senv)?.into()))
                }
                MValue::Inr(v) => {
                    Some(MValue::Inr(VClosure::mk_clos(v, env).close(lenv, senv)?.into()))
                }
                MValue::Thunk(t) => panic!("tried to close thunk: {}", t),
            },
            VClosure::LogicVar { ident } => lenv.lookup(*ident)?.close(lenv, senv),
            VClosure::Susp { ident } => senv
                .lookup(ident)
                .expect("unexpected suspension")
                .close(lenv, senv),
        }
    }
}
