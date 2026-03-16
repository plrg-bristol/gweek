use bumpalo::Bump;

use super::config::config;
use super::env::Env;
use super::lvar::LogicEnv;
use super::mterms::MValue;
use super::senv::{SuspAt, SuspEnv};
use super::VClosure;

pub enum UnifyError<'a> {
    Occurs,
    Fail,
    Susp {
        at: SuspAt<'a>,
        remaining: Vec<(VClosure<'a>, VClosure<'a>)>,
    },
}

pub fn unify<'a>(
    arena: &'a Bump,
    lhs: &'a MValue<'a>,
    rhs: &'a MValue<'a>,
    env: Env<'a>,
    lenv: &mut LogicEnv<'a>,
    senv: &SuspEnv<'a>,
) -> Result<(), UnifyError<'a>> {
    let q = vec![(VClosure::mk_clos(lhs, env), VClosure::mk_clos(rhs, env))];
    unify_loop(arena, q, lenv, senv)
}

pub fn unify_resume<'a>(
    arena: &'a Bump,
    queue: &[(VClosure<'a>, VClosure<'a>)],
    lenv: &mut LogicEnv<'a>,
    senv: &SuspEnv<'a>,
) -> Result<(), UnifyError<'a>> {
    unify_loop(arena, queue.to_vec(), lenv, senv)
}

fn unify_loop<'a>(
    arena: &'a Bump,
    mut q: Vec<(VClosure<'a>, VClosure<'a>)>,
    lenv: &mut LogicEnv<'a>,
    senv: &SuspEnv<'a>,
) -> Result<(), UnifyError<'a>> {
    while let Some((lhs, rhs)) = q.pop() {
        let lhs_r = match lhs.close_head(lenv, senv) {
            Ok(v) => v,
            Err(at) => {
                q.push((lhs, rhs));
                return Err(UnifyError::Susp { at, remaining: q });
            }
        };
        let rhs_r = match rhs.close_head(lenv, senv) {
            Ok(v) => v,
            Err(at) => {
                q.push((lhs_r, rhs));
                return Err(UnifyError::Susp { at, remaining: q });
            }
        };

        match (&lhs_r, &rhs_r) {
            (VClosure::LogicVar { ident: id1 }, VClosure::LogicVar { ident: id2 }) => {
                lenv.identify(*id1, *id2);
            }
            (VClosure::LogicVar { ident }, _) => {
                if config().occurs_check {
                    match rhs_r.occurs_lvar(lenv, senv, *ident) {
                        Ok(true) => return Err(UnifyError::Occurs),
                        Ok(false) => {}
                        Err(at) => {
                            q.push((lhs_r, rhs_r));
                            return Err(UnifyError::Susp { at, remaining: q });
                        }
                    }
                }
                lenv.set_vclos(*ident, rhs_r);
            }
            (_, VClosure::LogicVar { ident }) => {
                if config().occurs_check {
                    match lhs_r.occurs_lvar(lenv, senv, *ident) {
                        Ok(true) => return Err(UnifyError::Occurs),
                        Ok(false) => {}
                        Err(at) => {
                            q.push((lhs_r, rhs_r));
                            return Err(UnifyError::Susp { at, remaining: q });
                        }
                    }
                }
                lenv.set_vclos(*ident, lhs_r);
            }
            (
                VClosure::Clos {
                    val: lv,
                    env: lenv_r,
                },
                VClosure::Clos {
                    val: rv,
                    env: renv_r,
                },
            ) => match (lv, rv) {
                (MValue::Unit, MValue::Unit)
                | (MValue::Zero, MValue::Zero)
                | (MValue::Nil, MValue::Nil) => continue,

                // Nat vs Nat
                (MValue::Nat(a), MValue::Nat(b)) => {
                    if a != b {
                        return Err(UnifyError::Fail);
                    }
                }

                // Nat vs Zero/Succ (mixed representations)
                (MValue::Nat(0), MValue::Zero) | (MValue::Zero, MValue::Nat(0)) => continue,
                (MValue::Nat(n), MValue::Zero) | (MValue::Zero, MValue::Nat(n)) if *n > 0 => {
                    return Err(UnifyError::Fail);
                }
                (MValue::Nat(n), MValue::Succ(v)) if *n > 0 => {
                    let pred = arena.alloc(MValue::Nat(n - 1));
                    q.push((
                        VClosure::mk_clos(pred, *lenv_r),
                        VClosure::mk_clos(v, *renv_r),
                    ));
                }
                (MValue::Succ(v), MValue::Nat(n)) if *n > 0 => {
                    let pred = arena.alloc(MValue::Nat(n - 1));
                    q.push((
                        VClosure::mk_clos(v, *lenv_r),
                        VClosure::mk_clos(pred, *renv_r),
                    ));
                }
                (MValue::Nat(0), MValue::Succ(_)) | (MValue::Succ(_), MValue::Nat(0)) => {
                    return Err(UnifyError::Fail);
                }

                (MValue::Succ(v), MValue::Succ(w)) => {
                    q.push((VClosure::mk_clos(v, *lenv_r), VClosure::mk_clos(w, *renv_r)));
                }
                (MValue::Cons(x, xs), MValue::Cons(y, ys)) => {
                    q.push((VClosure::mk_clos(x, *lenv_r), VClosure::mk_clos(y, *renv_r)));
                    q.push((VClosure::mk_clos(xs, *lenv_r), VClosure::mk_clos(ys, *renv_r)));
                }
                (MValue::Pair(a, b), MValue::Pair(c, d)) => {
                    q.push((VClosure::mk_clos(a, *lenv_r), VClosure::mk_clos(c, *renv_r)));
                    q.push((VClosure::mk_clos(b, *lenv_r), VClosure::mk_clos(d, *renv_r)));
                }
                (MValue::Inl(a), MValue::Inl(b)) | (MValue::Inr(a), MValue::Inr(b)) => {
                    q.push((VClosure::mk_clos(a, *lenv_r), VClosure::mk_clos(b, *renv_r)));
                }
                (MValue::Thunk(_), _) | (_, MValue::Thunk(_)) => {
                    panic!("tried to unify a thunk")
                }
                _ => return Err(UnifyError::Fail),
            },
            (VClosure::Susp { .. }, _) | (_, VClosure::Susp { .. }) => {
                unreachable!("tried to unify a suspension")
            }
        }
    }
    Ok(())
}
