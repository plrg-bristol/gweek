//! # The search schedulers
//!
//! This module owns the search. It takes the heap and an initial machine, creates a
//! [`Branch`](super::branch::Branch) around it, then drives the branch under one of four
//! strategies, recording each solution.

use std::collections::{HashMap, HashSet, VecDeque};

#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use super::branch::{Branch, MachineRole, Thread};
use super::config::Config;
use super::env::Env;
use super::heap::{CompId, Heap};
use super::lvar::LogicEnv;
use super::senv::SuspEnv;
use super::step::{Clock, Machine, Stack, StepOutcome};
use super::vclosure::VClosure;
use super::NodeId;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Strategy { Bfs, Dfs, Iddfs, Fair }

// ── Public entry points ───────────────────────────────────────────

pub fn eval(cfg: &Config, heap: &mut Heap, comp: CompId, vals: &[NodeId]) {
    let env = import_env(heap, vals);
    let deadline = deadline_from(cfg);
    let mut on_solution = |s: &str| println!("> {}", s);
    let mut sink = Sink::new(cfg, &mut on_solution);
    let timed_out = run_internal(cfg, heap, comp, env, deadline, &mut sink);
    let solns = sink.count;
    if timed_out { println!(">>> timed out after {}s, {} solutions found", cfg.timeout_secs, solns); }
    else { println!(">>> {} solutions", solns); }
}

pub fn eval_collect(cfg: &Config, heap: &mut Heap, comp: CompId, vals: &[NodeId]) -> String {
    let env = import_env(heap, vals);
    let deadline = deadline_from(cfg);
    let mut solutions: Vec<String> = Vec::new();
    let timed_out = {
        let mut on_solution = |s: &str| solutions.push(format!("> {}", s));
        let mut sink = Sink::new(cfg, &mut on_solution);
        run_internal(cfg, heap, comp, env, deadline, &mut sink)
    };
    let solns = solutions.len();
    if timed_out { solutions.push(format!(">>> timed out after {}s, {} solutions found", cfg.timeout_secs, solns)); }
    else { solutions.push(format!(">>> {} solutions", solns)); }
    solutions.join("\n")
}

pub fn eval_streaming(cfg: &Config, heap: &mut Heap, comp: CompId, vals: &[NodeId], mut on_solution: impl FnMut(&str)) -> String {
    let env = import_env(heap, vals);
    let deadline = deadline_from(cfg);
    let mut cb = |s: &str| on_solution(&format!("> {}", s));
    let mut sink = Sink::new(cfg, &mut cb);
    let timed_out = run_internal(cfg, heap, comp, env, deadline, &mut sink);
    let solns = sink.count;
    if timed_out { format!(">>> timed out after {}s, {} solutions found", cfg.timeout_secs, solns) }
    else { format!(">>> {} solutions", solns) }
}

pub fn run(cfg: &Config, heap: &mut Heap, comp: CompId, vals: &[NodeId], print: bool) -> usize {
    let env = import_env(heap, vals);
    let deadline = deadline_from(cfg);
    if print {
        let mut on_solution = |s: &str| println!("> {}", s);
        let mut sink = Sink::new(cfg, &mut on_solution);
        run_internal(cfg, heap, comp, env, deadline, &mut sink);
        sink.count
    } else {
        let mut on_solution = |_: &str| {};
        let mut sink = Sink::new(cfg, &mut on_solution);
        run_internal(cfg, heap, comp, env, deadline, &mut sink);
        sink.count
    }
}

// ── Helpers ────────────────────────────────────────────────────────

fn import_env(heap: &mut Heap, vals: &[NodeId]) -> Env {
    let mut env = Env::empty_imm(heap);
    for val in vals { env = env.extend_val_imm(heap, *val, env); }
    env
}

fn deadline_from(cfg: &Config) -> Instant {
    Instant::now() + std::time::Duration::from_secs(cfg.timeout_secs)
}

fn run_internal(cfg: &Config, heap: &mut Heap, comp: CompId, env: Env, deadline: Instant, sink: &mut Sink) -> bool {
    match cfg.strategy {
        Strategy::Bfs => eval_bfs(cfg, heap, comp, env, deadline, sink),
        Strategy::Dfs => eval_dfs(cfg, heap, comp, env, deadline, sink),
        Strategy::Iddfs => eval_iddfs(cfg, heap, comp, env, deadline, sink),
        Strategy::Fair => eval_fair(cfg, heap, comp, env, deadline, sink),
    }
}

struct Sink<'a> {
    count: usize,
    seen: Option<HashSet<String>>,
    first_only: bool,
    on_solution: &'a mut dyn FnMut(&str),
}

impl<'a> Sink<'a> {
    fn new(cfg: &Config, on_solution: &'a mut dyn FnMut(&str)) -> Self {
        Sink { count: 0, seen: cfg.distinct.then(HashSet::new), first_only: cfg.first_only, on_solution }
    }
    fn record(&mut self, rendered: String) -> bool {
        if let Some(seen) = &mut self.seen { if !seen.insert(rendered.clone()) { return false; } }
        (self.on_solution)(&rendered);
        self.count += 1;
        self.first_only
    }
}

fn record_solution(heap: &Heap, branch: &Branch, sink: &mut Sink) -> bool {
    if let Some(vclos) = &branch.candidate_answer {
        return sink.record(output(heap, *vclos, &branch.lenv, &branch.senv));
    }
    false
}

fn fresh_branch(heap: &mut Heap, comp: CompId, env: Env) -> Branch {
    let machine = Machine { cclos: (comp, env), stack: Stack::empty(heap), done: false };
    Branch::new(heap, LogicEnv::new(), SuspEnv::new(), machine)
}

// ── Collection ─────────────────────────────────────────────────────

fn collect_branches<'b>(heap: &mut Heap, branches: impl Iterator<Item = &'b mut Branch>) {
    let mut v: Vec<&mut Branch> = branches.collect();
    heap.begin_minor();
    forward_roots(heap, &mut v);
    heap.scan();
    heap.end_minor();
    if heap.needs_major() {
        heap.begin_major();
        forward_roots(heap, &mut v);
        heap.scan();
        heap.end_major();
    }
}

fn forward_roots(heap: &mut Heap, branches: &mut [&mut Branch]) {
    let mut lenv_map: HashMap<usize, LogicEnv> = HashMap::new();
    let mut senv_map: HashMap<usize, SuspEnv> = HashMap::new();
    for b in branches.iter_mut() {
        let lkey = b.lenv.store_ptr();
        if let Some(c) = lenv_map.get(&lkey) { b.lenv = c.clone(); }
        else { let n = b.lenv.forwarded(heap); lenv_map.insert(lkey, n.clone()); b.lenv = n; }
        let skey = b.senv.store_ptr();
        if let Some(c) = senv_map.get(&skey) { b.senv = c.clone(); }
        else { let n = b.senv.forwarded(heap); senv_map.insert(skey, n.clone()); b.senv = n; }
        if let Some(vc) = &mut b.candidate_answer { *vc = (*vc).forward(heap); }
        for slot in b.machines.iter_mut().flatten() {
            slot.machine.cclos.1 = heap.forward_env(slot.machine.cclos.1);
            slot.machine.stack = Stack(heap.forward(slot.machine.stack.0));
        }
    }
}

fn output(heap: &Heap, vclos: VClosure, lenv: &LogicEnv, senv: &SuspEnv) -> String {
    match vclos.close(heap, lenv, senv) {
        Ok(closed) => closed.to_string(),
        Err(_) => "<cyclic term: cannot print (occurs check disabled)>".to_string(),
    }
}

// ── Step a single branch ──────────────────────────────────────────

enum BranchStep {
    Continue(Branch),
    Emitted(Branch),
    Forked(Vec<Branch>),
    Dead,
    NeedGc(Branch),
    TimedOut,
}

fn step_branch(cfg: &Config, heap: &mut Heap, mut branch: Branch, deadline: Instant) -> BranchStep {
    let (mid, thread) = match branch.pop_ready() {
        Some(pair) => pair,
        None => return if branch.ready_to_emit() { BranchStep::Emitted(branch) } else { BranchStep::Dead },
    };
    let role = thread.role;
    let machine = thread.machine;
    match machine.run_to_event(cfg, heap, &mut branch.lenv, &mut branch.senv, deadline) {
        StepOutcome::Continue(m) => { branch.put_runnable(mid, role, m); BranchStep::Continue(branch) }
        StepOutcome::Returned(vclos) => {
            branch.thread_returned(mid, role, vclos, heap);
            if branch.ready_to_emit() { BranchStep::Emitted(branch) }
            else if branch.has_runnable() { BranchStep::Continue(branch) }
            else { BranchStep::Dead }
        }
        StepOutcome::Fork(alternatives) => {
            let new_branches: Vec<Branch> = alternatives.into_iter()
                .map(|alt| Branch::new(heap, alt.lenv, alt.senv, alt.machine))
                .collect();
            BranchStep::Forked(new_branches)
        }
        StepOutcome::BlockedOn { susp, resume } => {
            branch.block_on(mid, role, resume, susp);
            let owner_id = branch.insert_thread(Thread::new(
                Machine { cclos: susp.cclos, stack: Stack::empty(heap), done: false },
                MachineRole::SuspEval { target: susp.ident },
            ));
            branch.ready.push_back(owner_id);
            BranchStep::Continue(branch)
        }
        StepOutcome::Failed => BranchStep::Dead,
        StepOutcome::NeedGc(m) => { branch.put_runnable(mid, role, m); BranchStep::NeedGc(branch) }
        StepOutcome::TimedOut => BranchStep::TimedOut,
    }
}

// ── BFS ────────────────────────────────────────────────────────────

fn eval_bfs(cfg: &Config, heap: &mut Heap, comp: CompId, env: Env, deadline: Instant, sink: &mut Sink) -> bool {
    let mut branches = vec![fresh_branch(heap, comp, env)];
    let mut next = Vec::new();
    let mut clock = Clock::new(deadline);
    while !branches.is_empty() {
        while let Some(mut branch) = branches.pop() {
            if clock.expired() { return true; }
            loop {
                match step_branch(cfg, heap, branch, deadline) {
                    BranchStep::Continue(b) => branch = b,
                    BranchStep::Emitted(b) => { if record_solution(heap, &b, sink) { return false; } break; }
                    BranchStep::Forked(nb) => { next.extend(nb); break; }
                    BranchStep::Dead => break,
                    BranchStep::NeedGc(b) => {
                        branch = b;
                        collect_branches(heap, std::iter::once(&mut branch).chain(branches.iter_mut()).chain(next.iter_mut()));
                    }
                    BranchStep::TimedOut => return true,
                }
            }
        }
        std::mem::swap(&mut branches, &mut next);
    }
    false
}

// ── DFS ────────────────────────────────────────────────────────────

fn eval_dfs(cfg: &Config, heap: &mut Heap, comp: CompId, env: Env, deadline: Instant, sink: &mut Sink) -> bool {
    let mut stack = vec![fresh_branch(heap, comp, env)];
    let mut clock = Clock::new(deadline);
    while let Some(mut branch) = stack.pop() {
        if clock.expired() { return true; }
        loop {
            match step_branch(cfg, heap, branch, deadline) {
                BranchStep::Continue(b) => branch = b,
                BranchStep::Emitted(b) => { if record_solution(heap, &b, sink) { return false; } break; }
                BranchStep::Forked(nb) => { for b in nb.into_iter().rev() { stack.push(b); } break; }
                BranchStep::Dead => break,
                BranchStep::NeedGc(b) => {
                    branch = b;
                    collect_branches(heap, std::iter::once(&mut branch).chain(stack.iter_mut()));
                }
                BranchStep::TimedOut => return true,
            }
        }
    }
    false
}

// ── IDDFS ──────────────────────────────────────────────────────────

fn eval_iddfs(cfg: &Config, heap: &mut Heap, comp: CompId, env: Env, deadline: Instant, sink: &mut Sink) -> bool {
    let mut depth_limit: usize = 1;
    loop {
        let mut cutoff = false;
        let mut stack: Vec<(Branch, usize)> = vec![(fresh_branch(heap, comp, env), 0)];
        let mut clock = Clock::new(deadline);
        while let Some((mut branch, depth)) = stack.pop() {
            if clock.expired() { return true; }
            if depth > depth_limit { cutoff = true; continue; }
            loop {
                match step_branch(cfg, heap, branch, deadline) {
                    BranchStep::Continue(b) => branch = b,
                    BranchStep::Emitted(b) => { if record_solution(heap, &b, sink) { return false; } break; }
                    BranchStep::Forked(nb) => {
                        let nd = depth + 1;
                        for b in nb.into_iter().rev() { stack.push((b, nd)); }
                        break;
                    }
                    BranchStep::Dead => break,
                    BranchStep::NeedGc(b) => {
                        branch = b;
                        collect_branches(heap, std::iter::once(&mut branch).chain(stack.iter_mut().map(|(b2, _)| b2)));
                    }
                    BranchStep::TimedOut => return true,
                }
            }
        }
        if !cutoff { break; }
        depth_limit *= 2;
    }
    false
}

// ── Fair ───────────────────────────────────────────────────────────

fn eval_fair(cfg: &Config, heap: &mut Heap, comp: CompId, env: Env, deadline: Instant, sink: &mut Sink) -> bool {
    const QUOTA: usize = 10000;
    const MAX_THREADS: usize = 10000;
    let mut queue: VecDeque<Vec<Branch>> = VecDeque::new();
    queue.push_back(vec![fresh_branch(heap, comp, env)]);
    let mut clock = Clock::new(deadline);
    while let Some(mut local) = queue.pop_front() {
        let mut steps = 0;
        while let Some(branch) = local.pop() {
            if clock.expired() { return true; }
            if steps >= QUOTA { local.push(branch); break; }
            steps += 1;
            match step_branch(cfg, heap, branch, deadline) {
                BranchStep::Continue(b) => local.push(b),
                BranchStep::Emitted(b) => { if record_solution(heap, &b, sink) { return false; } }
                BranchStep::Forked(nb) => {
                    if nb.len() > 1 && queue.len() < MAX_THREADS {
                        let mut first = true;
                        for b in nb { if first { local.push(b); first = false; } else { queue.push_back(vec![b]); } }
                    } else { for b in nb.into_iter().rev() { local.push(b); } }
                }
                BranchStep::Dead => {}
                BranchStep::NeedGc(b) => {
                    local.push(b);
                    collect_branches(heap, queue.iter_mut().flatten().chain(local.iter_mut()));
                }
                BranchStep::TimedOut => return true,
            }
        }
        if !local.is_empty() { queue.push_back(local); }
    }
    false
}

// ── Tests ──────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::machine::elaborate::elaborate;
    use crate::parser;

    fn test_config(strategy: Strategy) -> Config {
        Config { strategy, optimize: false, timeout_secs: 60, occurs_check: true, first_only: false, distinct: false }
    }

    fn solutions(src: &str, strategy: Strategy) -> Vec<String> {
        let mut heap = Heap::new();
        let ast = parser::parse(src).unwrap();
        let (comp, env_vals) = elaborate(&mut heap, ast);
        let env = import_env(&mut heap, &env_vals);
        let cfg = test_config(strategy);
        let deadline = Instant::now() + std::time::Duration::from_secs(60);
        let mut out = Vec::new();
        let timed_out = {
            let mut on_solution = |s: &str| out.push(s.to_string());
            let mut sink = Sink::new(&cfg, &mut on_solution);
            run_internal(&cfg, &mut heap, comp, env, deadline, &mut sink)
        };
        assert!(!timed_out, "test program timed out");
        out
    }

    #[test]
    fn inert_reports_free_variable() {
        let src = std::fs::read_to_string("examples/inert.gwk").unwrap();
        let solns = solutions(&src, Strategy::Bfs);
        assert_eq!(solns.len(), 1);
        assert!(solns[0].starts_with('_'), "expected a free-variable placeholder, got {:?}", solns[0]);
    }
}

