//! # The branch scheduler
//!
//! A [`Branch`] is the unit of search scheduling. It owns a logic environment,
//! a suspension environment, and a collection of live machine threads that
//! share those stores. Threads are conjunctive: they run cooperatively,
//! and failure of a required thread kills the whole branch.
//!
//! This module is introduced as part of the `need` refactor (see PLAN.md).
//! During Phase 1, the external behaviour is preserved: the branch still
//! drains pending suspensions sequentially after the main computation returns.

use std::collections::{HashMap, VecDeque};
use std::fmt;

use super::heap::Heap;
use super::lvar::LogicEnv;
use super::senv::{SuspEnv, SuspState};
use super::config::Config;
use super::step::{Event, Machine, Stack};
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant as StepInstant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant as StepInstant;
use super::vclosure::VClosure;
use super::SuspId;

/// Identifies a machine thread within a branch.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct MachineId(pub usize);

/// The role a thread plays in the branch.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MachineRole {
    Main,
    SuspEval { target: SuspId },
}

/// The state of a thread within the branch.
#[derive(Clone, Debug)]
pub enum ThreadState {
    Runnable,
    WaitingOn(SuspId),
}

/// A live thread in the branch.
#[derive(Clone, Debug)]
pub struct Thread {
    pub machine: Machine,
    pub role: MachineRole,
    pub state: ThreadState,
}

impl Thread {
    pub fn new(machine: Machine, role: MachineRole) -> Self {
        Thread {
            machine,
            role,
            state: ThreadState::Runnable,
        }
    }
}

/// An alternative branch when a logic-variable or Choice split occurs.
#[derive(Clone)]
pub struct Alt {
    pub machine: Machine,
    pub lenv: LogicEnv,
    pub senv: SuspEnv,
}

impl fmt::Debug for Alt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Alt")
            .field("machine", &self.machine)
            .finish()
    }
}

/// Events the Branch can emit after a scheduling step.
#[derive(Debug)]
pub(crate) enum BranchEvent {
    /// A solution was emitted.
    Emit(VClosure),
    /// The branch forked into several new branches.
    Split(Vec<Branch>),
    /// The branch still has work to do.
    More,
    /// The branch is dead (no runnable threads, no pending work).
    Dead,
    /// The heap needs collection.
    Gc,
    /// The deadline elapsed.
    Timeout,
}


/// A single search branch: shared stores plus a set of live machines.
#[derive(Clone)]
pub struct Branch {
    pub(crate) machines: Vec<Option<Thread>>,
    pub(crate) ready: VecDeque<MachineId>,
    pub(crate) waiters: HashMap<SuspId, Vec<MachineId>>,
    pub(crate) main: MachineId,
    pub(crate) lenv: LogicEnv,
    pub(crate) senv: SuspEnv,
    pub(crate) obligations: Vec<SuspId>,
    pub(crate) candidate_answer: Option<VClosure>,
}

impl fmt::Debug for Branch {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Branch")
            .field("machines", &self.machines.len())
            .field("ready", &self.ready)
            .field("main", &self.main)
            .field("obligations", &self.obligations)
            .field("candidate_answer", &self.candidate_answer.is_some())
            .finish()
    }
}

impl Branch {
    pub fn new(_heap: &mut Heap, lenv: LogicEnv, senv: SuspEnv, main_machine: Machine) -> Self {
        let main_thread = Thread::new(main_machine, MachineRole::Main);
        let main_id = MachineId(0);
        let mut branch = Branch {
            machines: vec![Some(main_thread)],
            ready: VecDeque::new(),
            waiters: HashMap::new(),
            main: main_id,
            lenv,
            senv,
            obligations: Vec::new(),
            candidate_answer: None,
        };
        branch.ready.push_back(main_id);
        branch
    }

    pub fn insert_thread(&mut self, thread: Thread) -> MachineId {
        let id = MachineId(self.machines.len());
        self.machines.push(Some(thread));
        id
    }

    pub fn put_runnable(&mut self, mid: MachineId, role: MachineRole, machine: Machine) {
        let thread = Thread {
            machine,
            role,
            state: ThreadState::Runnable,
        };
        self.machines[mid.0] = Some(thread);
        self.ready.push_back(mid);
    }

    pub fn block_on(&mut self, mid: MachineId, role: MachineRole, resume: Machine, sid: SuspId) {
        let thread = Thread {
            machine: resume,
            role,
            state: ThreadState::WaitingOn(sid),
        };
        self.machines[mid.0] = Some(thread);
        self.waiters.entry(sid).or_default().push(mid);
    }

    /// Mark a suspension as done and wake any waiters.
    fn done(&mut self, sid: SuspId, vclos: VClosure) {
        self.senv.set_done(sid, vclos);
        if let Some(waiters) = self.waiters.remove(&sid) {
            for mid in waiters {
                if let Some(Some(thread)) = self.machines.get(mid.0) {
                    if matches!(thread.state, ThreadState::WaitingOn(s) if s == sid) {
                        let mut t = self.machines[mid.0].take().unwrap();
                        t.state = ThreadState::Runnable;
                        self.machines[mid.0] = Some(t);
                        self.ready.push_back(mid);
                    }
                }
            }
        }
    }

    /// Check if the branch is ready to emit its candidate answer.
    fn check_emit(&self) -> Option<VClosure> {
        if self.candidate_answer.is_some() && self.obligations_done() {
            self.candidate_answer
        } else {
            None
        }
    }

    fn obligations_done(&self) -> bool {
        self.obligations.iter().all(|sid| matches!(self.senv.get(*sid), SuspState::Done(_)))
    }

    fn has_runnable(&self) -> bool {
        !self.ready.is_empty()
    }

    pub fn pop_ready(&mut self) -> Option<(MachineId, Thread)> {
        while let Some(mid) = self.ready.pop_front() {
            if let Some(Some(thread)) = self.machines.get(mid.0) {
                if matches!(thread.state, ThreadState::Runnable) {
                    let t = self.machines[mid.0].take().unwrap();
                    return Some((mid, t));
                }
            }
        }
        None
    }


    /// Clone the branch, replacing the thread at `mid` with a new one.
    /// The original thread should have been taken out (its slot is `None`).
    /// The new thread gets the given `machine` and `role`, and is added to ready.
    /// The branch's `lenv` and `senv` are replaced with the given ones.
    pub fn clone_with_thread(&self, mid: MachineId, role: MachineRole, machine: Machine, lenv: LogicEnv, senv: SuspEnv) -> Branch {
        let mut cloned = self.clone();
        let new_thread = Thread::new(machine, role);
        cloned.machines[mid.0] = Some(new_thread);
        cloned.lenv = lenv;
        cloned.senv = senv;
        cloned.ready.push_back(mid);
        cloned
    }

    /// Fork alternatives from a single machine into new branches.
    fn fork(&self, mid: MachineId, role: MachineRole, alts: Vec<Alt>) -> Vec<Branch> {
        alts.into_iter()
            .map(|alt| self.clone_with_thread(mid, role, alt.machine, alt.lenv, alt.senv))
            .collect()
    }
/// Verify internal consistency. Panics on violation.
pub fn check(&self) {
    // 1. Every machine in ready has state Runnable and its slot is occupied
    for &mid in &self.ready {
        match self.machines.get(mid.0) {
            Some(Some(thread)) => {
                assert!(matches!(thread.state, ThreadState::Runnable),
                    "ready machine {mid:?} not Runnable: {:?}", thread.state);
            }
            _ => panic!("ready machine {mid:?} has empty or missing slot"),
        }
    }

    // 2. Waiter consistency: every waiter has WaitingOn state matching the map key
    for (&sid, mids) in &self.waiters {
        for &mid in mids {
            match self.machines.get(mid.0) {
                Some(Some(thread)) => {
                    assert!(matches!(thread.state, ThreadState::WaitingOn(s) if s == sid),
                        "waiter {mid:?} expected WaitingOn({sid:?}), got {:?}", thread.state);
                }
                _ => panic!("waiter {mid:?} for {sid:?} has empty or missing slot"),
            }
        }
    }

    // 3. Main machine id is valid
    assert!(self.machines.get(self.main.0).is_some(), "main {:?} out of bounds (machines len {})", self.main, self.machines.len());

    // 4. SuspEval targets consistent with SuspState::Run
    for (i, slot) in self.machines.iter().enumerate() {
        if let Some(thread) = slot {
            if let MachineRole::SuspEval { target } = thread.role {
                match self.senv.get(target) {
                    SuspState::Run(mid, _) => {
                        assert!(mid.0 == i, "SuspEval at {i} target {target:?} but senv says Run({})", mid.0);
                    }
                    SuspState::Done(_) => {} // already done, stale machine slot
                    SuspState::Susp(_) => panic!("SuspEval at {i} target {target:?} but senv says Susp"),
                }
            }
        }
    }

    // 5. Every Running suspension has a corresponding SuspEval machine
    for (sid, state) in self.senv.iter() {
        if let SuspState::Run(mid, _) = state {
            match self.machines.get(mid.0) {
                Some(Some(thread)) => {
                    assert!(matches!(thread.role, MachineRole::SuspEval { target } if target == sid),
                        "Run({sid:?}) points to {mid:?} but role is {:?}", thread.role);
                }
                _ => panic!("Run({sid:?}) points to empty or missing slot {mid:?}"),
            }
        }
    }

    // 6. If candidate_answer is set and there is no runnable work left,
    if self.candidate_answer.is_some() && !self.has_runnable() {
        assert!(self.obligations_done(),
            "candidate_answer set but obligations not done: {:?}", self.obligations);
    }
}
    /// Advance the branch by one quantum: pop the next ready thread, run it,
    /// and handle the resulting event.
pub(crate) fn step(&mut self, heap: &mut Heap, cfg: &Config, deadline: StepInstant) -> BranchEvent {
    #[cfg(debug_assertions)]
    self.check();
        let (mid, thread) = match self.pop_ready() {
            Some(p) => p,
            None => {
                if let Some(v) = self.check_emit() {
                    return BranchEvent::Emit(v);
                }
                return BranchEvent::Dead;
            }
        };
        let mut machine = thread.machine;
        let role = thread.role;
        match machine.run(heap, &mut self.lenv, &mut self.senv, cfg, deadline) {
            Event::Ret(vclos) => {
                match role {
                    MachineRole::Main => self.candidate_answer = Some(vclos),
                    MachineRole::SuspEval { target } => self.done(target, vclos),
                }
                if let Some(v) = self.check_emit() {
                    BranchEvent::Emit(v)
                } else if self.has_runnable() {
                    BranchEvent::More
                } else {
                    BranchEvent::Dead
                }
            }
            Event::Fail => BranchEvent::Dead,
            Event::Split(alts) => {
                let branches = self.fork(mid, role, alts);
                BranchEvent::Split(branches)
            }
            Event::Need(sid) => {
                self.obligations.push(sid);
                // Start evaluating the suspension
                let cclos = self.senv.get_suspension(sid);
                self.senv.mark_running(sid, MachineId(self.machines.len()));
                let susp_machine = Machine { cclos, stack: Stack::empty(heap) };
                let susp_mid = self.insert_thread(Thread::new(susp_machine, MachineRole::SuspEval { target: sid }));
                self.ready.push_back(susp_mid);
                // Continue current machine
                self.put_runnable(mid, role, machine);
                BranchEvent::More
            }
            Event::Wait(sid) => {
                let need_eval = matches!(self.senv.get(sid), SuspState::Susp(_));
                self.block_on(mid, role, machine, sid);
                if need_eval {
                    let cclos = self.senv.get_suspension(sid);
                    self.senv.mark_running(sid, MachineId(self.machines.len()));
                    let susp_machine = Machine { cclos, stack: Stack::empty(heap) };
                    let susp_mid = self.insert_thread(Thread::new(susp_machine, MachineRole::SuspEval { target: sid }));
                    self.ready.push_back(susp_mid);
                }
                BranchEvent::More
            }
            Event::Gc => {
                self.put_runnable(mid, role, machine);
                BranchEvent::Gc
            }
            Event::Timeout => BranchEvent::Timeout,
        }
    }
}

