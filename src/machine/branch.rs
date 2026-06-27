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
use super::senv::{SuspAt, SuspEnv, SuspState};
use super::step::{Machine, Stack};
use super::vclosure::VClosure;

/// Identifies a machine thread within a branch.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct MachineId(pub usize);

/// The role a thread plays in the branch.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MachineRole {
    Main,
    SuspEval { target: super::SuspId },
}

/// The state of a thread within the branch.
#[derive(Clone, Debug)]
pub enum ThreadState {
    Runnable,
    WaitingOn(super::SuspId),
    Returned(VClosure),
    Failed,
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
pub struct BranchAlternative {
    pub machine: Machine,
    pub lenv: LogicEnv,
    pub senv: SuspEnv,
}

impl fmt::Debug for BranchAlternative {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BranchAlternative")
            .field("machine", &self.machine)
            .finish()
    }
}

/// A single search branch: shared stores plus a set of live machines.
#[derive(Clone)]
pub struct Branch {
    pub machines: Vec<Option<Thread>>,
    pub ready: VecDeque<MachineId>,
    pub waiters: HashMap<super::SuspId, Vec<MachineId>>,
    pub main: MachineId,
    pub lenv: LogicEnv,
    pub senv: SuspEnv,
    pub obligations: Vec<super::SuspId>,
    pub candidate_answer: Option<VClosure>,
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
        // Never reuse slots; always append to avoid mid collisions
        // with threads that have been popped but will be re-queued.
        let id = MachineId(self.machines.len());
        self.machines.push(Some(thread));
        id
    }

    pub fn take_thread(&mut self, mid: MachineId) -> Thread {
        self.machines[mid.0]
            .take()
            .expect("take_thread on empty slot")
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

    pub fn block_on(
        &mut self,
        mid: MachineId,
        role: MachineRole,
        resume: Machine,
        susp: SuspAt,
    ) {
        let sid = susp.ident;
        let thread = Thread {
            machine: resume,
            role,
            state: ThreadState::WaitingOn(sid),
        };
        self.machines[mid.0] = Some(thread);
        self.waiters.entry(sid).or_default().push(mid);
        self.senv.mark_running(sid);
    }

    pub fn set_done(&mut self, sid: super::SuspId, vclos: VClosure) {
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

    pub fn thread_returned(
        &mut self,
        _mid: MachineId,
        role: MachineRole,
        vclos: VClosure,
        _heap: &mut Heap,
    ) {
        match role {
            MachineRole::Main => {
                self.candidate_answer = Some(vclos);
            }
            MachineRole::SuspEval { target } => {
                self.set_done(target, vclos);
            }
        }
    }

    pub fn ready_to_emit(&self) -> bool {
        self.candidate_answer.is_some() && self.obligations_done()
    }

    fn obligations_done(&self) -> bool {
        self.obligations.iter().all(|sid| matches!(self.senv.get(*sid), SuspState::Done(_)))
    }

    /// Start a thread for a pending obligation, if any remain.
    /// Returns true if a thread was started and pushed to the ready queue.
    pub fn start_pending_obligation(&mut self, heap: &mut Heap) -> bool {
        for &sid in &self.obligations {
            match self.senv.get(sid) {
                SuspState::Suspended(cclos) => {
                    self.senv.mark_running(sid);
                    let machine = Machine {
                        cclos,
                        stack: Stack::empty(heap),
                        done: false,
                    };
                    let thread = Thread::new(machine, MachineRole::SuspEval { target: sid });
                    let mid = self.insert_thread(thread);
                    self.ready.push_back(mid);
                    return true;
                }
                SuspState::Running(_) | SuspState::Done(_) => {}
            }
        }
        false
    }

    pub fn has_runnable(&self) -> bool {
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
}

