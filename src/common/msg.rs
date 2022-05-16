//! Messages used in the framework.

use std::cell::RefCell;
use std::sync::mpsc::channel;

use crate::{
    common::{profiling::Profiler, *},
    data::{AssData, LrnData},
};

/// Sender / receiver pair alias type.
pub type Channel<T> = (Sender<T>, Receiver<T>);

/// Type of processes the teacher can spawn, and how to id them.
#[derive(Clone, Copy)]
pub enum Id {
    /// Learners.
    Learner(LrnIdx),
    /// Assistant.
    Assistant,
}
impl Id {
    /// True if the id is that of a learner.
    pub fn is_learner(&self) -> bool {
        match *self {
            Id::Learner(_) => true,
            _ => false,
        }
    }

    /// True if the id is the assistant.
    pub fn is_assistant(&self) -> bool {
        match *self {
            Id::Assistant => true,
            _ => false,
        }
    }
}
impl fmt::Display for Id {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Id::Learner(idx) => write!(fmt, "learner#{}", idx),
            Id::Assistant => write!(fmt, "assistant"),
        }
    }
}

/// Kind of messages the teacher can receive.
pub enum MsgKind {
    /// Some candidates, from learners.
    Cands(Candidates),
    /// Some samples from the assistant.
    Samples(Box<AssData>),
    /// A message.
    Msg(String),
    /// An error.
    Err(Error),
    /// Unsat result.
    Unsat,
    /// Statistics.
    Stats(Profiler),
}

impl MsgKind {
    /// True if the message is a candidates message.
    pub fn is_candidates(&self) -> bool {
        match *self {
            MsgKind::Cands(_) => true,
            _ => false,
        }
    }

    /// True if the message is a samples message.
    pub fn is_samples(&self) -> bool {
        match *self {
            MsgKind::Samples(_) => true,
            _ => false,
        }
    }
}

impl From<Candidates> for MsgKind {
    fn from(cands: Candidates) -> MsgKind {
        MsgKind::Cands(cands)
    }
}
impl From<AssData> for MsgKind {
    fn from(data: AssData) -> MsgKind {
        MsgKind::Samples(Box::new(data))
    }
}
impl From<String> for MsgKind {
    fn from(msg: String) -> MsgKind {
        MsgKind::Msg(msg)
    }
}
impl From<Error> for MsgKind {
    fn from(err: Error) -> MsgKind {
        MsgKind::Err(err)
    }
}
impl From<Profiler> for MsgKind {
    fn from(profiler: Profiler) -> MsgKind {
        MsgKind::Stats(profiler)
    }
}

/// Messages the teacher can receive.
pub struct Msg {
    /// Id of the sender.
    pub id: Id,
    /// Actual message.
    pub msg: MsgKind,
}
impl Msg {
    /// Creates a message.
    pub fn new<M>(id: Id, msg: M) -> Self
    where
        M: Into<MsgKind>,
    {
        let msg = msg.into();
        debug_assert! { ! msg.is_candidates() || id.is_learner()   }
        debug_assert! {    ! msg.is_samples() || id.is_assistant() }

        Msg { id, msg }
    }

    /// Creates a candidates message.
    pub fn cands(id: Id, cands: Candidates) -> Self {
        debug_assert! { id.is_learner() }
        Msg {
            id,
            msg: MsgKind::Cands(cands),
        }
    }
    /// Creates a samples message.
    pub fn samples(id: Id, samples: AssData) -> Self {
        debug_assert! { id.is_assistant() }
        Msg {
            id,
            msg: MsgKind::Samples(Box::new(samples)),
        }
    }

    /// Channel to the teacher.
    pub fn channel() -> Channel<Msg> {
        channel()
    }
}

/// Data sent by the teacher.
pub enum FromTeacher {
    /// Exit message.
    Exit,
    /// Learning data.
    Data(Box<LrnData>),
}
impl FromTeacher {
    /// Channel from the teacher.
    pub fn channel() -> Channel<FromTeacher> {
        channel()
    }
}

/// Bails saying `"disconnected from teacher"`.
macro_rules! deco {
    () => {
        bail!("disconnected from teacher")
    };
}

/// Communication core.
///
/// Used by sub-processes to communicate with the teacher.
pub struct MsgCore {
    /// Identifier of the process.
    id: Id,
    /// Message channel to the teacher.
    sender: Sender<Msg>,
    /// Receives stuff from the teacher.
    recver: Receiver<FromTeacher>,
    /// Profiler.
    pub _profiler: Profiler,
    /// Some profilers whoever is above the core can use.
    _subs: RefCell<HashMap<&'static str, Profiler>>,
}

impl MsgCore {
    /// Creates a core for a learner.
    pub fn new_learner(id: LrnIdx, sender: Sender<Msg>, recver: Receiver<FromTeacher>) -> Self {
        MsgCore {
            id: Id::Learner(id),
            sender,
            recver,
            _profiler: Profiler::new(),
            _subs: RefCell::new(HashMap::new()),
        }
    }

    /// Creates a core for the assistant.
    pub fn new_assistant(sender: Sender<Msg>, recver: Receiver<FromTeacher>) -> Self {
        MsgCore {
            id: Id::Assistant,
            sender,
            recver,
            _profiler: Profiler::new(),
            _subs: RefCell::new(HashMap::new()),
        }
    }

    /// Merges a profiler with the subprofiler `name`.
    pub fn merge_prof(&self, name: &'static str, prof: Profiler) {
        self._subs
            .borrow_mut()
            .entry(name)
            .or_insert_with(Profiler::new)
            .merge(prof)
    }

    /// Merges a profiler with the subprofiler `name`.
    pub fn merge_set_prof(&self, name: &'static str, prof: Profiler) {
        self._subs
            .borrow_mut()
            .entry(name)
            .or_insert_with(Profiler::new)
            .merge_set(prof)
    }

    /// Sends some candidates.
    pub fn send_candidates(&self, candidates: Candidates) -> Res<()> {
        if self.sender.send(Msg::cands(self.id, candidates)).is_ok() {
            Ok(())
        } else {
            deco!()
        }
    }

    /// Sends some samples.
    pub fn send_samples(&self, samples: AssData) -> Res<()> {
        if self.sender.send(Msg::samples(self.id, samples)).is_ok() {
            Ok(())
        } else {
            deco!()
        }
    }

    /// Sends statistics.
    pub fn stats(self) -> Res<()> {
        for (name, prof) in self._subs.into_inner() {
            self._profiler.add_sub(name, prof)
        }
        if self.sender.send(Msg::new(self.id, self._profiler)).is_ok() {
            Ok(())
        } else {
            deco!()
        }
    }

    /// Sends a string message.
    #[cfg(not(feature = "bench"))]
    pub fn msg<S: Into<String>>(&self, s: S) -> Res<()> {
        if self.sender.send(Msg::new(self.id, s.into())).is_ok() {
            Ok(())
        } else {
            deco!()
        }
    }
    #[cfg(feature = "bench")]
    #[inline]
    pub fn msg<S>(&self, _: S) -> Res<()> {
        Ok(())
    }

    /// Sends an error message and then the stats.
    ///
    /// Equivalent to `self.unsat()` if the error is `Unsat`.
    pub fn err(self, err: Error) -> () {
        if err.is_unsat() {
            self.unsat()
        } else if err.is_exit() {
            self.exit()
        } else {
            let _ = self.sender.send(Msg::new(self.id, err));
            self.exit()
        }
    }

    /// Sends an unsat message and exits.
    pub fn unsat(self) -> () {
        if self.sender.send(Msg::new(self.id, MsgKind::Unsat)).is_ok() {
            self.exit()
        }
    }

    /// Exits, sends statistics.
    pub fn exit(self) -> () {
        let _ = self.stats();
        ()
    }

    /// Exit if we have received an exit message.
    #[inline]
    pub fn check_exit(&self) -> Res<()> {
        use std::sync::mpsc::TryRecvError::*;
        match self.recver.try_recv() {
            Ok(FromTeacher::Exit) => bail!(ErrorKind::Exit),
            Ok(_) => bail!("received data while checking for exit, logic error"),
            Err(Empty) => Ok(()),
            Err(Disconnected) => deco!(),
        }
    }

    /// Receives some data from the teacher.
    pub fn recv(&self) -> Res<LrnData> {
        match self.recver.recv() {
            Ok(FromTeacher::Exit) => bail!(ErrorKind::Exit),
            Ok(FromTeacher::Data(data)) => Ok(*data),
            Err(_) => deco!(),
        }
    }
}

/// A learner can be launched when given a core and an instance, and has a
/// description.
pub trait Learner: Sync + Send {
    /// Launches the learner.
    ///
    /// The boolean flag `mine` specifies whether the learner should mine the
    /// instance, typically for qualifiers.
    fn run(&self, core: MsgCore, instance: Arc<Instance>, data: LrnData, mine: bool);
    /// Short description of the learner.
    fn description(&self, mine: bool) -> String;
}

/// Messages from assistant.
pub enum FromAssistant {
    /// Positive and negative samples.
    Samples(Box<AssData>),
    /// Message.
    Msg(String),
    /// Error.
    Err(Error),
    /// Statistics.
    Stats(Profiler),
    /// Unsat.
    Unsat,
}
unsafe impl Send for FromAssistant {}

/// Messages to the assistant.
pub enum ToAssistant {
    /// Implication constraints.
    Samples(Box<AssData>),
    /// Exit message.
    Exit,
}

/// Channel from a teacher to an assistant.
pub fn new_to_assistant() -> Channel<ToAssistant> {
    channel()
}

/// Channel from the assistants to the teacher.
pub fn from_assistants() -> Channel<FromAssistant> {
    channel()
}

/// A communication core for assistants.
pub struct AssistantCore {
    /// Sends stuff to the teacher.
    sender: Sender<FromAssistant>,
    /// Receives stuff from the teacher.
    recver: Receiver<ToAssistant>,
    /// Profiler.
    pub _profiler: Profiler,
}
impl AssistantCore {
    /// Constructor.
    pub fn new(sender: Sender<FromAssistant>, recver: Receiver<ToAssistant>) -> Self {
        AssistantCore {
            sender,
            recver,
            _profiler: Profiler::new(),
        }
    }

    /// Sends some samples to the teacher. Returns `false` iff sending fails,
    /// **meaning the teacher is disconnected**.
    pub fn send_samples(&self, samples: AssData) -> bool {
        self.sender
            .send(FromAssistant::Samples(Box::new(samples)))
            .is_ok()
    }

    /// Sends statistics.
    #[cfg(not(feature = "bench"))]
    pub fn stats(self) -> bool {
        if conf.stats {
            self.sender
                .send(FromAssistant::Stats(self._profiler))
                .is_ok()
        } else {
            true
        }
    }
    #[cfg(feature = "bench")]
    pub fn stats(self) -> bool {
        true
    }

    /// Sends a message to the teacher. Returns `false` iff sending fails,
    /// **meaning the teacher is disconnected**.
    pub fn msg<S: Into<String>>(&self, s: S) -> bool {
        self.sender.send(FromAssistant::Msg(s.into())).is_ok()
    }
    /// Sends an error to the teacher. Returns `false` iff sending fails,
    /// **meaning the teacher is disconnected**.
    pub fn err(&self, err: Error) -> bool {
        if let ErrorKind::Unsat = *err.kind() {
            return self.unsat();
        }
        self.sender.send(FromAssistant::Err(err)).is_ok()
    }

    /// Sends an unsat result to the teacher. Returns `false` iff sending fails,
    /// **meaning the teacher is disconnected**.
    pub fn unsat(&self) -> bool {
        self.sender.send(FromAssistant::Unsat).is_ok()
    }

    /// Exits, destroys itself.
    pub fn exit(self) -> () {
        self.stats();
        ()
    }

    /// Exit if we have received an exit message.
    #[inline]
    pub fn check_exit(&self) -> Res<()> {
        use std::sync::mpsc::TryRecvError::*;
        match self.recver.try_recv() {
            Ok(ToAssistant::Exit) => bail!(ErrorKind::Exit),
            Ok(ToAssistant::Samples(_)) => {
                bail!("received data while checking for exit, logic error")
            }
            Err(Empty) => Ok(()),
            Err(Disconnected) => bail!("disconnected from teacher..."),
        }
    }

    /// Receive some learning data from the teacher.
    ///
    /// Returns `None` if an exit message was received.
    ///
    /// Error if disconnected.
    pub fn recv(&self) -> Res<Option<AssData>> {
        match self.recver.recv() {
            Ok(ToAssistant::Samples(data)) => Ok(Some(*data)),
            Ok(ToAssistant::Exit) => Ok(None),
            Err(_) => bail!("disconnected from teacher"),
        }
    }
}
