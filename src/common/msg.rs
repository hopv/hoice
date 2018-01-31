//! Messages used in the framework.

use std::sync::mpsc::channel ;

use common::* ;
use common::data::* ;

use common::profiling::{ ProfileTree, Stats } ;


/// From one or more learners to the teacher.
pub enum FromLearners {
  /// Some candidates.
  Cands(Candidates),
  /// A message.
  Msg( String ),
  /// An error.
  Err( Error ),
  /// Unsat result.
  Unsat,
  /// Statistics.
  Stats( ProfileTree, Stats ),
}
unsafe impl Send for FromLearners {}

/// From the teacher to the learners.
pub enum FromTeacher {
  /// A data core, normal information sent to learners.
  Data(DataCore),
  /// Exit message.
  Exit
}
unsafe impl Send for FromTeacher {}


/// Sender / receiver pair alias type.
pub type Channel<T> = (Sender<T>, Receiver<T>) ;


/// Channel from a teacher to a learner.
pub fn new_to_learner() -> Channel<FromTeacher> { channel() }


/// Channel from the learners to the teachers
pub fn from_learners() -> Channel<(LrnIdx, FromLearners)> { channel() }



/// A learner can be launched when given a core and an instance, and has a
/// description.
pub trait Learner: Sync + Send {
  /// Launches the learner.
  ///
  /// The boolean flag `mine` specifies whether the learner should mine the
  /// instance, typically for qualifiers.
  fn run(
    & self, LearnerCore, Arc<Instance>, DataCore, mine: bool
  ) ;
  /// Short description of the learner.
  fn description(& self, mine: bool) -> String ;
}




/// A learner can be launched given some info.
pub struct LearnerCore {
  /// Index of the learner w.r.t. the teacher.
  idx: LrnIdx,
  /// Sends stuff to the teacher.
  sender: Sender<(LrnIdx, FromLearners)>,
  /// Receives stuff from the teacher.
  recver: Receiver<FromTeacher>,
  /// Profiler.
  pub _profiler: Profiler,
}
impl LearnerCore {
  /// Constructor.
  pub fn new(
    idx: LrnIdx,
    sender: Sender<(LrnIdx, FromLearners)>,
    recver: Receiver<FromTeacher>
  ) -> Self {
    LearnerCore {
      idx, sender, recver, _profiler: Profiler::new()
    }
  }

  /// Sends some candidates to the teacher. Returns `false` iff sending fails,
  /// **meaning the teacher is disconnected**.
  pub fn send_candidates(& self, candidates: Candidates) -> bool {
    self.sender.send(
      ( self.idx, FromLearners::Cands(candidates) )
    ).is_ok()
  }
  /// Sends statistics.
  #[cfg( not(feature = "bench") )]
  pub fn stats(self) -> bool {
    let (tree, stats) = self._profiler.extract_tree() ;
    self.sender.send(
      ( self.idx, FromLearners::Stats( tree, stats ) )
    ).is_ok()
  }
  #[cfg(feature = "bench")]
  pub fn stats(self) -> bool {
    true
  }
  /// Sends a message to the teacher. Returns `false` iff sending fails,
  /// **meaning the teacher is disconnected**.
  pub fn msg<S: Into<String>>(& self, s: S) -> bool {
    self.sender.send(
      ( self.idx, FromLearners::Msg(s.into()) )
    ).is_ok()
  }
  /// Sends an error to the teacher. Returns `false` iff sending fails,
  /// **meaning the teacher is disconnected**.
  pub fn err(& self, err: Error) -> bool {
    match err.kind() {
      & ErrorKind::Unsat => return self.unsat(),
      _ => (),
    }
    self.sender.send(
      ( self.idx, FromLearners::Err(err) )
    ).is_ok()
  }
  /// Sends an unsat result to the teacher. Returns `false` iff sending fails,
  /// **meaning the teacher is disconnected**.
  pub fn unsat(& self) -> bool {
    self.sender.send(
      ( self.idx, FromLearners::Unsat )
    ).is_ok()
  }

  /// Exits, destroys itself.
  pub fn exit(self) -> () {
    self.stats() ;
    ()
  }

  /// Exit if we have received an exit message.
  #[inline]
  pub fn check_exit(& self) -> ::errors::learners::LRes<()> {
    use std::sync::mpsc::TryRecvError::* ;
    match self.recver.try_recv() {
      Ok(FromTeacher::Exit) => bail!( ::errors::learners::LError::Exit ),
      Ok(FromTeacher::Data(_)) => bail!(
        "received data while checking for exit, logic error"
      ),
      Err(Empty) => Ok(()),
      Err(Disconnected) => bail!(
        "disconnected from teacher..."
      ),
    }
  }

  /// Receive some learning data from the teacher. Returns `None` iff receiving
  /// fails, **meaning the teacher is disconnected**.
  pub fn recv(& self) -> Option<DataCore> {
    if let Ok(data) = self.recver.recv() {
      match data {
        FromTeacher::Data(core) => Some(core),
        FromTeacher::Exit => None,
      }
    } else {
      None
    }
  }
}