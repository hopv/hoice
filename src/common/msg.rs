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


/// Sender / receiver pair alias type.
pub type Channel<T> = (Sender<T>, Receiver<T>) ;


/// Channel from a teacher to a learner.
pub fn new_to_learner() -> Channel<DataCore> { channel() }


/// Channel from the learners to the teachers
pub fn from_learners() -> Channel<(LrnIdx, FromLearners)> { channel() }



/// A learner can be launched when given a core and an instance, and has a
/// description.
pub trait Learner: Sync + Send {
  /// Launches the learner.
  fn run(
    & self, LearnerCore, Arc<Instance>, DataCore
  ) ;
  /// Short description of the learner.
  fn description(& self) -> String ;
}




/// A learner can be launched given some info.
pub struct LearnerCore {
  /// Index of the learner w.r.t. the teacher.
  idx: LrnIdx,
  /// Sends stuff to the teacher.
  sender: Sender<(LrnIdx, FromLearners)>,
  /// Receives stuff from the teacher.
  recver: Receiver<DataCore>
}
impl LearnerCore {
  /// Constructor.
  pub fn new(
    idx: LrnIdx,
    sender: Sender<(LrnIdx, FromLearners)>,
    recver: Receiver<DataCore>,
  ) -> Self {
    LearnerCore { idx, sender, recver }
  }
}
impl HasLearnerCore for LearnerCore {
  fn core(& self) -> & LearnerCore { self }
}
/// Helpers learners can use if they make their core accessible.
pub trait HasLearnerCore {
  /// Learner core accessor.
  fn core(& self) -> & LearnerCore ;

  /// Sends some candidates to the teacher. Returns `false` iff sending fails,
  /// **meaning the teacher is disconnected**.
  fn send_candidates(& self, candidates: Candidates) -> bool {
    self.core().sender.send(
      ( self.core().idx, FromLearners::Cands(candidates) )
    ).is_ok()
  }
  /// Sends statistics.
  #[cfg( not(feature = "bench") )]
  fn stats(
    & self, profile: Profiler, lift: Vec< Vec<& 'static str> >
  ) -> bool {
    let (mut tree, stats) = profile.extract_tree() ;
    for lift in lift {
      if let Err(e) = tree.lift(lift) {
        self.err(e) ;
      }
    }
    self.core().sender.send(
      ( self.core().idx, FromLearners::Stats( tree, stats ) )
    ).is_ok()
  }
  #[cfg(feature = "bench")]
  fn stats(
    & self, _: Profiler, _: Vec< Vec<& 'static str> >
  ) -> bool {
    true
  }
  /// Sends a message to the teacher. Returns `false` iff sending fails,
  /// **meaning the teacher is disconnected**.
  fn msg<S: Into<String>>(& self, s: S) -> bool {
    self.core().sender.send(
      ( self.core().idx, FromLearners::Msg(s.into()) )
    ).is_ok()
  }
  /// Sends an error to the teacher. Returns `false` iff sending fails,
  /// **meaning the teacher is disconnected**.
  fn err(& self, err: Error) -> bool {
    match * err.kind() {
      ErrorKind::Unsat => return self.unsat(),
      _ => (),
    }
    self.core().sender.send(
      ( self.core().idx, FromLearners::Err(err) )
    ).is_ok()
  }
  /// Sends an unsat result to the teacher. Returns `false` iff sending fails,
  /// **meaning the teacher is disconnected**.
  fn unsat(& self) -> bool {
    self.core().sender.send(
      ( self.core().idx, FromLearners::Unsat )
    ).is_ok()
  }

  /// Receive some learning data from the teacher. Returns `None` iff receiving
  /// fails, **meaning the teacher is disconnected**.
  fn recv(& self) -> Option<DataCore> {
    if let Ok(data) = self.core().recver.recv() { Some(data) } else { None }
  }
}