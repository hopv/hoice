//! Messages used in the framework.

use std::sync::mpsc::channel ;

use common::* ;
use common::data::* ;


wrap_usize!{
  #[doc = "Learner index."]
  LrnIdx
  #[doc = "Map of learners"]
  hash map: LrnHMap
  #[doc = "Total map from learners to something."]
  map: LrnMap with iter: LrnMapIter
}
unsafe impl Send for LrnIdx {}


/// From one or more learners to the teacher.
pub enum FromLearners {
  /// Some candidates.
  Cands(Candidates),
  /// A message.
  Msg( String ),
  /// An error.
  Err( Error )
}
unsafe impl Send for FromLearners {}


/// Sender / receiver pair alias type.
pub type Channel<T> = (Sender<T>, Receiver<T>) ;


/// Channel from a teacher to a learner.
pub fn to_learner() -> Channel<LearningData> { channel() }


/// Channel from the learners to the teachers
pub fn from_learners() -> Channel<(LrnIdx, FromLearners)> { channel() }



/// A learner can be launched when given a core and an instance, and has a
/// description.
pub trait Learner: Sync + Send {
  /// Launches the learner.
  fn run(
    & self, LearnerCore, Arc<::instance::Instance>, Arc<::common::data::Data>
  ) ;
  /// Short description of the learner.
  fn description(& self) -> String ;
}



/// Messaging macro, compiled to nothing in `release`.
#[macro_export]
#[cfg( feature = "bench" )]
macro_rules! msg {
  ( $($tt:tt)* ) => (()) ;
}
#[cfg( not(feature = "bench") )]
macro_rules! msg {
  ( debug $slf:expr => $($tt:tt)* ) => (
    if conf.verb == Verb::Debug {
      msg!( $slf => $($tt)* )
    } else { true }
  ) ;
  ( $slf:expr => $e:expr ) => (
    ::common::msg::HasLearnerCore::msg(
      $slf, $e
    )
  ) ;
  ( $slf:expr => $($tt:tt)* ) => (
    ::common::msg::HasLearnerCore::msg(
      $slf, format!( $($tt)* )
    )
  ) ;
}



/// A learner can be launched given some info.
pub struct LearnerCore {
  /// Index of the learner w.r.t. the teacher.
  idx: LrnIdx,
  /// Sends stuff to the teacher.
  sender: Sender<(LrnIdx, FromLearners)>,
  /// Receives stuff from the teacher.
  recver: Receiver<LearningData>
}
impl LearnerCore {
  /// Constructor.
  pub fn mk(
    idx: LrnIdx,
    sender: Sender<(LrnIdx, FromLearners)>,
    recver: Receiver<LearningData>,
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
    self.core().sender.send(
      ( self.core().idx, FromLearners::Err(err) )
    ).is_ok()
  }

  /// Receive some learning data from the teacher. Returns `None` iff receiving
  /// fails, **meaning the teacher is disconnected**.
  fn recv(& self) -> Option<LearningData> {
    if let Ok(data) = self.core().recver.recv() { Some(data) } else { None }
  }
}