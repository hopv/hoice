use common::* ;

use data::args::SubsumeExt ;

/// A sample is some values for a predicate.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sample {
  /// Predicate the sample is for.
  pub pred: PrdIdx,
  /// Arguments.
  pub args: Args,
}
impl Sample {
  /// Constructor.
  pub fn new(pred: PrdIdx, args: Args) -> Self {
    Sample { pred, args }
  }

  /// Tests if a sample is about some predicate and its arguments is subsumed
  /// by one of the elements of a set.
  pub fn set_subsumed(
    & self, pred: PrdIdx, samples: & ArgsSet
  ) -> bool {
    if self.pred != pred {
      return false
    } else {
      self.args.set_subsumed(samples)
    }
  }

  /// Tests if a sample is about some predicate and its arguments is subsumed
  /// by one of the elements of a set.
  ///
  /// Samples from the set that are subsumed by `self` are removed if `rm`.
  pub fn set_subsumed_rm(
    & self, pred: PrdIdx, samples: & mut ArgsSet
  ) -> (bool, usize) {
    if self.pred != pred {
      (false, 0)
    } else {
      self.args.set_subsumed_rm(samples)
    }
  }
}
impl<'a> PebcakFmt<'a> for Sample {
  type Info = & 'a PrdInfos ;
  fn pebcak_err(& self) -> ErrorKind {
    "during sample pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, map: & 'a PrdInfos
  ) -> IoRes<()> {
    write!(w, "({}", map[self.pred].name) ? ;
    for arg in self.args.iter() {
      write!(w, " {}", arg) ?
    }
    write!(w, ")")
  }
}
impl_fmt!{
  Sample(self, fmt) {
    write!(fmt, "p_{} {}", self.pred, self.args)
  }
}