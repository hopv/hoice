use crate::common::{var_to::vals::VarValsSet, *};

/// A sample is some values for a predicate.
#[derive(Clone, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct Sample {
    /// Predicate the sample is for.
    pub pred: PrdIdx,
    /// Arguments.
    pub args: VarVals,
}
impl Sample {
    /// Constructor.
    pub fn new(pred: PrdIdx, args: VarVals) -> Self {
        Sample { pred, args }
    }

    /// Tests if a sample is about some predicate and its arguments is subsumed
    /// by one of the elements of a set.
    pub fn set_subsumed(&self, pred: PrdIdx, samples: &VarValsSet) -> bool {
        if self.pred != pred {
            false
        } else {
            self.args.set_subsumed(samples)
        }
    }

    /// Tests if a sample is about some predicate and its arguments is subsumed
    /// by one of the elements of a set.
    ///
    /// Samples from the set that are subsumed by `self` are removed if `rm`.
    pub fn set_subsumed_rm(&self, pred: PrdIdx, samples: &mut VarValsSet) -> (bool, usize) {
        if self.pred != pred {
            (false, 0)
        } else {
            self.args.set_subsumed_rm(samples)
        }
    }
}
impl<'a> PebcakFmt<'a> for Sample {
    type Info = &'a Preds;
    fn pebcak_err(&self) -> ErrorKind {
        "during sample pebcak formatting".into()
    }
    fn pebcak_io_fmt<W: Write>(&self, w: &mut W, map: &'a Preds) -> IoRes<()> {
        write!(w, "({}", map[self.pred].name)?;
        for arg in self.args.iter() {
            write!(w, " {}", arg)?
        }
        write!(w, ")")
    }
}
mylib::impl_fmt! {
    Sample(self, fmt) {
        write!(fmt, "p_{} {}", self.pred, self.args)
    }
}
