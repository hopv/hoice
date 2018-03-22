use std::cmp::Ordering ;

use hashconsing::{ HashConsign, HConsed } ;

use common::* ;


/// Mapping from variables to values, used for learning data.
#[derive(PartialEq, Eq, Hash, Clone, Debug)]
pub struct RArgs {
  /// Internal map.
  map: VarMap<Val>,
}

impl_fmt! {
  RArgs(self, fmt) {
    self.map.fmt(fmt)
  }
}
impl ::std::ops::Deref for RArgs {
  type Target = VarMap<Val> ;
  fn deref(& self) -> & VarMap<Val> { & self.map }
}
impl ::std::ops::DerefMut for RArgs {
  fn deref_mut(& mut self) -> & mut VarMap<Val> { & mut self.map }
}
impl From< VarMap<Val> > for RArgs {
  fn from(map: VarMap<Val>) -> Self {
    RArgs::new(map)
  }
}
impl Evaluator for RArgs {
  #[inline]
  fn get(& self, var: VarIdx) -> & Val {
    & self.map[var]
  }
  #[inline]
  fn len(& self) -> usize { VarMap::len(& self.map) }
}

impl RArgs {
  /// Constructor.
  pub fn new(map: VarMap<Val>) -> Self {
    RArgs { map }
  }

  /// Constructor with some capacity.
  pub fn with_capacity(capa: usize) -> Self {
    Self::new( VarMap::with_capacity(capa) )
  }

  /// True if at least one value is `Val::N`.
  pub fn is_partial(& self) -> bool {
    for v in self.iter() {
      if ! v.is_known() { return true }
    }
    false
  }

  /// True if the two args are semantically the same.
  ///
  /// "Semantically" here means that `Val::N` is not equal to itself.
  pub fn equal(& self, other: & Self) -> bool {
    for (v_1, v_2) in self.map.iter().zip( other.map.iter() ) {
      if ! v_1.equal(v_2) { return false }
    }
    true
  }

  /// Constructor from a model.
  pub fn of_model<T>(
    info: & VarMap<::instance::info::VarInfo>,
    model: Vec<(VarIdx, T, Val)>,
    partial: bool,
  ) -> Res<Self> {
    let mut slf = RArgs::new(
      info.iter().map(
        |info| if partial {
          Val::N
        } else {
          let default = info.typ.default_val() ;
          default
        }
      ).collect()
    ) ;
    for (var, _, val) in model {
      slf[var] = val.cast(info[var].typ) ? ;
    }
    Ok(slf)
  }

  /// Evaluates some arguments and yields the resulting `VarMap`.
  pub fn apply_to(
    & self, args: & VarMap<::term::Term>
  ) -> ::errors::Res<Self> {
    let mut res = Self::with_capacity( args.len() ) ;
    for arg in args {
      res.push( arg.eval(self) ? )
    }
    Ok(res)
  }
}




/// Factory for hash consed arguments.
pub type ArgFactory = Arc< RwLock<HashConsign<RArgs>> > ;
/// Creates an argument factory.
pub fn new_factory() -> ArgFactory {
  Arc::new(
    RwLock::new(
      HashConsign::with_capacity(211)
    )
  )
}



/// Hash consed arguments.
pub type Args = HConsed<RArgs> ;

/// A set of hashconsed arguments.
// #[derive(Debug, Clone)]
pub type ArgsSet = HConSet<Args> ;
//   /// Set of arguments.
//   set: HConSet<Args>,
// }
// impl ::std::ops::Deref for ArgsSet {
//   type Target = HConSet<Args> ;
//   fn deref(& self) -> & HConSet<Args> {
//     & self.set
//   }
// }
// impl ::std::ops::DerefMut for ArgsSet {
//   fn deref_mut(& mut self) -> & mut HConSet<Args> {
//     & mut self.set
//   }
// }
// impl ArgsSet {
//   /// Constructor.
//   pub fn new() -> Self {
//     ArgsSet { set: HConSet::new() }
//   }
//   /// Constructor with a capacity.
//   pub fn with_capacity(capa: usize) -> Self {
//     ArgsSet { set: HConSet::with_capacity(capa) }
//   }
// }

/// A map from hashconsed arguments to something.
pub type ArgsMap<T> = HConMap<Args, T> ;



/// Helper functions for `Args`.
pub trait SubsumeExt {
  /// Type of the sets we want to check for subsumption.
  type Set ;

  /// Compares two arguments w.r.t. subsumption.
  ///
  /// Returns
  ///
  /// - `Some(Greater)` if `self` subsumes `other`,
  /// - `Some(Equal)` if `self` is equal to `other`,
  /// - `Some(Less)` if `other` subsumes `self`,
  /// - `None` if `self` and `other` cannot be compared.
  ///
  /// Returns an error if `self` and `other` do not have the same length.
  fn compare(& self, other: & Self) -> Option<Ordering> ;

  /// True iff `self` subsumes or is equal to `other`.
  fn subsumes(& self, other: & Self) -> bool {
    match self.compare(other) {
      Some(Ordering::Greater) | Some(Ordering::Equal) => true,
      _ => false,
    }
  }
  /// True iff `other` subsumes or is equal to `self`.
  fn subsumed(& self, other: & Self) -> bool {
    other.subsumes(self)
  }

  /// Checks whether `self` is subsumed by anything in the set.
  ///
  /// Returns `(b, n)`:
  ///
  /// - `b` indicates whether `self` is subsumed
  /// - `n` is the number of elements removed because they were subsumed
  ///   by `self`
  ///
  /// Generally speaking, it is expected that `n > 0 => ! b`. In particular, if
  /// `self` is in the set the expected output is `(true, 0)`.
  fn set_subsumed_rm(& self, set: & mut Self::Set) -> (bool, usize) ;

  /// Checks whether `self` is subsumed by anything in the set.
  ///
  /// Same as `set_subsumed_rm`, but does remove anything.
  fn set_subsumed(& self, set: & Self::Set) -> bool ;
}
impl SubsumeExt for Args {
  type Set = ArgsSet ;
  fn compare(& self, other: & Self) -> Option<Ordering> {
    debug_assert_eq! { self.len(), other.len() }

    if self == other { return Some(Ordering::Equal) }

    if ! conf.teacher.partial {
      None
    } else {

      let (mut less, mut greater) = (true, true) ;

      for (val, other_val) in self.iter().zip( other.iter() ) {
        greater = greater && (
          ! val.is_known() || val == other_val
        ) ;
        less = less && (
          ! other_val.is_known() || val == other_val
        ) ;
      }

      match (less, greater) {
        (false, false) => None,
        (true, false) => Some(Ordering::Less),
        (false, true) => Some(Ordering::Greater),
        (true, true) => fail_with!(
          "Fatal error in sample hashconsing"
        ),
      }

    }
  }

  fn set_subsumed(& self, set: & Self::Set) -> bool {
    if ! conf.teacher.partial {
      set.contains(self)
    } else {
      for elem in set.iter() {
        if elem.subsumes(self) {
          return true
        }
      }
      false
    }
  }

  fn set_subsumed_rm(
    & self, set: & mut ArgsSet
  ) -> (bool, usize) {
    if ! conf.teacher.partial {
      (set.contains(self), 0)
    } else if ! self.is_partial() {
      for elem in set.iter() {
        if elem.subsumes(self) {
          return { (true, 0) }
        }
      }
      (false, 0)
    } else {
      let mut subsumed = false ;
      let mut count = 0 ;
      set.retain(
        |other| match self.compare(other) {
          Some(Ordering::Equal) => {
            subsumed = true ;
            true
          },
          Some(Ordering::Greater) => {
            count += 1 ;
            false
          },
          Some(Ordering::Less) => {
            subsumed = true ;
            true
          },
          None => true,
        }
      ) ;
      (subsumed, count)
    }
  }
}