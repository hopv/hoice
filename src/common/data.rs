//! Learning-data-related types.
//!
//! The types in this module mostly concern the [`Teacher`][teacher].
//!
//! [teacher]: ../../teacher/struct.Teacher.html
//! (Teacher struct)

use std::sync::RwLock ;
use std::cmp::Ordering ;

use hashconsing::{ HConser, HConsed, HashConsign } ;

use common::* ;
use instance::Instance ;
use instance::info::* ;

use learning::ice::data::CData ;



/// Hash consed samples.
pub type HSample = HConsed<Args> ;
/// Helper functions for `HSample`.
pub trait HSampleExt {
  /// Compares two samples w.r.t. subsumption.
  ///
  /// Returns
  ///
  /// - `Some(Greater)` if `self` subsumes `other`,
  /// - `Some(Equal)` if `self` is equal to `other`,
  /// - `Some(Less)` if `other` subsumes `self`,
  /// - `None` if `self` and `other` cannot be compared.
  ///
  /// Returns an error if `self` and `other` do not have the same length.
  fn compare(& self, other: & Self) -> Res< Option<Ordering> > ;

  /// True iff `self` subsumes or is equal to `other`.
  fn subsumes(& self, other: & Self) -> Res<bool> {
    Ok(
      match self.compare(other) ? {
        Some(Ordering::Greater) | Some(Ordering::Equal) => true,
        _ => false,
      }
    )
  }
  /// True iff `other` subsumes or is equal to `self`.
  fn subsumed_by(& self, other: & Self) -> Res<bool> {
    other.subsumes(self)
  }
}
impl HSampleExt for HSample {
  fn compare(& self, other: & Self) -> Res< Option<Ordering> > {
    if_debug! {
      if self.len() != other.len() {
        bail!("attempting to compare two hsamples of different length")
      }
    }

    if self == other { return Ok( Some(Ordering::Equal) ) }

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
      (false, false) => Ok(None),
      (true, false) => Ok( Some(Ordering::Less) ),
      (false, true) => Ok( Some(Ordering::Greater) ),
      (true, true) => bail!(
        "problem in hsample hconsing..."
      ),
    }
  }
}

/// Consign for hash consed samples.
pub type HSampleConsign = Arc< RwLock<HashConsign<Args>> > ;

/// Vector of samples.
pub type HSamples = Vec<HSample> ;


/// A sample is some values for a predicate.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Sample {
  pub pred: PrdIdx,
  pub args: HSample,
}
impl Sample {
  /// Constructor.
  pub fn new(pred: PrdIdx, args: HSample) -> Self {
    Sample { pred, args }
  }

  /// Tests if a sample is about some predicate and its arguments belong
  /// to a set.
  pub fn is_in(& self, pred: PrdIdx, samples: & HConSet<HSample>) -> bool {
    self.pred == pred && samples.contains(& self.args)
  }
}
impl<'a> PebcakFmt<'a> for Sample {
  type Info = & 'a PrdMap<PrdInfo> ;
  fn pebcak_err(& self) -> ErrorKind {
    "during sample pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, map: & 'a PrdMap<PrdInfo>
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


/// Constraints using hashconsed samples.
///
/// A constraint is a tautology iff `lhs.is_empty()` and `rhs.is_none()`.
///
/// # Invariants
///
/// - `lhs.is_empty() => rhs.is_none()`
#[derive(Clone, Debug)]
pub struct Constraint {
  /// Left-hand side.
  pub lhs: PrdHMap< HConSet<HSample> >,
  /// Right-hand side.
  pub rhs: Option< Sample >,
}
macro_rules! constraint_map {
  ($cstr:expr => |$pred:ident, $sample:ident| $body:expr) => (
    for (pred, samples) in & $cstr.lhs {
      let $pred = * pred ;
      for $sample in samples { $body }
    }
    if let Some(
      Sample { pred: $pred, args: ref $sample }
    ) = $cstr.rhs {
      $body
    }
  ) ;
}
impl PartialOrd for Constraint {
  /// Constraint comparison.
  ///
  /// Constraint `c_1` is less than `c_2` if
  ///
  /// - `c_1.rhs == c_2.rhs`
  /// - `c_1.lhs => c_2.lhs`
  fn partial_cmp(& self, other: & Constraint) -> Option<
    ::std::cmp::Ordering
  > {
    use std::cmp::Ordering ;

    if self.rhs != other.rhs {
      None
    } else {
      let (reversed, c_1, c_2) = match self.lhs_len().cmp(
        & other.lhs_len()
      ) {
        Ordering::Less => (false, self, other),
        Ordering::Equal => if self == other {
          return Some( Ordering::Equal )
        } else {
          return None
        },
        Ordering::Greater => (true, other, self),
      } ;

      for (pred, samples_1) in & c_1.lhs {
        if let Some(samples_2) = c_2.lhs.get(pred) {
          if ! samples_1.is_subset(samples_2) {
            return None
          }
        }
      }

      if reversed {
        Some(Ordering::Greater)
      } else {
        Some(Ordering::Less)
      }
    }
  }
}
impl Eq for Constraint {}
impl PartialEq for Constraint {
  fn eq(& self, other: & Constraint) -> bool {
    if self.lhs.len() == other.lhs.len()
    && self.rhs == other.rhs {
      for (
        (lhs_pred, lhs_samples), (rhs_pred, rhs_samples)
      ) in self.lhs.iter().zip( other.lhs.iter() ) {
        if lhs_pred == rhs_pred
        && lhs_samples.len() == rhs_samples.len() {
          for (lhs_sample, rhs_sample) in lhs_samples.iter().zip(
            rhs_samples.iter()
          ) {
            if lhs_sample != rhs_sample {
              return false
            }
          }
        } else {
          return false
        }
      }
      true
    } else {
      false
    }
  }
}
impl Constraint {
  /// Constructor.
  pub fn new(
    lhs: PrdHMap< HConSet<HSample> >, rhs: Option<Sample>
  ) -> Constraint {
    Constraint { lhs, rhs }
  }

  /// Number of samples in the lhs.
  pub fn lhs_len(& self) -> usize {
    let mut count = 0 ;
    for samples in self.lhs.values() {
      count += samples.len()
    }
    count
  }
  /// Transforms a constraint in a tautology. Returns all the samples from the
  /// constraint.
  pub fn tautologize(& mut self) -> (Vec<Sample>, Option<Sample>) {
    let mut lhs = Vec::with_capacity(0) ;
    for (pred, samples) in self.lhs.drain() {
      for sample in samples {
        lhs.push( Sample::new(pred, sample) )
      }
    }
    let mut rhs = None ;
    ::std::mem::swap(& mut rhs, & mut self.rhs) ;
    (lhs, rhs)
  }

  /// Checks whether the lhs of the constraint is empty.
  pub fn is_tautology(& self) -> bool {
    if self.lhs.is_empty() {
      debug_assert!( self.rhs.is_none() ) ;
      true
    } else {
      false
    }
  }
}
impl<'a> PebcakFmt<'a> for Constraint {
  type Info = & 'a PrdMap<PrdInfo> ;
  fn pebcak_err(& self) -> ErrorKind {
    "during constraint pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, map: & 'a PrdMap<PrdInfo>
  ) -> IoRes<()> {
    for (pred, samples) in & self.lhs {
      for sample in samples {
        write!(w, "({} {}) ", map[* pred], sample) ?
      }
    }
    write!(w, "=> ") ? ;
    if let Some(ref rhs) = self.rhs {
      rhs.pebcak_io_fmt(w, map)
    } else {
      write!(w, "false")
    }
  }
}
impl_fmt!{
  Constraint(self, fmt) {
    for (pred, samples) in & self.lhs {
      for sample in samples {
        write!(fmt, "(p_{} {}) ", pred, sample) ?
      }
    }
    write!(fmt, "=> ") ? ;
    if let Some(ref rhs) = self.rhs {
      write!(fmt, "{}", rhs)
    } else {
      write!(fmt, "false")
    }
  }
}


/// Structure manipulating unprojected learning data.
///
/// Cannot create new samples as it does not contain the factory. This is the
/// structure manipulated by learners.
#[derive(Clone)]
pub struct DataCore {
  /// Instance, only used for printing.
  pub instance: Arc<Instance>,
  /// Positive examples.
  pub pos: PrdMap< HConSet<HSample> >,
  /// Negative examples.
  pub neg: PrdMap< HConSet<HSample> >,
  /// Constraints.
  pub constraints: CstrMap<Constraint>,
  ///  Map from samples to contstraints.
  pub map: PrdMap< HConMap<HSample, CstrSet> >,

  /// Positive examples to add (used by propagation).
  pos_to_add: PrdHMap< HConSet<HSample> >,
  /// Negative examples to add (used by propagation).
  neg_to_add: PrdHMap< HConSet<HSample> >,
  /// Constraints that have changed since the last reset.
  modded_constraints: CstrSet,
}
impl DataCore {

  /// Constructor.
  pub fn new(instance: Arc<Instance>) -> Self {
    let pred_count = instance.preds().len() ;
    let (
      mut map, mut pos, mut neg
    ) = (
      PrdMap::with_capacity(pred_count),
      PrdMap::with_capacity(pred_count),
      PrdMap::with_capacity(pred_count)
    ) ;
    for _ in instance.preds() {
      map.push( HConMap::with_capacity(103) ) ;
      pos.push( HConSet::with_capacity(103) ) ;
      neg.push( HConSet::with_capacity(103) ) ;
    }
    let constraints = CstrMap::with_capacity(103) ;
    DataCore {
      instance, pos, neg, constraints, map,
      pos_to_add: PrdHMap::with_capacity(pred_count),
      neg_to_add: PrdHMap::with_capacity(pred_count),
      modded_constraints: CstrSet::new(),
    }
  }

  /// Number of positive/negative samples.
  pub fn pos_neg_count(& self) -> (usize, usize) {
    let (mut pos, mut neg) = (0, 0) ;
    for samples in & self.pos {
      pos += samples.len()
    }
    for samples in & self.neg {
      neg += samples.len()
    }
    (pos, neg)
  }

  /// Shrinks the list of constraints.
  ///
  /// - pops all trailing empty constraints from [`self.constraints`][cstrs].
  ///
  /// Called at the end of [`propagate`][prop].
  ///
  /// [cstrs]: #structfield.constraints (constraints field)
  /// [prop]: #method.propagate (propagate function)
  pub fn shrink_constraints(& mut self) {
    loop {
      scoped! {
        if let Some(last) = self.constraints.last() {
          if ! last.is_tautology() {
            return ()
          }
        } else {
          return ()
        }
      }
      let last = self.constraints.pop() ;
      debug_assert_eq!(
        last.map(|c| c.is_tautology()), Some(true)
      )
    }
  }

  /// Checks the state of the data. Does nothing in release.
  ///
  /// - no positive / negative data is linked to some constraints
  /// - `(pred, sample, constraint)` in [`self.map`][map] implies `(pred
  ///   sample)` in [`self.constraints`][cstrs]`[constraint]`'s lhs or rhs
  /// - and conversely
  ///
  /// [map]: #structfield.map (map field)
  /// [cstrs]: #structfield.constraints (constraints field)
  #[cfg(debug_assertions)]
  pub fn check(& self) -> Res<()> {
    if ! self.pos_to_add.is_empty() {
      bail!("pos_to_add is not empty...")
    }
    if ! self.neg_to_add.is_empty() {
      bail!("neg_to_add is not empty...")
    }

    // Pos/neg data cannot appear in constraints.
    for pred in self.instance.pred_indices() {
      let pos = self.pos[pred].iter().map(
        |p| (p, "positive")
      ) ;
      let neg = self.neg[pred].iter().map(
        |n| (n, "negative")
      ) ;
      for (sample, polarity) in pos.chain(neg) {
        if let Some(set) = self.map[pred].get(sample) {
          let mut s: String = "{".into() ;
          for idx in set {
            s.push_str(& format!(" {}", idx))
          }
          s.push_str(" }") ;
          bail!(
            "{}\n({} {}) is {} but appears in constraint(s) {}",
            self.string_do(& (), |s| s.to_string()).unwrap(),
            self.instance[pred], sample, polarity, s
          )
        }
      }
    }

    // Constraints are consistent with map.
    for (idx, constraint) in self.constraints.index_iter() {
      constraint_map!{
        constraint => |prd, sample| {
          if ! self.map[prd].get(sample).map(
            |set| set.contains(& idx)
          ).unwrap_or(false) {
            bail!(
              "{}\n({} {}) appears in constraint #{} \
              but is not registered in map",
              self.string_do(& (), |s| s.to_string()).unwrap(),
              self.instance[prd], sample, idx
            )
          }
        }
      }
    }

    // Map is consistent with constraints.
    for (pred, map) in self.map.index_iter() {
      for (sample, set) in map {
        for idx in set {
          let c = & self.constraints[* idx] ;
          let mut okay = false ;
          constraint_map! {
            c => |p, s| if p == pred && s == sample {
              okay = true
            }
          }
          if ! okay {
            bail!(
              "{}\n({} {}) registered in map for constraint #{} \
              but does not appear in this constraint",
              self.string_do(& (), |s| s.to_string()).unwrap(),
              self.instance[pred], sample, idx
            )
          }
        }
      }
    }

    Ok(())
  }
  #[cfg(not(debug_assertions))]
  #[inline]
  pub fn check(& self) -> Res<()> { Ok(()) }


  /// Applies the classification represented by the data to some projected
  /// data.
  pub fn classify(& self, pred: PrdIdx, data: & mut CData) {
    let mut index = 0 ;
    while index < data.unc.len() {
      if self.pos[pred].contains(& data.unc[index]) {
        let to_pos = data.unc.swap_remove(index) ;
        data.pos.push(to_pos)
      } else if self.neg[pred].contains(& data.unc[index]) {
        let to_neg = data.unc.swap_remove(index) ;
        data.neg.push(to_neg)
      } else {
        index += 1
      }
    }
  }


  /// Sets all the unknown data of a given predicate to be false, and
  /// propagates.
  pub fn pred_all_false(& mut self, pred: PrdIdx) -> Res<()> {
    {
      let set = self.neg_to_add.entry(pred).or_insert_with(
        || HConSet::new()
      ) ;
      for (sample, _) in & self.map[pred] {
        set.insert( sample.clone() ) ;
      }
    }
    self.propagate()
  }

  /// Sets all the unknown data of a given predicate to be true, and
  /// propagates.
  pub fn pred_all_true(& mut self, pred: PrdIdx) -> Res<()> {
    {
      let set = self.pos_to_add.entry(pred).or_insert_with(
        || HConSet::new()
      ) ;
      for (sample, _) in & self.map[pred] {
        set.insert( sample.clone() ) ;
      }
    }
    self.propagate()
  }

  /// Remember a positive example to add.
  pub fn stage_pos(& mut self, pred: PrdIdx, args: HSample) -> bool {
    self.pos_to_add.entry(pred).or_insert_with(
      || HConSet::with_capacity(11)
    ).insert(args)
  }

  /// Remember a negative example to add.
  pub fn stage_neg(& mut self, pred: PrdIdx, args: HSample) -> bool {
    self.neg_to_add.entry(pred).or_insert_with(
      || HConSet::with_capacity(11)
    ).insert(args)
  }

  /// Diff between two data structures. Returns the new positive, negative,
  /// and implication data respectively.
  ///
  /// Assumes `self` is the "most recent" data.
  ///
  /// **NB**: does not look at the constraints that are not new but may have
  /// been modified.
  ///
  /// Used by the smt learner to know what's new.
  pub fn diff<'a>(& 'a self, other: & 'a Self) -> (
    Vec<& 'a HSample>, Vec<& 'a HSample>, & 'a [Constraint]
  ) {
    let (mut pos, mut neg) = ( Vec::new(), Vec::new() ) ;
    for pred in self.instance.pred_indices() {
      for sample in self.pos[pred].difference( & other.pos[pred] ) {
        pos.push(sample)
      }
      for sample in self.neg[pred].difference( & other.neg[pred] ) {
        neg.push(sample)
      }
    }
    let constraints = & self.constraints[
      other.constraints.len() .. self.constraints.len()
    ] ;
    (pos, neg, constraints)
  }

  /// The projected data for some predicate.
  pub fn data_of(& self, pred: PrdIdx) -> CData {
    let unc_set = & self.map[pred] ;
    let pos_set = & self.pos[pred] ;
    let neg_set = & self.neg[pred] ;
    let (mut pos, mut neg, mut unc) = (
      Vec::with_capacity( pos_set.len() ),
      Vec::with_capacity( neg_set.len() ),
      Vec::with_capacity( unc_set.len() )
    ) ;
    for sample in pos_set.iter() {
      pos.push( sample.clone() )
    }
    for sample in neg_set.iter() {
      neg.push( sample.clone() )
    }
    for (sample, set) in unc_set.iter() {
      if ! set.is_empty() {
        unc.push( sample.clone() )
      }
    }
    CData { pos, neg, unc }
  }

  /// Tautologizes a constraint and removes the links with its samples in
  /// the map.
  pub fn tautologize(
    & mut self, constraint: CstrIdx
  ) -> (Vec<Sample>, Option<Sample>) {
    debug_assert! { constraint < self.constraints.len() }
    constraint_map! {
      self.constraints[constraint] => |prd, sample| {
        let _ = self.map[prd].get_mut(sample).map(
          |set| set.remove(& constraint)
        ) ;
      }
    }
    self.constraints[constraint].tautologize()
  }

  /// Propagates everything it can.
  pub fn propagate(& mut self) -> Res<()> {
    while ! (self.pos_to_add.is_empty() && self.neg_to_add.is_empty()) {
      if ! self.pos_to_add.is_empty() {
        self.add_propagate_pos() ?
      }
      if ! self.neg_to_add.is_empty() {
        self.add_propagate_neg() ?
      }
    }
    self.check() ? ;
    self.shrink_constraints() ;
    Ok(())
  }

  /// Adds some positive examples from `pos_to_add`.
  ///
  /// Simplifies constraints containing these samples.
  ///
  /// `modded_constraints` will be updated as follows: a constraint is
  ///
  /// - added to the set when it is modified (but not tautologized)
  /// - removed from the set when it is tautologized
  fn add_propagate_pos(& mut self) -> Res<()> {
    // Stack of things to propagate.
    let mut to_propagate = Vec::with_capacity( self.pos_to_add.len() ) ;

    // The stack is updated here and at the end of the `'propagate` loop below.
    // Be careful when using `continue 'propagate` as this will skip the stack
    // update.
    for (pred, set) in self.pos_to_add.drain() {
      to_propagate.push( (pred, set) )
    }

    'propagate: while let Some(
      (curr_pred, curr_samples)
    ) = to_propagate.pop() {
      if curr_samples.is_empty() { continue 'propagate }

      log_debug!(
        "propagating {} samples for predicate {}",
        curr_samples.len(), self.instance[curr_pred]
      ) ;

      let mut new_stuff = false ;
      for sample in & curr_samples {
        let is_new = self.pos[curr_pred].insert( sample.clone() ) ;
        new_stuff = new_stuff || is_new
      }
      if ! new_stuff { continue 'propagate }

      // Look for 

      // Get the constraints mentioning the positive samples.
      let mut constraints ;
      {
        let mut tmp = None ;
        let mut iter = curr_samples.iter() ;
        // Find the first sample that appears in some constraints.
        'find_first: while let Some(sample) = iter.next() {
          if let Some(cstr_set) = self.map[curr_pred].remove(sample) {
            if ! cstr_set.is_empty() {
              log_debug!(
                "  - sample {} appears in {} constraints",
                sample, cstr_set.len()
              ) ;
              tmp = Some(cstr_set) ;
              break 'find_first
            }
          }
          log_debug!("  - sample {} does not appear in any constraint", sample)
        }
        if let Some(set) = tmp {
          constraints = set
        } else { // None of the samples appear in any constraint.
          continue 'propagate
        }
        // Iterate over the remaining samples and add to the constraints to
        // check.
        'other_samples: while let Some(sample) = iter.next() {
          if let Some(cstr_set) = self.map[curr_pred].remove(sample) {
            if ! cstr_set.is_empty() {
              use std::iter::Extend ;
              log_debug!(
                "  - sample {} appears in {} constraints",
                sample, cstr_set.len()
              ) ;
              constraints.extend( cstr_set ) ;
              continue 'other_samples
            }
          }
          log_debug!("  - sample {} does not appear in any constraint", sample)
        }
      }

      log_debug!("  working on {} constraints", constraints.len()) ;

      'update_constraints: for c_idx in constraints {

        log_debug!(
          "    looking at {}", self.constraints[c_idx].to_string_info(
            self.instance.preds()
          ) ?
        ) ;
        
        // Is `rhs` true?
        if self.constraints[c_idx].rhs.as_ref().map(
          | sample | sample.is_in(curr_pred, & curr_samples)
        ).unwrap_or(false) {
          log_debug!("    -> rhs is true, tautologizing") ;
          // Tautologize and break links.
          let _ = self.tautologize(c_idx) ;
          let _ = self.modded_constraints.remove(& c_idx) ;
          // Move on.
          continue 'update_constraints
        }

        // `lhs` simplification.
        let mut remove = false ;
        if let Some(set) = self.constraints[c_idx].lhs.get_mut(& curr_pred) {
          set.retain(
            |sample| ! curr_samples.contains(sample)
          ) ;
          remove = set.is_empty()
        }
        if remove {
          let empty = self.constraints[c_idx].lhs.remove(& curr_pred) ;
          debug_assert! { empty.map(|set| set.is_empty()).unwrap_or(false) }
        }

        // Is `lhs` empty?
        if self.constraints[c_idx].lhs.is_empty() {
          log_debug!("    -> lhs is empty, remembering for later") ;
          // Then `rhs` has to be true.
          let (lhs, maybe_rhs) = self.tautologize(c_idx) ;
          debug_assert! { lhs.is_empty() }
          let _ = self.modded_constraints.remove(& c_idx) ;
          if let Some( Sample { pred, args } ) = maybe_rhs {
            // Remember the sample has to be true.
            self.stage_pos(pred, args) ;
          } else {
            // No `rhs`, we have `true => false`, contradiction.
            bail!(ErrorKind::Unsat)
          }
        }

        else

        // Is the constraint negative and the `lhs` has only one element?
        if self.constraints[c_idx].rhs.is_none()
        && self.constraints[c_idx].lhs_len() == 1 {
          // Then tautologize and add as negative example to add.
          let (mut lhs, rhs) = self.tautologize(c_idx) ;
          debug_assert! { rhs.is_none() }
          let _ = self.modded_constraints.remove(& c_idx) ;
          if let Some( Sample { pred, args } ) = lhs.pop() {
            debug_assert!( lhs.is_empty() ) ;
            // Remember the sample has to be false.
            self.stage_neg(pred, args) ;
          } else {
            bail!(
              "[unreachable] just checked lhs's length is 1 but it's empty now"
            )
          }
        }

        else {
          // `lhs` has changed, remember that for unit clause propagation.
          let _ = self.modded_constraints.insert(c_idx) ;
        }
      }

      // Done propagating `curr_args` for `curr_pred`, push new positive
      // samples.
      for (pred, set) in self.pos_to_add.drain() {
        to_propagate.push( (pred, set) )
      }

    }

    Ok(())
  }

  /// Adds some negative examples from `neg_to_add`.
  ///
  /// Simplifies constraints containing these samples.
  ///
  /// `modded_constraints` will be updated as follows: a constraint is
  ///
  /// - added to the set when it is modified (but not tautologized)
  /// - removed from the set when it is tautologized
  fn add_propagate_neg(& mut self) -> Res<()> {
    // Stack of things to propagate.
    let mut to_propagate = Vec::with_capacity( self.neg_to_add.len() ) ;
    // The stack is updated here and at the end of the `'propagate` loop below.
    // Be careful when using `continue 'propagate` as this will skip the stack
    // update.
    for (pred, set) in self.neg_to_add.drain() {
      to_propagate.push( (pred, set) )
    }

    'propagate: while let Some(
      (curr_pred, curr_samples)
    ) = to_propagate.pop() {
      if curr_samples.is_empty() { continue }

      let mut new_stuff = false ;
      for sample in & curr_samples {
        let is_new = self.neg[curr_pred].insert( sample.clone() ) ;
        new_stuff = new_stuff || is_new
      }
      if ! new_stuff { continue 'propagate }

      log_debug!(
        "propagating {} samples for predicate {}",
        curr_samples.len(), self.instance[curr_pred]
      ) ;

      // Get the constraints mentioning the negative samples.
      let mut constraints ;
      {
        let mut tmp = None ;
        let mut iter = curr_samples.iter() ;
        // Find the first sample that appears in some constraints.
        'find_first: while let Some(sample) = iter.next() {
          if let Some(cstr_set) = self.map[curr_pred].remove(sample) {
            if ! cstr_set.is_empty() {
              log_debug!(
                "  - sample {} appears in {} constraints",
                sample, cstr_set.len()
              ) ;
              tmp = Some(cstr_set) ;
              break 'find_first
            }
          }
          log_debug!("  - sample {} does not appear in any constraint", sample)
        }
        if let Some(set) = tmp {
          constraints = set
        } else { // None of the samples appear in any constraint.
          continue 'propagate
        }
        // Iterate over the remaining samples and add to the constraints to
        // check.
        'other_samples: while let Some(sample) = iter.next() {
          if let Some(cstr_set) = self.map[curr_pred].remove(sample) {
            if ! cstr_set.is_empty() {
              use std::iter::Extend ;
              log_debug!(
                "  - sample {} appears in {} constraints",
                sample, cstr_set.len()
              ) ;
              constraints.extend( cstr_set ) ;
              continue 'other_samples
            }
          }
          log_debug!("  - sample {} does not appear in any constraint", sample)
        }
      }

      log_debug!("  working on {} constraints", constraints.len()) ;

      'update_constraints: for c_idx in constraints {

        log_debug!(
          "    looking at {}", self.constraints[c_idx].to_string_info(
            self.instance.preds()
          ) ?
        ) ;
        
        // Is `rhs` false?
        if self.constraints[c_idx].rhs.as_ref().map(
          | sample | sample.is_in(curr_pred, & curr_samples)
        ).unwrap_or(false) {
          log_debug!("    -> rhs is false, constraint is negative") ;
          // Forget rhs.
          self.constraints[c_idx].rhs = None
        }

        // `lhs` inspection.
        let mut trivial = false ;
        for (pred, samples) in & self.constraints[c_idx].lhs {
          if pred == & curr_pred {
            for sample in samples {
              if curr_samples.contains(sample) {
                // This sample is false, the constraint is trivially true.
                trivial = true ;
                break
              }
            }
          }
        }

        // Is constraint trivial?
        if trivial {
          log_debug!("    -> lhs is always false, constraint is trivial") ;
          let _ = self.tautologize(c_idx) ;
        }

        else

        if self.constraints[c_idx].lhs_len() == 1
        && self.constraints[c_idx].rhs.is_none() {
          log_debug!(
            "    -> one sample in lhs of negative constraint, remembering"
          ) ;
          // Constraint is negative and only one sample in lhs, it has to be
          // false.
          let (mut just_one, rhs) = self.tautologize(c_idx) ;
          debug_assert! { rhs.is_none() }
          if let Some( Sample { pred, args } ) = just_one.pop() {
            debug_assert!( just_one.is_empty() ) ;
            self.modded_constraints.remove(& c_idx) ;
            let _ = self.stage_neg(pred, args) ;
          } else {
            unreachable!()
          }
        } else {
          // Constraint has changed, remember that for unit clause propagation.
          let _ = self.modded_constraints.insert(c_idx) ;
        }
      }

      // Done propagating `curr_args` for `curr_pred`, push new negative
      // samples.
      for (pred, set) in self.neg_to_add.drain() {
        to_propagate.push( (pred, set) )
      }

    }

    Ok(())
  }

}

impl<'a> PebcakFmt<'a> for DataCore {
  type Info = & 'a () ;
  fn pebcak_err(& self) -> ErrorKind {
    "during data pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, _: & 'a ()
  ) -> IoRes<()> {
    let map = self.instance.preds() ;
    write!(w, "pos (") ? ;
    for (pred, set) in self.pos.index_iter() {
      for args in set.iter() {
        write!(w, "\n  ({}", map[pred]) ? ;
        for arg in args.iter() {
          write!(w, " {}", arg)?
        }
        write!(w, ")") ?
      }
    }
    write!(w, "\n) neg (") ? ;
    for (pred, set) in self.neg.index_iter() {
      for args in set.iter() {
        write!(w, "\n  ({}", map[pred]) ? ;
        for arg in args.iter() {
          write!(w, " {}", arg)?
        }
        write!(w, ")") ?
      }
    }
    write!(w, "\n) constraints (") ? ;
    for (index, cstr) in self.constraints.index_iter() {
      write!(w, "\n  {: >3} | ", index) ? ;
      if cstr.is_tautology() {
        write!(w, "_") ?
      } else {
        for (pred, samples) in & cstr.lhs {
          for sample in samples {
            write!(w, "({} {}) ", map[* pred], sample) ?
          }
        }
        write!(w, "=> ") ? ;
        if let Some(& Sample { pred, ref args }) = cstr.rhs.as_ref() {
          write!(w, "({}", map[pred]) ? ;
          for arg in args.iter() {
            write!(w, " {}", arg) ?
          }
          write!(w, ")") ?
        } else {
          write!(w, "false") ?
        }
      }
    }
    write!(w, "\n) constraint map(") ? ;
    for (pred, samples) in self.map.index_iter() {
      for (sample, set) in samples.iter() {
        write!(w, "\n  ({}", map[pred]) ? ;
        for arg in sample.iter() {
          write!(w, " {}", arg) ?
        }
        write!(w, ") ->") ? ;
        for pred in set.iter() {
          write!(w, " {}", pred) ?
        }
      }
    }
    write!(w, "\n) positive examples staged (") ? ;
    for (pred, set) in & self.pos_to_add {
      write!(w, "\n  {} |", self.instance[* pred]) ? ;
      for sample in set {
        write!(w, " {}", sample) ?
      }
    }
    write!(w, "\n) negative examples staged (\n") ? ;
    for (pred, set) in & self.neg_to_add {
      write!(w, "  {} |", self.instance[* pred]) ? ;
      for sample in set {
        write!(w, " {}", sample) ?
      }
      write!(w, "\n") ?
    }
    write!(w, ")\n")
  }
}


/// Structure storing unprojected learning data.
///
/// Used by the teacher to simplify constraints as it adds samples. Basically a
/// [`DataCore`][core] and a factory for samples.
///
/// [core]: struct.DataCore.html (DataCore struct)
#[derive(Clone)]
pub struct Data {
  /// Data core.
  core: DataCore,
  /// Consign for hash consed samples.
  samples: HSampleConsign,
}
impl ::std::ops::Deref for Data {
  type Target = DataCore ;
  fn deref(& self) -> & DataCore {
    & self.core
  }
}
impl ::std::ops::DerefMut for Data {
  fn deref_mut(& mut self) -> & mut DataCore {
    & mut self.core
  }
}
impl Data {

  /// Constructor.
  pub fn new(instance: Arc<Instance>) -> Self {
    let samples = Arc::new(
      RwLock::new( HashConsign::with_capacity(1007) )
    ) ;
    Data {
      core: DataCore::new(instance), samples
    }
  }

  /// Clones the data core.
  pub fn clone_core(& self) -> DataCore {
    self.core.clone()
  }

  /// Clones the constraints to create a new `Data`.
  pub fn clone_constraints(& self) -> Option<Data> {
    let mut data = None ;
    for constraint in & self.core.constraints {
      if ! constraint.is_tautology() {
        data.get_or_insert_with(
          || Data {
            core: DataCore::new( self.core.instance.clone() ),
            samples: self.samples.clone()
          }
        ).internal_add_cstr( constraint.clone() ) ;
      }
    }
    data
  }

  /// Merges the positive and negative samples in `other` to `self`.
  ///
  /// Returns the number of new positive/negative examples.
  pub fn merge_samples(& mut self, other: Data) -> Res<(usize, usize)> {
    let (mut pos, mut neg) = (0, 0) ;
    for (pred, samples) in other.core.pos.into_index_iter() {
      for sample in samples {
        if self.stage_pos(pred, sample) {
          pos += 1
        }
      }
    }
    for (pred, samples) in other.core.neg.into_index_iter() {
      for sample in samples {
        if self.stage_neg(pred, sample) {
          neg += 1
        }
      }
    }
    self.propagate() ? ;
    Ok((pos, neg))
  }

  /// Creates a new sample. Returns true if it's new.
  pub fn mk_sample(
    & mut self, args: Args
  ) -> (HSample, bool) {
    let (args, is_new) = self.samples.mk_is_new( args.into() ) ;
    (args, is_new)
  }

  /// Adds a constraint. Does not propagate.
  pub fn add_cstr(
    & mut self, lhs: Vec<(PrdIdx, Args)>, rhs: Option< (PrdIdx, Args) >
  ) -> Res<bool> {
    self.propagate() ? ;

    let mut nu_lhs = PrdHMap::with_capacity( lhs.len() ) ;
    let mut nu_lhs_len = 0 ;

    'smpl_iter: for (pred, args) in lhs {
      let (args, is_new) = self.mk_sample(args) ;
      if ! is_new {
        if self.pos[pred].contains(& args) {
          // Sample known to be positive, ignore.
          continue 'smpl_iter
        } else if self.neg[pred].contains(& args) {
          // Sample known to be negative, constraint is a tautology.
          return Ok(false)
        }
      }

      // Neither pos or neg, memorizing.
      let is_new = nu_lhs.entry(pred).or_insert_with(
        || HConSet::new()
      ).insert(args) ;

      if is_new { nu_lhs_len += 1 }
    }

    let nu_rhs = if let Some( (pred, args) ) = rhs {
      let (args, is_new) = self.mk_sample(args) ;
      if ! is_new {
        if self.pos[pred].contains(& args) {
          // Sample known to be positive, constraint's a tautology.
          return Ok(false)
        } else if self.neg[pred].contains(& args) {
          // Sample known to be negative, constraint is a negative one.
          None
        } else {
          Some( Sample { pred, args } )
        }
      } else {
        Some( Sample { pred, args } )
      }
    } else { None } ;

    // Detect unit cases.
    if nu_lhs.is_empty() {
      // unit, rhs has to be true.
      if let Some( Sample { pred, args } ) = nu_rhs {
        self.stage_pos(pred, args) ;
        self.add_propagate_pos() ? ;
        // Necessarily new, otherwise we would know that the constraint is a
        // tautology.
        return Ok(true)
      } else {
        bail!(ErrorKind::Unsat)
      }
    } else if nu_lhs_len == 1 && nu_rhs.is_none() {
      let mut lhs = nu_lhs.into_iter() ;
      if let Some((pred, samples)) = lhs.next() {
        let mut samples = samples.into_iter() ;
        if let Some(sample) = samples.next() {
          self.stage_neg(pred, sample) ;
          self.add_propagate_neg() ? ;
          // Necessarily new, otherwise we would know that the constraint is a
          // tautology.
          return Ok(true)
        }
      }
      unreachable!()
    }

    let constraint = Constraint::new(nu_lhs, nu_rhs) ;

    log_debug! {
      "adding constraint {}",
      constraint.to_string_info( self.instance.preds() ).unwrap()
    }

    for idx in CstrRange::zero_to( self.constraints.len() ) {
      use std::cmp::Ordering ;
      if self.constraints[idx].is_tautology() {
        continue
      }
      match constraint.partial_cmp(
        & self.constraints[idx]
      ) {
        Some(Ordering::Less) => {
          log_debug! {
            "  subsumes {}",
            self.constraints[idx].to_string_info(
              self.instance.preds()
            ).unwrap()
          }
          let _ = self.tautologize(idx) ;
          ()
        },
        Some(Ordering::Equal) | 
        Some(Ordering::Greater) => {
          log_debug! {
            "  subsumed by {}",
            self.constraints[idx].to_string_info(
              self.instance.preds()
            ).unwrap()
          }
          return Ok(false)
        },
        None => (),
      }
    }
    log_debug! { "  actually adding it" }
    self.shrink_constraints() ;

    self.internal_add_cstr(constraint) ;

    Ok(true)
  }

  /// Adds a constraint.
  ///
  /// Does not check anything, just creates the links and adds the constraint.
  fn internal_add_cstr(& mut self, constraint: Constraint) {
    let cstr_index = self.constraints.next_index() ;

    // Update the map from samples to constraints. Better to do that now than
    // above, since there might be further simplifications possible.
    for (pred, samples) in & constraint.lhs {
      for sample in samples {
        let _ = self.map[* pred].entry( sample.clone() ).or_insert_with(
          || CstrSet::with_capacity(17)
        ).insert(cstr_index) ;
      }
    }
    if let Some( & Sample { pred, ref args } ) = constraint.rhs.as_ref() {
      let _ = self.map[pred].entry( args.clone() ).or_insert_with(
        || CstrSet::with_capacity(17)
      ).insert(cstr_index) ;
    }

    self.constraints.push(constraint)
  }

  /// Adds positive data after hash consing. True if new.
  ///
  /// Stages propagation but does not run it.
  pub fn stage_raw_pos(
    & mut self, pred: PrdIdx, args: Args
  ) -> Res<bool> {
    let (args, is_new) = self.mk_sample(args) ;
    if is_new {
      let is_new = self.pos[pred].insert(args) ;
      debug_assert!( is_new ) ;
      Ok(true)
    } else {
      if ! self.pos[pred].contains(& args) {
        self.stage_pos(pred, args) ;
        Ok(true)
      } else {
        Ok(false)
      }
    }
  }

  /// Adds negative data after hash consing. True if new.
  pub fn stage_raw_neg(
    & mut self, pred: PrdIdx, args: Args
  ) -> Res<bool> {
    let (args, is_new) = self.mk_sample(args) ;
    if is_new {
      let is_new = self.neg[pred].insert(args) ;
      debug_assert!( is_new ) ;
      Ok(true)
    } else {
      if ! self.neg[pred].contains(& args) {
        self.stage_neg(pred, args) ;
        Ok(true)
      } else {
        Ok(false)
      }
    }
  }
}







/// New learning data sent by the teacher to the learners.
#[derive(Clone)]
pub struct LearningData {
  /// Positive learning data.
  pub pos: Vec<Sample>,
  /// Negative learning data.
  pub neg: Vec<Sample>,
  /// Constraints.
  pub cstr: Vec<Constraint>,
}
impl LearningData {
  /// Constructor.
  pub fn new(
    pos: Vec<Sample>, neg: Vec<Sample>, cstr: Vec<Constraint>
  ) -> Self {
    LearningData { pos, neg, cstr }
  }
  /// Returns `true` if everything's empty.
  pub fn is_empty(& self) -> bool {
    self.pos.is_empty() && self.neg.is_empty() && self.cstr.is_empty()
  }
}
impl<'a> PebcakFmt<'a> for LearningData {
  type Info = & 'a PrdMap<PrdInfo> ;
  fn pebcak_err(& self) -> ErrorKind {
    "during constraint pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, map: & 'a PrdMap<PrdInfo>
  ) -> IoRes<()> {
    write!(w, "pos (") ? ;
    if ! self.pos.is_empty() {
      write!(w, "\n ") ? ;
      for pos in & self.pos {
        write!(w, "  ") ? ;
        pos.pebcak_io_fmt(w, map) ? ;
        write!(w, "\n") ?
      }
    }
    write!(w, ") neg (") ? ;
    if ! self.neg.is_empty() {
      write!(w, "\n ") ? ;
      for neg in & self.neg {
        write!(w, "  ") ? ;
        neg.pebcak_io_fmt(w, map) ? ;
        write!(w, "\n") ?
      }
    }
    write!(w, ") constraints (") ? ;
    if ! self.cstr.is_empty() {
      write!(w, "\n ") ? ;
      for cstr in & self.cstr {
        write!(w, "  ") ? ;
        cstr.pebcak_io_fmt(w, map) ? ;
        writeln!(w, "") ?
      }
    }
    writeln!(w, ")")
  }
}


