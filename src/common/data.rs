#![doc = "Learning data-related types."]

use std::sync::RwLock ;

use hashconsing::{ HConser, HConsed, HashConsign } ;

use common::* ;
use instance::Instance ;
use instance::info::* ;

use learning::ice::CData ;



/// Hash consed samples.
pub type HSample = HConsed< Args > ;


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
  pub fn mk(pred: PrdIdx, args: HSample) -> Self {
    Sample { pred, args }
  }

  /// Tests if a sample is about some predicate and its arguments belong
  /// to a set.
  pub fn is_in(& self, pred: PrdIdx, samples: & HConSet<Args>) -> bool {
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
    for arg in & * self.args {
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



wrap_usize!{
  #[doc = "Constraint index."]
  CstrIdx
  #[doc = "Constraint set."]
  set: CstrSet
  #[doc = "Constraint total map."]
  map: CstrMap with iter: CstrMapIter
}


/// Constraints using hashconsed samples.
///
/// A constraint is a tautology iff `lhs.is_empty()` and `rhs.is_none()`.
///
/// # Invariants
///
/// - `lhs.is_empty() => rhs.is_none()`
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Constraint {
  pub lhs: Vec< Sample >,
  pub rhs: Option< Sample >,
}
impl Constraint {
  /// Transforms a constraint in a tautology. Returns all the samples from the
  /// constraint.
  pub fn tautologize(& mut self) -> Vec<Sample> {
    let mut res = Vec::with_capacity(0) ;
    ::std::mem::swap(& mut res, & mut self.lhs) ;
    let mut rhs = None ;
    ::std::mem::swap(& mut rhs, & mut self.rhs) ;
    if let Some(sample) = rhs {
      res.push(sample)
    }
    res
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
    for lhs in & self.lhs {
      lhs.pebcak_io_fmt(w, map) ? ;
      write!(w, " ") ?
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
    for lhs in & self.lhs {
      write!(fmt, "{} ", lhs) ?
    }
    write!(fmt, "=> ") ? ;
    if let Some(ref rhs) = self.rhs {
      write!(fmt, "{}", rhs)
    } else {
      write!(fmt, "false")
    }
  }
}



/// Structure storing unprojected learning data.
///
/// Used by the teacher to simplify constraints as it hads samples.
///
/// Also used by the ice learner to propagate the choices it makes.
pub struct NewData {
  /// Instance, only used for printing.
  instance: Arc<Instance>,
  /// Positive examples.
  pos: PrdMap< HConSet<Args> >,
  /// Negative examples.
  neg: PrdMap< HConSet<Args> >,
  /// Constraints.
  constraints: CstrMap<Constraint>,
  ///  Map from samples to contstraints.
  map: PrdMap< HConMap<Args, CstrSet> >,
}
impl NewData {
  /// Constructor.
  pub fn mk(instance: Arc<Instance>) -> Self {
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
    NewData { instance, pos, neg, constraints, map }
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
  pub fn tautologize(& mut self, constraint: CstrIdx) -> Vec<Sample> {
    let samples = self.constraints[constraint].tautologize() ;
    for & Sample { pred, ref args } in & samples {
      let _ = self.map[pred].get_mut(& args).map(
        |set| set.remove(& constraint)
      ) ;
    }
    samples
  }

  /// Adds some positive examples.
  ///
  /// Simplifies constraints containing these samples.
  ///
  /// `modded_constraints` will be updated as follows: a constraint is
  ///
  /// - added to the set when it is modified (but not tautologized)
  /// - removed from the set when it is tautologized
  pub fn add_pos(
    & mut self, mut samples: PrdHMap< HConSet<Args> >,
    modded_constraints: & mut CstrSet
  ) -> Res<()> {
    // Stack of things to propagate.
    let mut to_propagate = Vec::with_capacity( samples.len() ) ;
    // The stack is updated here and at the end of the `'propagate` loop below.
    // Be careful when using `continue 'propagate` as this will skip the stack
    // update.
    for (pred, set) in samples.drain() {
      to_propagate.push( (pred, set) )
    }

    'propagate: while let Some(
      (curr_pred, curr_samples)
    ) = to_propagate.pop() {
      if curr_samples.is_empty() { continue }

      println!(
        "propagating {} samples for predicate {}",
        curr_samples.len(), self.instance[curr_pred]
      ) ;

      // Get the constraints mentioning the positive samples.
      let mut constraints ;
      {
        let mut tmp = None ;
        let mut iter = curr_samples.iter() ;
        // Find the first sample that appears in some constraints.
        'find_first: while let Some(sample) = iter.next() {
          if let Some(cstr_set) = self.map[curr_pred].remove(sample) {
            if ! cstr_set.is_empty() {
              println!(
                "  - sample {} appears in {} constraints",
                sample, cstr_set.len()
              ) ;
              tmp = Some(cstr_set) ;
              break 'find_first
            }
          }
          println!("  - sample {} does not appear in any constraint", sample)
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
              println!(
                "  - sample {} appears in {} constraints",
                sample, cstr_set.len()
              ) ;
              constraints.extend( cstr_set ) ;
              continue 'other_samples
            }
          }
          println!("  - sample {} does not appear in any constraint", sample)
        }
      }

      println!("  working on {} constraints", constraints.len()) ;

      'update_constraints: for c_idx in constraints {

        println!(
          "    looking at {}", self.constraints[c_idx].to_string_info(
            self.instance.preds()
          ) ?
        ) ;
        
        // Is `rhs` true?
        if self.constraints[c_idx].rhs.as_ref().map(
          | sample | sample.is_in(curr_pred, & curr_samples)
        ).unwrap_or(false) {
          println!("    -> rhs is true, tautologizing") ;
          // Tautologize and break links.
          let _ = self.tautologize(c_idx) ;
          let _ = modded_constraints.remove(& c_idx) ;
          // Move on.
          continue 'update_constraints
        }

        // `lhs` simplification.
        let mut count = 0 ;
        while count < self.constraints[c_idx].lhs.len() {
          if self.constraints[c_idx].lhs[count].is_in(
            curr_pred, & curr_samples
          ) {
            let _ = self.constraints[c_idx].lhs.swap_remove(count) ;
            // No need to break links here as we've already removed all links
            // from `curr_samples` (to get the constraints).
            // DO NOT increment `count` here as we just `swap_remove`d. `count`
            // is already the index of an unvisited element.
            ()
          } else {
            // Unknown, moving on to next sample.
            count += 1
          }
        }
        // Is `lhs` empty?
        if self.constraints[c_idx].lhs.is_empty() {
          println!("    -> lhs is empty, remembering for later") ;
          // Then `rhs` has to be true.
          let mut maybe_rhs = self.tautologize(c_idx) ;
          let _ = modded_constraints.remove(& c_idx) ;
          if let Some( Sample { pred, args } ) = maybe_rhs.pop() {
            // `maybe_rhs` can only be empty now, we've removed the whole
            // `lhs`.
            debug_assert!( maybe_rhs.is_empty() ) ;
            // Remember the sample has to be true.
            let _ = samples.entry(pred).or_insert_with(
              || HConSet::with_capacity(11)
            ).insert(args) ;
          } else {
            // No `rhs`, we have `true => false`, contradiction.
            bail!("contradiction detected, inference impossible")
          }
        } else {
          // `lhs` has changed, remember that for unit clause propagation.
          let _ = modded_constraints.insert(c_idx) ;
        }
      }

      // Done propagating `curr_args` for `curr_pred`, push new positive
      // samples.
      for (pred, set) in samples.drain() {
        to_propagate.push( (pred, set) )
      }

    }

    Ok(())
  }

  /// Adds some negative examples.
  ///
  /// Simplifies constraints containing these samples.
  ///
  /// `modded_constraints` will be updated as follows: a constraint is
  ///
  /// - added to the set when it is modified (but not tautologized)
  /// - removed from the set when it is tautologized
  pub fn add_neg(
    & mut self, mut samples: PrdHMap< HConSet<Args> >,
    modded_constraints: & mut CstrSet
  ) -> Res<()> {
    // Stack of things to propagate.
    let mut to_propagate = Vec::with_capacity( samples.len() ) ;
    // The stack is updated here and at the end of the `'propagate` loop below.
    // Be careful when using `continue 'propagate` as this will skip the stack
    // update.
    for (pred, set) in samples.drain() {
      to_propagate.push( (pred, set) )
    }

    'propagate: while let Some(
      (curr_pred, curr_samples)
    ) = to_propagate.pop() {
      if curr_samples.is_empty() { continue }

      println!(
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
              println!(
                "  - sample {} appears in {} constraints",
                sample, cstr_set.len()
              ) ;
              tmp = Some(cstr_set) ;
              break 'find_first
            }
          }
          println!("  - sample {} does not appear in any constraint", sample)
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
              println!(
                "  - sample {} appears in {} constraints",
                sample, cstr_set.len()
              ) ;
              constraints.extend( cstr_set ) ;
              continue 'other_samples
            }
          }
          println!("  - sample {} does not appear in any constraint", sample)
        }
      }

      println!("  working on {} constraints", constraints.len()) ;

      'update_constraints: for c_idx in constraints {

        println!(
          "    looking at {}", self.constraints[c_idx].to_string_info(
            self.instance.preds()
          ) ?
        ) ;
        
        // Is `rhs` false?
        if self.constraints[c_idx].rhs.as_ref().map(
          | sample | sample.is_in(curr_pred, & curr_samples)
        ).unwrap_or(false) {
          println!("    -> rhs is false, constraint is negative") ;
          // Forget rhs.
          self.constraints[c_idx].rhs = None
        }

        // `lhs` inspection.
        let mut trivial = false ;
        for sample in & self.constraints[c_idx].lhs {
          if sample.is_in(curr_pred, & curr_samples) {
            // This sample is false, the constraint is trivially true.
            trivial = true ;
            break
          }
        }
        // Is constraint trivial?
        if trivial {
          println!("    -> lhs is always false, constraint is trivial") ;
          let _ = self.tautologize(c_idx) ;
        } else if self.constraints[c_idx].lhs.len() == 1
        && self.constraints[c_idx].rhs.is_none() {
          println!(
            "    -> one sample in lhs of negative constraint, remembering"
          ) ;
          // Constraint is negative and only one sample in lhs, it has to be
          // false.
          let mut just_one = self.tautologize(c_idx) ;
          if let Some( Sample {pred, args } ) = just_one.pop() {
            debug_assert!( just_one.is_empty() ) ;
            let _ = samples.entry(pred).or_insert_with(
              || HConSet::with_capacity(11)
            ).insert(args) ;
          } else {
            unreachable!()
          }
        } else {
          // Constraint has changed, remember that for unit clause propagation.
          let _ = modded_constraints.insert(c_idx) ;
        }
      }

      // Done propagating `curr_args` for `curr_pred`, push new negative
      // samples.
      for (pred, set) in samples.drain() {
        to_propagate.push( (pred, set) )
      }

    }

    Ok(())
  }

  /// Adds a constraint. Propagates positive and negative samples.
  pub fn add_cstr(
    & self,
    lhs: Vec<(PrdIdx, Args)>, rhs: Option< (PrdIdx, Args) >
  ) -> Res< Option< Either<Constraint, (Sample, bool)> > > {
    let mut nu_lhs = Vec::with_capacity( lhs.len() ) ;
    'smpl_iter: for (pred, args) in lhs {
      let (args, is_new) = self.samples.mk_is_new(args) ;
      if ! is_new {
        if self.pos[pred].read().map_err(corrupted_err)?.contains(& args) {
          // Sample known to be positive, ignore.
          continue 'smpl_iter
        } else if self.neg[pred].read().map_err(
          corrupted_err
        )?.contains(& args) {
          // Sample known to be negative, constraint is a tautology.
          return Ok(None)
        }
      }
      // Neither pos or neg, memorizing.
      nu_lhs.push( Sample { pred, args } )
    }
    let nu_rhs = if let Some( (pred, args) ) = rhs {
      let (args, is_new) = self.samples.mk_is_new(args) ;
      if ! is_new {
        if self.pos[pred].read().map_err(corrupted_err)?.contains(& args) {
          // Sample known to be positive, constraint's a tautology.
          return Ok(None)
        } else if self.neg[pred].read().map_err(
          corrupted_err
        )?.contains(& args) {
          // Sample known to be negative, constraint is a negative one.
          None
        } else {
          Some( Sample { pred, args } )
        }
      } else {
        Some( Sample { pred, args } )
      }
    } else { None } ;

    let cstr_index = self.constraints.read().map_err(
      corrupted_err
    )?.next_index() ;

    // Detect unit cases.
    if nu_lhs.is_empty() {
      // unit, rhs has to be true.
      if let Some( Sample { pred, args } ) = nu_rhs {
        return Ok(
          Some(Either::Rgt( (self.add_pos(pred, args.get().clone())?, true) ))
        )
      } else {
        bail!("contradiction detected, inference is impossible")
      }
    } else if nu_lhs.len() == 1 && nu_rhs.is_none() {
      // unit, the single lhs has to be false.
      let Sample { pred, args } = nu_lhs.pop().unwrap() ;
      return Ok(
        Some(Either::Rgt( (self.add_neg(pred, args.get().clone())?, false) ))
      )
    }

    // Update the map from samples to constraints. Better to do that now than
    // above, since there might be further simplifications possible.
    for & Sample { pred, ref args } in & nu_lhs {
      let mut map = self.map[pred].write().map_err(corrupted_err)? ;
      let entry = map.entry(
        args.clone()
      ) ;
      let set = entry.or_insert_with(
        || CstrSet::with_capacity(17)
      ) ;
      let _ = set.insert(cstr_index) ;
    }
    if let Some( & Sample { pred, ref args } ) = nu_rhs.as_ref() {
      let mut map = self.map[pred].write().map_err(corrupted_err)? ;
      let entry = map.entry(
        args.clone()
      ) ;
      let set = entry.or_insert_with(
        || CstrSet::with_capacity(17)
      ) ;
      let _ = set.insert(cstr_index) ;
    }

    let cstr = Constraint { lhs: nu_lhs, rhs: nu_rhs } ;

    self.constraints.write().map_err(corrupted_err)?.push(
      cstr.clone()
    ) ;

    Ok( Some( Either::Lft(cstr) ) )
  }
}




/// Structure storing the (unprojected) learning data.
///
/// # TO DO
///
/// - add stats monitoring simplifications and unit clause propagation
pub struct Data {
  /// Sample hashconsign.
  samples: RwLock< HashConsign<Args> >,
  /// Constraints.
  pub constraints: RwLock< CstrMap<Constraint> >,
  /// Map from samples to constraints.
  pub map: PrdMap< RwLock< HConMap<Args, CstrSet> > >,
  /// Positive examples.
  pub pos: PrdMap< RwLock< HConSet<Args> > >,
  /// Negative examples.
  pub neg: PrdMap< RwLock< HConSet<Args> > >,
}
impl Data {
  /// Constructor.
  pub fn mk(instance: & Instance) -> Self {
    let mut map = PrdMap::with_capacity( instance.preds().len() ) ;
    let mut pos = PrdMap::with_capacity( instance.preds().len() ) ;
    let mut neg = PrdMap::with_capacity( instance.preds().len() ) ;
    for _ in instance.preds() {
      map.push(
        RwLock::new( HConMap::with_capacity(103) )
      ) ;
      pos.push(
        RwLock::new( HConSet::with_capacity(103) )
      ) ;
      neg.push(
        RwLock::new( HConSet::with_capacity(103) )
      ) ;
    }
    Data {
      samples: RwLock::new( HashConsign::with_capacity(1007) ),
      constraints: RwLock::new( CstrMap::with_capacity(703) ),
      map, pos, neg
    }
  }

  /// Performs an action on all samples.
  pub fn samples_fold<T, F>(& self, init: T, f: F) -> Res<T>
  where F: Fn(T, HSample) -> T {
    Ok(
      self.samples.read().map_err(corrupted_err)?.fold(f, init)
    )
  }

  /// The projected data for some predicate.
  pub fn data_of(& self, pred: PrdIdx) -> Res<CData> {
    let unc_set = self.map[pred].read().map_err(corrupted_err) ? ;
    let pos_set = self.pos[pred].read().map_err(corrupted_err) ? ;
    let neg_set = self.neg[pred].read().map_err(corrupted_err) ? ;
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
    Ok( CData { pos, neg, unc } )
  }

  // /// Temporary function adding learning data directly.
  // pub fn add_learning_data(& self, data: & LearningData) -> Res<()> {
  //   for sample in & data.pos {
  //     self.add_pos( sample.pred, sample.args.clone() ) ?
  //   }
  //   for sample in & data.neg {
  //     self.add_neg( sample.pred, sample.args.clone() ) ?
  //   }
  //   for cstr in & data.cstr {
  //     let lhs = cstr.lhs.iter().map(
  //       |sample| (sample.pred, sample.args.clone())
  //     ).collect() ;
  //     let rhs = cstr.rhs.as_ref().map(
  //       |sample| (sample.pred, sample.args.clone())
  //     ) ;
  //     self.add_cstr(lhs, rhs) ?
  //   }
  //   Ok(())
  // }

  /// Removes the links between the samples in the input constraint and the
  /// constraint. Also, tautologizes the constraint.
  pub fn unlink(
    & self, dead_links: Vec<(PrdIdx, HSample, CstrIdx)>
  ) -> Res<()> {
    for (pred, args, cstr) in dead_links {
      let _ = self.map[pred].write().map_err(
        corrupted_err
      )?.get_mut(& args).map(|set| set.remove(& cstr)) ;
    }
    Ok(())
  }

  /// Propagates unit clauses recursively.
  pub fn propagate_unit_clauses(
    & self
  ) -> Res<()> {
    let (mut pos, mut neg) = (None, None) ;
    'fixed_point: loop {
      {
        for cstr in self.constraints.read().map_err(corrupted_err)?.iter() {
          if ! cstr.is_tautology() {
            match (cstr.lhs.len(), cstr.rhs.as_ref()) {
              (0, Some(rhs)) => {
                pos = Some( (rhs.pred, rhs.args.get().clone()) ) ;
                break
              },
              (1, None) => {
                neg = Some( (cstr.lhs[0].pred, cstr.lhs[0].args.get().clone()) ) ;
                break
              },
              _ => (),
            }
          }
        }
      }

      if let Some( (pred, args) ) = pos {
        let _ = self.add_pos(pred, args) ? ;
        pos = None
      } else if let Some( (pred, args) ) = neg {
        let _ = self.add_neg(pred, args) ? ;
        neg = None
      } else {
        break 'fixed_point
      }
    }
    Ok(())

  }

  /// Adds a positive example. Simplifies constraints containing that sample.
  pub fn add_pos(
    & self, pred: PrdIdx, args: Args
  ) -> Res<Sample> {
    let (args, is_new_sample) = self.samples.mk_is_new(args) ;
    let is_new_pos = self.pos[pred].write().map_err(
      corrupted_err
    )?.insert( args.clone() ) ;
    let res = Sample { pred, args: args.clone() } ;

    let mut dead_links = vec![] ;

    // New positive, but not a new sample. Might appear in some constraints.
    if is_new_pos && ! is_new_sample {

      let mut to_propagate = vec![ (pred, args) ] ;

      'propagate: while let Some(
        (curr_pred, curr_args)
      ) = to_propagate.pop() {

        let mut all_constraints = self.map[curr_pred].write().map_err(
          corrupted_err
        ) ? ;

        // Get all constraints that mention the current sample.
        if let Some(constraints) = all_constraints.remove(& curr_args) {
          let mut cstrs = self.constraints.write().map_err(corrupted_err) ? ;

          'cstr_iter: for cstr in constraints {
            // Index of the sample in the lhs of the constraint.
            // None if it's the rhs.
            let maybe_index = match cstrs[cstr].rhs.as_ref() {

              // rhs
              Some(rhs)
              if rhs.pred == curr_pred && rhs.args == curr_args => None,

              // lhs
              _ => {
                let mut cnt = 0 ;
                let mut res = None ;

                'lhs_iter: for & Sample {
                  pred, ref args
                } in & cstrs[cstr].lhs {
                  if pred == curr_pred && curr_args == * args {
                    res = Some(cnt) ;
                    break 'lhs_iter
                  } else {
                    cnt += 1
                  }
                }
                if res.is_none() {
                  // This can happen if a constraint was tautologized when
                  // adding a negative example.
                  continue 'cstr_iter
                } else {
                  res
                }
              },
            } ;

            if let Some(idx) = maybe_index {
              // Current sample appears in lhs.
              let _ = cstrs[cstr].lhs.swap_remove(idx) ;
              dead_links.push( (curr_pred, curr_args.clone(), cstr) ) ;

              // Anything left?
              if cstrs[cstr].lhs.is_empty() {
                // Nothing left, meaning the `lhs` is true. Propagating `rhs`.
                let mut rhs = None ;
                ::std::mem::swap(& mut rhs, & mut cstrs[cstr].rhs) ;
                if let Some( Sample { pred, args } ) = rhs {
                  dead_links.push( (pred, args.clone(), cstr) ) ;
                  // Constraint is unit, propagating.
                  debug_assert!( cstrs[cstr].is_tautology() ) ;
                  self.pos[pred].write().map_err(
                    corrupted_err
                  )?.insert( args.clone() ) ;
                  to_propagate.push( (pred, args) ) ;
                } else {
                  bail!("contradiction detected, inference is impossible")
                }
              } else {
                // Constraint's not unit, done.
              }
            } else {
              // Current positive sample is rhs, clause is a tautology.
              let samples = cstrs[cstr].tautologize() ;
              for Sample { pred, args } in samples {
                dead_links.push( (pred, args, cstr) )
              }
            }
          }
        }
      }
    }

    self.unlink(dead_links) ? ;

    Ok(res)
  }

  /// Adds a negative example. Simplifies constraints containing that sample.
  pub fn add_neg(
    & self, pred: PrdIdx, args: Args
  ) -> Res<Sample> {
    let (args, is_new_sample) = self.samples.mk_is_new(args) ;
    let is_new_neg = self.neg[pred].write().map_err(
      corrupted_err
    )?.insert( args.clone() ) ;
    let res = Sample { pred, args: args.clone() } ;

    let mut dead_links = vec![] ;

    // New negative, but not a new sample. Might appear in some constraints.
    if is_new_neg && ! is_new_sample {

      let mut to_propagate = vec![ (pred, args) ] ;

      'propagate: while let Some(
        (curr_pred, curr_args)
      ) = to_propagate.pop() {

      // let (mut curr_pred, mut curr_args) = (pred, args) ;

      // 'propagate: loop {

        let mut all_constraints = self.map[curr_pred].write().map_err(
          corrupted_err
        ) ? ;

        // Get all constraints that mention the current sample.
        if let Some(constraints) = all_constraints.remove(& curr_args) {
          let mut cstrs = self.constraints.write().map_err(corrupted_err) ? ;

          'cstr_iter: for cstr in constraints {
            // Index of the sample in the lhs of the constraint.
            // None if it's the rhs.
            let maybe_index = match cstrs[cstr].rhs.as_ref() {

              // rhs
              Some(rhs)
              if rhs.pred == curr_pred && rhs.args == curr_args => None,

              // lhs
              _ => {
                let mut cnt = 0 ;
                let mut res = None ;

                'lhs_iter: for & Sample {
                  pred, ref args
                } in & cstrs[cstr].lhs {
                  if pred == curr_pred && curr_args == * args {
                    res = Some(cnt) ;
                    break 'lhs_iter
                  } else {
                    cnt += 1
                  }
                }
                if res.is_none() {
                  // This can happen if a constraint was tautologized when
                  // adding a positive or negative sample.
                  continue 'cstr_iter
                } else {
                  res
                }
              },
            } ;

            if maybe_index.is_some() {
              // Current sample appears in lhs, constraint's a tautology.
              let samples = cstrs[cstr].tautologize() ;
              for Sample { pred, args } in samples {
                dead_links.push( (pred, args, cstr) )
              }
            } else {
              // Current sample appears in rhs, constraint's negative.
              cstrs[cstr].rhs = None ;
              dead_links.push( (curr_pred, curr_args.clone(), cstr) ) ;
              if cstrs[cstr].lhs.len() == 1 {
                // Only one sample in lhs, has to be negative, propagating.
                let Sample { pred, args } = cstrs[cstr].lhs.pop().unwrap() ;
                dead_links.push( (pred, args.clone(), cstr) ) ;
                debug_assert!( cstrs[cstr].is_tautology() ) ;
                self.neg[pred].write().map_err(
                  corrupted_err
                )?.insert( args.clone() ) ;
                to_propagate.push( (pred, args) ) ;
              }
            }
          }
        } else {
          // No constraint mentions current sample.
        }
      }
    }

    self.unlink(dead_links) ? ;

    Ok(res)
  }

  /// Adds a constraint. Propagates positive and negative samples.
  pub fn add_cstr(
    & self,
    lhs: Vec<(PrdIdx, Args)>, rhs: Option< (PrdIdx, Args) >
  ) -> Res< Option< Either<Constraint, (Sample, bool)> > > {
    let mut nu_lhs = Vec::with_capacity( lhs.len() ) ;
    'smpl_iter: for (pred, args) in lhs {
      let (args, is_new) = self.samples.mk_is_new(args) ;
      if ! is_new {
        if self.pos[pred].read().map_err(corrupted_err)?.contains(& args) {
          // Sample known to be positive, ignore.
          continue 'smpl_iter
        } else if self.neg[pred].read().map_err(
          corrupted_err
        )?.contains(& args) {
          // Sample known to be negative, constraint is a tautology.
          return Ok(None)
        }
      }
      // Neither pos or neg, memorizing.
      nu_lhs.push( Sample { pred, args } )
    }
    let nu_rhs = if let Some( (pred, args) ) = rhs {
      let (args, is_new) = self.samples.mk_is_new(args) ;
      if ! is_new {
        if self.pos[pred].read().map_err(corrupted_err)?.contains(& args) {
          // Sample known to be positive, constraint's a tautology.
          return Ok(None)
        } else if self.neg[pred].read().map_err(
          corrupted_err
        )?.contains(& args) {
          // Sample known to be negative, constraint is a negative one.
          None
        } else {
          Some( Sample { pred, args } )
        }
      } else {
        Some( Sample { pred, args } )
      }
    } else { None } ;

    let cstr_index = self.constraints.read().map_err(
      corrupted_err
    )?.next_index() ;

    // Detect unit cases.
    if nu_lhs.is_empty() {
      // unit, rhs has to be true.
      if let Some( Sample { pred, args } ) = nu_rhs {
        return Ok(
          Some(Either::Rgt( (self.add_pos(pred, args.get().clone())?, true) ))
        )
      } else {
        bail!("contradiction detected, inference is impossible")
      }
    } else if nu_lhs.len() == 1 && nu_rhs.is_none() {
      // unit, the single lhs has to be false.
      let Sample { pred, args } = nu_lhs.pop().unwrap() ;
      return Ok(
        Some(Either::Rgt( (self.add_neg(pred, args.get().clone())?, false) ))
      )
    }

    // Update the map from samples to constraints. Better to do that now than
    // above, since there might be further simplifications possible.
    for & Sample { pred, ref args } in & nu_lhs {
      let mut map = self.map[pred].write().map_err(corrupted_err)? ;
      let entry = map.entry(
        args.clone()
      ) ;
      let set = entry.or_insert_with(
        || CstrSet::with_capacity(17)
      ) ;
      let _ = set.insert(cstr_index) ;
    }
    if let Some( & Sample { pred, ref args } ) = nu_rhs.as_ref() {
      let mut map = self.map[pred].write().map_err(corrupted_err)? ;
      let entry = map.entry(
        args.clone()
      ) ;
      let set = entry.or_insert_with(
        || CstrSet::with_capacity(17)
      ) ;
      let _ = set.insert(cstr_index) ;
    }

    let cstr = Constraint { lhs: nu_lhs, rhs: nu_rhs } ;

    self.constraints.write().map_err(corrupted_err)?.push(
      cstr.clone()
    ) ;

    Ok( Some( Either::Lft(cstr) ) )
  }

  /// Uses the classification info to classify some ICE data.
  pub fn apply(
    & self, pred: PrdIdx, data: & mut CData
  ) -> Res<()> {
    let pos = self.pos[pred].read().map_err(corrupted_err)? ;
    let neg = self.neg[pred].read().map_err(corrupted_err)? ;
    let mut cursor = 0 ;
    while cursor < data.unc.len() {
      if pos.contains(& data.unc[cursor]) {
        let sample = data.unc.swap_remove(cursor) ;
        data.pos.push(sample)
      } else if neg.contains(& data.unc[cursor]) {
        let sample = data.unc.swap_remove(cursor) ;
        data.neg.push(sample)
      } else {
        cursor += 1
      }
    }
    Ok(())
  }

}

impl<'a> PebcakFmt<'a> for Data {
  type Info = & 'a PrdMap<PrdInfo> ;
  fn pebcak_err(& self) -> ErrorKind {
    "during data pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, map: & 'a PrdMap<PrdInfo>
  ) -> IoRes<()> {
    write!(w, "pos (") ? ;
    for (pred, set) in self.pos.index_iter() {
      for args in set.read().unwrap().iter() {
        write!(w, "\n  ({}", map[pred]) ? ;
        for arg in args.iter() {
          write!(w, " {}", arg)?
        }
        write!(w, ")") ?
      }
    }
    write!(w, "\n) neg (") ? ;
    for (pred, set) in self.neg.index_iter() {
      for args in set.read().unwrap().iter() {
        write!(w, "\n  ({}", map[pred]) ? ;
        for arg in args.iter() {
          write!(w, " {}", arg)?
        }
        write!(w, ")") ?
      }
    }
    write!(w, "\n) constraints (") ? ;
    for (index, cstr) in self.constraints.read().unwrap().index_iter() {
      write!(w, "\n  {: >3} | ", index) ? ;
      if cstr.is_tautology() {
        write!(w, "_") ?
      } else {
        for & Sample { pred, ref args } in cstr.lhs.iter() {
          write!(w, "({}", map[pred]) ? ;
          for arg in args.iter() {
            write!(w, " {}", arg) ?
          }
          write!(w, ") ") ?
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
      for (sample, set) in samples.read().unwrap().iter() {
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
    writeln!(w, "\n)")
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
  pub fn mk(
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


