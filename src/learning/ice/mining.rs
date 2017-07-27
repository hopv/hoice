//! Mines an instance for qualifiers.

use common::* ;
use instance::* ;
use common::data::{ Data, HSample, LearningData, Sample, Constraint } ;


#[doc = r#"Stores the (truth) value of a qualifier on some samples.

In `debug` mode, stores two sets of samples, one for each truth value the
qualifier can take.

In `release` mode, stores only the set of samples on which the qualifier is
true. Any sample not in this set is assumed to make the qualifier evaluate
to false.

This is because in `debug`, we want to check that we're not missing qualifiers.
But not in `release`, where we just want to go fast and save memory.

The two versions must be indistinguishable from the outside."#]
#[cfg( not(release) )]
pub struct QualValues {
  /// Samples on which the qualifier evaluates to true.
  true_set: HConSet<Args>,
  /// Samples on which the qualifier evaluates to false.
  flse_set: HConSet<Args>,
}
#[cfg( not(release) )]
impl QualValues {
  /// Constructor.
  pub fn mk() -> Self {
    QualValues {
      true_set: HConSet::with_capacity(1003),
      flse_set: HConSet::with_capacity(1003),
    }
  }
}
#[cfg( not(release) )]
impl QualValuesExt for QualValues {
  fn add(& mut self, s: HSample, val: bool) {
    let _ = if val {
      self.true_set.insert(s)
    } else { self.flse_set.insert(s) } ;
    ()
  }
  fn eval(& self, s: & HSample) -> bool {
    if self.true_set.contains(s) {
      true
    } else if self.flse_set.contains(s) {
      false
    } else {
      panic!("[bug QualValues] evaluation on unknown sample: {:?}", s.get())
    }
  }
}

#[cfg(release)]
pub struct QualValues {
  /// Samples on which the qualifier evaluates to true.
  true_set: HConSet<Args>,
}
#[cfg(release)]
impl QualValues {
  /// Constructor.
  pub fn mk() -> Self {
    QualValues { true_set: HConSet::with_capacity(1003) }
  }
}
#[cfg(release)]
impl QualValuesExt for QualValues {
  fn add(& mut self, s: HSample, val: bool) {
    let _ = if val { self.true_set.insert(s) } ;
    ()
  }
  fn eval(& self, s: & HSample) -> bool {
    self.true_set.contains(s)
  }
}


/// Trait extending `QualValues` in `release` and `debug`.
pub trait QualValuesExt {
  /// Adds a sample for the qualifier.
  #[inline]
  fn add(& mut self, HSample, bool) ;
  /// Checks whether the qualifier evaluates to false on a sample.
  #[inline]
  fn eval(& self, & HSample) -> bool ;
}


#[doc = r#"Associates qualifiers to predicates.

Predicate variables are anonymous, so the qualifiers are the same for everyone.
It's just a matter of what the arity of the predicate is. So this structure
really stores all the qualifiers for a predicate with arity `1`, then all those
for arity `2`, and so on.

A list of blacklisted qualifiers is also maintained so that one can block
qualifiers that have already been chosen. **Do not forget** to clear the
blacklist when relevant."#]
pub struct Qualifiers {
  /// Maps arity to qualifiers. Only accessible *via* the iterator.
  ///
  /// Invariant: `arity_map.len()` is `instance.max_pred_arity` where
  /// `instance` is the Instance used during construction.
  arity_map: ArityMap< Vec< (Term, QualValues) > >,
  /// Maps predicates to their arity.
  pred_to_arity: PrdMap<Arity>,
  /// Blacklisted qualifiers.
  blacklist: HConSet<RTerm>,
}
impl Qualifiers {
  /// Constructor.
  pub fn mk(instance: & Instance) -> Self {
    let mut arity_map = ArityMap::with_capacity( * instance.max_pred_arity ) ;
    arity_map.push( vec![] ) ;
    for var_idx in VarRange::zero_to( * instance.max_pred_arity ) {
      let var = instance.var(var_idx) ;
      let mut terms = HConSet::with_capacity( instance.consts().len() * 5 ) ;
      for cst in instance.consts() {
        let _ = terms.insert( instance.ge(var.clone(), cst.clone()) ) ;
        let _ = terms.insert( instance.le(var.clone(), cst.clone()) ) ;
        let _ = terms.insert( instance.eq(var.clone(), cst.clone()) ) ;
        for other_var in VarRange::zero_to( var_idx ) {
          use instance::Op ;
          let other_var = instance.var(other_var) ;
          let add = instance.op(
            Op::Add, vec![ var.clone(), other_var.clone() ]
          ) ;
          let _ = terms.insert( instance.ge(add.clone(), cst.clone()) ) ;
          let _ = terms.insert( instance.le(add.clone(), cst.clone()) ) ;
          let _ = terms.insert( instance.eq(add.clone(), cst.clone()) ) ;
          let sub_1 = instance.op(
            Op::Sub, vec![ var.clone(), other_var.clone() ]
          ) ;
          let _ = terms.insert( instance.ge(sub_1.clone(), cst.clone()) ) ;
          let _ = terms.insert( instance.le(sub_1.clone(), cst.clone()) ) ;
          let _ = terms.insert( instance.eq(sub_1.clone(), cst.clone()) ) ;
          let sub_2 = instance.op(
            Op::Sub, vec![ other_var, var.clone() ]
          ) ;
          let _ = terms.insert( instance.ge(sub_2.clone(), cst.clone()) ) ;
          let _ = terms.insert( instance.le(sub_2.clone(), cst.clone()) ) ;
          let _ = terms.insert( instance.eq(sub_2.clone(), cst.clone()) ) ;
        }
      }
      arity_map.push(
        terms.into_iter().map(
          |term| ( term, QualValues::mk() )
        ).collect()
      )
    }
    let pred_to_arity = instance.preds().iter().map(
      |info| info.sig.len().into()
    ).collect() ;
    Qualifiers {
      arity_map, pred_to_arity,
      blacklist: HConSet::with_capacity(107),
    }
  }

  /// Accessor to the qualifiers.
  pub fn qualifiers(& self) -> & ArityMap< Vec< (Term, QualValues) > > {
    & self.arity_map
  }

  /// Qualifiers for a predicate.
  pub fn of<'a>(& 'a self, pred: PrdIdx) -> QualIter<'a> {
    // for (arity, quals) in self.arity_map.index_iter() {
    //   println!("|===| arity {}", arity) ;
    //   for & (ref term, ref vals) in quals {
    //     println!("| {}", term) ;
    //     print!(  "|  +") ;
    //     for sample in vals.true_set.iter() {
    //       print!(" {}", sample)
    //     }
    //     println!("") ;
    //     print!("|  -") ;
    //     for sample in vals.flse_set.iter() {
    //       print!(" {}", sample)
    //     }
    //     println!("")
    //   }
    // }
    QualIter {
      arity_map: & self.arity_map,
      blacklist: & self.blacklist,
      pred_arity: self.pred_to_arity[pred],
      curr_arity: 0.into(),
      curr_term: 0,
    }
  }

  /// Blacklists a qualifier.
  pub fn blacklist(& mut self, qual: & Term) {
    let is_new = self.blacklist.insert(qual.clone()) ;
    debug_assert!(is_new)
  }

  /// Clears the blacklist.
  pub fn clear_blacklist(& mut self) {
    self.blacklist.clear()
  }

  /// Registers a sample.
  fn register_sample(& mut self, pred: PrdIdx, args: HSample) -> Res<()> {
    let mut exclusive_ub = self.pred_to_arity[pred] ;
    exclusive_ub.inc() ;
    for arity in ArityRange::zero_to( exclusive_ub ) {
      for pair in self.arity_map[arity].iter_mut() {
        let (term, values) = (& pair.0, & mut pair.1) ;
        if let Some(val) = term.bool_eval(& args) ? {
          values.add(args.clone(), val) ;
        } else {
          bail!("[bug] incomplete arguments in learning data")
        }
      }
    }
    Ok(())
  }

  /// Registers some learning data.
  pub fn register_data(& mut self, data: LearningData) -> Res<()> {
    for Sample { pred, args } in data.pos {
      self.register_sample(pred, args) ?
    }
    for Sample { pred, args } in data.neg {
      self.register_sample(pred, args) ?
    }
    for Constraint { lhs, rhs } in data.cstr {
      for Sample { pred, args } in lhs {
        self.register_sample(pred, args) ?
      }
      if let Some( Sample { pred, args } ) = rhs {
        self.register_sample(pred, args) ?
      }
    }
    Ok(())
  }


  /// Adds a qualifier.
  ///
  /// The data is necessary to evaluate the qualifier and populate its
  /// values.
  pub fn add_qual(& mut self, qual: Term, data: & Data) -> Res<()> {
    let arity: Arity = if let Some(max_var) = qual.highest_var() {
      (* max_var).into()
    } else {
      bail!("[bug] trying to add constant qualifier")
    } ;
    let values = data.samples_fold(
      QualValues::mk(), |mut values, sample| {
        if sample.len() >= * arity {
          match qual.bool_eval(& * sample) {
            Ok( Some(b) ) => values.add(sample, b),
            Ok( None ) => panic!(
              "incomplete model, cannot evaluate qualifier"
            ),
            Err(e) => panic!(
              "[bug] error while evaluating qualifier: {}", e
            ),
          }
        }
        values
      }
    ) ? ;
    debug_assert!({
      for & (ref q, _) in self.arity_map[arity].iter() {
        assert!(q != & qual)
      }
      true
    }) ;
    self.arity_map[arity].push( (qual, values) ) ;
    Ok(())
  }
}



#[doc = r#"Iterator over the qualifiers of a predicate."#]
pub struct QualIter<'a> {
  /// Reference to the arity map.
  arity_map: & 'a ArityMap< Vec< (Term, QualValues) > >,
  /// Blacklisted terms.
  blacklist: & 'a HConSet<RTerm>,
  /// Arity of the predicate the qualifiers are for.
  pred_arity: Arity,
  /// Arity index of the next qualifier.
  ///
  /// - invariant: `curr_arity <= pred_arity`
  curr_arity: Arity,
  /// Index of the next qualifier w.r.t. the arity index.
  curr_term: usize
}
impl<'a> ::std::iter::Iterator for QualIter<'a> {
  type Item = (& 'a Term, & 'a QualValues) ;
  fn next(& mut self) -> Option< (& 'a Term, & 'a QualValues) > {
    while self.curr_arity <= self.pred_arity {
      if self.curr_term < self.arity_map[self.curr_arity].len() {
        // Term of index `curr_term` exists, return that.
        let (
          ref term, ref values
        ) = self.arity_map[self.curr_arity][self.curr_term] ;
        self.curr_term += 1 ;
        // Early return if not blacklisted.
        if ! self.blacklist.contains(term) {
          return Some( (term, values) )
        }
      } else {
        // We reached the end of the current arity, moving on to the next one.
        self.curr_term = 0 ;
        self.curr_arity.inc()
        // Loop: will exit if return `None` if above predicate's arity.
      }
    }
    None
  }
}