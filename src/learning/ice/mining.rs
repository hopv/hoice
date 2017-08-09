//! Mines an instance for qualifiers.

use common::* ;
use instance::* ;
use common::data::HSample ;


#[doc = r#"Stores the (truth) value of a qualifier on some samples.

In `debug` mode, stores two sets of samples, one for each truth value the
qualifier can take.

In `release` mode, stores only the set of samples on which the qualifier is
true. Any sample not in this set is assumed to make the qualifier evaluate
to false.

This is because in `debug`, we want to check that we're not missing qualifiers.
But not in `release`, where we just want to go fast and save memory.

The two versions must be indistinguishable from the outside."#]
#[cfg(debug)]
pub struct QualValues {
  /// Samples on which the qualifier evaluates to true.
  true_set: HConSet<Args>,
  /// Samples on which the qualifier evaluates to false.
  flse_set: HConSet<Args>,
}
#[cfg(debug)]
impl QualValues {
  /// Constructor.
  pub fn mk() -> Self {
    QualValues {
      true_set: HConSet::with_capacity(1003),
      flse_set: HConSet::with_capacity(1003),
    }
  }
}
#[cfg(debug)]
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

#[cfg( not(debug) )]
pub struct QualValues {
  /// Samples on which the qualifier evaluates to true.
  true_set: HConSet<Args>,
}
#[cfg( not(debug) )]
impl QualValues {
  /// Constructor.
  pub fn mk() -> Self {
    QualValues { true_set: HConSet::with_capacity(1003) }
  }
}
#[cfg( not(debug) )]
impl QualValuesExt for QualValues {
  fn add(& mut self, s: HSample, val: bool) {
    if val {
      let _ = self.true_set.insert(s) ;
    }
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
blacklist when relevant.

# Warning

Sharing `arity_map` (behind a lock) is logically unsafe, as it breaks a
non-sharing assumption in `add_qual`."#]
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
  fn register_sample(& mut self, args: HSample) -> Res<()> {
    for arity in ArityRange::zero_to( args.len() + 1 ) {
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

  /// Registers some samples.
  pub fn register_samples(
    & mut self, new_samples: Vec<HSample>
  ) -> Res<()> {
    for sample in new_samples {
      self.register_sample(sample) ?
    }
    Ok(())
  }


  /// Adds a qualifier.
  pub fn add_qual<'a>(
    & 'a mut self, qual: Term, samples: & ::common::data::HSampleConsign
  ) -> Res<& 'a QualValues> {
    let arity: Arity = if let Some(max_var) = qual.highest_var() {
      (1 + * max_var).into()
    } else {
      bail!("[bug] trying to add constant qualifier")
    } ;
    let values = samples.read().map_err(
      corrupted_err
    )?.fold(
      |mut values, sample| {
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
      }, QualValues::mk()
    ) ;
    debug_assert!({
      for & (ref q, _) in self.arity_map[arity].iter() {
        assert!(q != & qual)
      }
      true
    }) ;
    
    // The two operations below make sense iff `arity_map` is not shared.
    self.arity_map[arity].push( (qual, values) ) ;
    // If it was shared, someone could insert between these two lines.
    let & (
      _, ref last_values
    ) = self.arity_map[arity].last().unwrap() ;
    //                               ^^^^^^^^|
    // Definitely safe right after the push -|

    Ok(last_values)
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