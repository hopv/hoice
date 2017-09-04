#![doc = r#"Reduction strategies.

The strategies are attached `struct`s so that they can be put in a
vector using single dispatch. That way, they can be combined however we want.
"#]

use common::* ;
use instance::* ;


/// Returns the active strategies.
fn strategies() -> Vec< Box<RedStrat> > {
  vec![
    Box::new( TrueImplies::mk() ),
  ]
}


/// Reduces an instance.
pub fn work(instance: & mut Instance) -> Res<()> {
  let mut strategies = strategies() ;
  let mut changed = true ;
  'all_strats_fp: while changed {
    changed = false ;
    for strat in & mut strategies {
      let mut this_changed = strat.apply(instance) ? ;
      'strat_fp: while this_changed {
        this_changed = strat.apply(instance) ?
      }
      changed = changed || this_changed
    }
  }
  Ok(())
}



/// Reduction strategy trait.
///
/// Function `apply` will be applied until fixed point (`false` is returned).
pub trait RedStrat {
  /// Applies the reduction strategy. Returns `true` if it did something.
  fn apply(& mut self, & mut Instance) -> Res<bool> ;
}

/// Simplies clauses of the form `true => p(v_1, ..., v_n)` where all the
/// `v_i`s are different.
pub struct TrueImplies {
  /// Predicates found to be equivalent to true, but not propagated yet.
  true_preds: PrdSet,
}
impl TrueImplies {
  /// Constructor.
  fn mk() -> Self {
    TrueImplies { true_preds: PrdSet::with_capacity(7) }
  }

  /// Propagates the predicates stored in `self`.
  fn propagate(& mut self, instance: & mut Instance) {
    let (mut lhs, mut rhs) = (
      ClsSet::with_capacity(self.true_preds.len() * 3),
      ClsSet::with_capacity(self.true_preds.len() * 2)
    ) ;
    for pred in & self.true_preds {
      instance.drain_unlink_pred(* pred, & mut lhs, & mut rhs) ;
    }

    // At this point, all the LHSs to update are in `lhs`, and likewise for
    // `rhs`. Now we iterate over `lhs`, ignoring those that are also in `rhs`
    // because these clauses will just be dropped afterwards anyways.
    for clause in lhs {
      if ! rhs.contains(& clause) {
        // Remove all applications of predicates we know are true.
        let clause = & mut instance.clauses[clause] ;
        let mut cnt = 0 ;
        'lhs_iter: while cnt < clause.lhs.len() {
          if let TTerm::P { pred, .. } = clause.lhs[cnt] {
            if self.true_preds.contains(& pred) {
              let _ = clause.lhs.swap_remove(cnt) ;
              continue 'lhs_iter // Don't increment `cnt` when swap removing.
            }
          }
          cnt += 1
        }
      }
    }

    // Now we just need to remove all clauses in `rhs`.
    instance.forget_clauses( rhs.into_iter().collect() ) ;
    self.true_preds.clear()
  }

  /// Finds `true => p(...)` and forces `p` to be `true` in the instance.
  ///
  /// Does not propagate.
  fn find_true_implies(& mut self, instance: & mut Instance) -> Res<()> {
    debug_assert!( self.true_preds.is_empty() ) ;
    let mut cls_idx = ClsIdx::zero() ;
    'trivial_preds: while cls_idx < instance.clauses().next_index() {
      let maybe_pred = if instance.clauses()[cls_idx].lhs().is_empty() {
        if let TTerm::P {
          pred, ref args
        } = * instance.clauses()[cls_idx].rhs() {
          // rhs is a predicate application...
          let mut vars = VarSet::with_capacity(args.len()) ;
          let mut okay = true ;
          for term in args {
            let arg_okay = if let Some(idx) = term.var_idx() {
              let is_new = vars.insert(idx) ;
              is_new
            } else {
              // Not a variable.
              false
            } ;
            okay = okay && arg_okay
          }
          if okay {
            Some(pred)
          } else {
            None
          }
        } else { None }
      } else { None } ;
      if let Some(pred) = maybe_pred {
        let _ = self.true_preds.insert(pred) ;
        let term = instance.bool(true) ;
        log_info!{
          "trivial predicate {}: forcing to {}", instance[pred], term
        }
        instance.force_pred(pred, term) ? ;
        let _clause = instance.forget_clause(cls_idx) ;
        log_info!{
          "dropped associated clause {}",
          _clause.string_do( & instance.preds, |s| s.to_string() ) ?
        }
      } else {
        cls_idx.inc()
      }
    }
    Ok(())
  }
}
impl RedStrat for TrueImplies {
  fn apply(& mut self, instance: & mut Instance) -> Res<bool> {
    self.find_true_implies(instance) ? ;
    if ! self.true_preds.is_empty() {
      self.propagate(instance) ;
      Ok(true)
    } else {
      Ok(false)
    }
  }
}