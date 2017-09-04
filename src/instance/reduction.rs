#![doc = r#"Reduction strategies.

The strategies are attached `struct`s so that they can be put in a
vector using single dispatch. That way, they can be combined however we want.
"#]

use common::* ;
use instance::* ;

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
  fn propagate(& mut self, instance: & mut Instance) -> Res<()> {
    let mut cls_idx = ClsIdx::zero() ;

    'clause_iter: while cls_idx < instance.clauses().next_index() {

      // If `rhs` is true, remove clause.
      if let TTerm::P { pred, .. }  = instance.clauses[cls_idx].rhs {
        match instance.preds_term[pred].as_ref().map(
          |t| t.is_true()
        ) {
          Some(true) => {
            let _clause = instance.forget_clause(cls_idx) ;
            log_info!{
              "dropping clause {}, rhs is true",
              _clause.string_do( & instance.preds, |s| s.to_string() ) ?
            }
            continue 'clause_iter
          },
          Some(false) => bail!(
            "progation for terms that are not `true` is not implemented"
          ),
          _ => (),
        }
      }

      let clause = & mut instance.clauses[cls_idx] ;
      let mut cnt = 0 ;
      'lhs_iter: while cnt < clause.lhs.len() {
        if let TTerm::P { pred, .. } = clause.lhs[cnt] {
          match instance.preds_term[pred].as_ref().map(
            |t| t.is_true()
          ) {
            Some(true) => {
              let _ = clause.lhs.swap_remove(cnt) ;
              continue 'lhs_iter
            },
            Some(false) => bail!(
              "progation for terms that are not `true` is not implemented"
            ),
            None => (),
          }
        }
        cnt += 1
      }

      cls_idx.inc()
    }
    Ok(())
  }

  /// Finds `true => p(...)` and forces `p` to be `true` in the instance.
  ///
  /// Does not propagate.
  fn find_true_implies(& mut self, instance: & mut Instance) -> Res<()> {
    self.true_preds.clear() ;
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
      self.propagate(instance) ? ;
      Ok(true)
    } else {
      Ok(false)
    }
  }
}


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