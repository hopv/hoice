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
    // Box::new( SimpleOneRhs::mk() ),
  ]
}


/// Reduces an instance.
pub fn work(instance: & mut Instance) -> Res<()> {
  let mut strategies = strategies() ;
  let mut changed = true ;
  'all_strats_fp: while changed {
    changed = false ;
    for strat in & mut strategies {
      info!("\napplying {}", conf.emph( strat.name() )) ;
      let mut this_changed = strat.apply(instance) ? ;
      changed = changed || this_changed ;
      'strat_fp: while this_changed {
        if this_changed {
          log_info!{
            "instance:\n{}\n\n", instance.to_string_info(()) ?
          }
        }
        this_changed = strat.apply(instance) ?
      }
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
  /// Name of the strategy.
  fn name(& self) -> & 'static str ;
}





/// Simplies clauses of the form `true => p(v_1, ..., v_n)` where all the
/// `v_i`s are different. Unfolds `p` to `true`.
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
        instance.force_pred(pred, vec![ TTerm::T(term) ]) ? ;
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
  fn name(& self) -> & 'static str { "true => ..." }
  fn apply(& mut self, instance: & mut Instance) -> Res<bool> {
    debug_assert!( self.true_preds.is_empty() ) ;
    self.find_true_implies(instance) ? ;
    if ! self.true_preds.is_empty() {
      self.propagate(instance) ;
      Ok(true)
    } else {
      Ok(false)
    }
  }
}



/// Unfolds predicates that appear as the rhs of a single clause, and for
/// which the part of the lhs mentioning the variables used by the predicate
/// are completely separated from the rest.
///
/// Actually, currently this version will replace the term iff the lhs
/// mentions nothing but the variables used in the predicate application (rhs).
pub struct SimpleOneRhs {
  /// Terms to substitute the predicates with. The variable map maps the
  /// predicate's formal arguments to the ones in the term.
  pred_map: PrdHMap<(Vec<TTerm>, VarMap<VarIdx>)>,
  /// Set of clauses to forget.
  obsolete_clauses: Vec<ClsIdx>,
}
impl SimpleOneRhs {
  // /// Constructor.
  // fn mk() -> Self {
  //   SimpleOneRhs {
  //     pred_map: PrdHMap::with_capacity(7),
  //     obsolete_clauses: Vec::with_capacity(7),
  //   }
  // }

  /// Finds predicates satisfying the constraints above and creates the maps.
  fn find_preds_to_subst(& mut self, instance: & mut Instance) -> Res<()> {
    'pred_loop: for pred in instance.pred_indices() {
      info!( "\nworking on {}", conf.emph(& instance[pred].name) ) ;
      if instance.pred_to_clauses[pred].1.len() == 1 {
        let clause_index = * instance.pred_to_clauses[
          pred
        ].1.iter().next().unwrap() ;
        let clause = & instance[clause_index] ;
        // Set of variables to detect when the same variable is given twice
        // as argument.
        let mut vars = VarSet::with_capacity( instance[pred].sig.len() ) ;
        // Maps formal parameters of the predicate to variables in the term.
        let mut var_map = VarMap::with_capacity( vars.capacity() ) ;
        // Stores terms from the lhs and auxiliary terms introduced by the
        // treatment of the arguments.
        let mut terms = Vec::with_capacity( clause.lhs().len() ) ;
        // We might introduce fresh variables, this is the first index that
        // will not clash with the other variables in the clause.
        let mut fresh_var = clause.vars().next_index() ;
        
        if let TTerm::P { pred: same_pred, ref args } = * clause.rhs() {
          debug_assert!( pred == same_pred ) ;
          for arg in args {
            if let Some(var) = arg.var_idx() {
              let is_new_param = vars.insert(var) ;
              if is_new_param {
                // Bind formal input to this variable.
                var_map.push(var)
              } else {
                // Variable was already given as argument previously. Introduce
                // a new variable and equate it with `var` in the terms.
                let fresh = fresh_var ;
                fresh_var.inc() ; // Increment so that next fresh is fresh.
                // Not inserting in `vars`, `fresh` does not appear in the
                // clause anyways.
                var_map.push(fresh) ;
                terms.push(
                  TTerm::T(
                    instance.eq( instance.var(fresh), instance.var(var) )
                  )
                )
              }
            } else {
              continue 'pred_loop
            }
          }
        } else {
          bail!("inconsistency in predicate and clause links")
        }

        info!( "vars {{" ) ;
        for var in & vars {
          info!("  {}", clause[* var])
        }
        info!("}}") ;
        info!( "var_map {{" ) ;
        for (from, to) in var_map.index_iter() {
          if * to < var_map.len() {
            info!("  v_{} -> {}", from, clause[* to])
          } else {
            info!("  v_{} -> v_{} (fresh)", from, to)
          }
        }
        info!("}}") ;
        info!( "auxiliary terms {{" ) ;
        for term in & terms {
          info!("  {}", term)
        }
        info!("}}") ;

        // At this point we know all the variables the predicate application
        // uses. We now split the lhs of the clause between the terms that 
        // mention only these variables.
        // We skip the clause if there are term linking variables in `vars` and
        // other variables.

        // To do (maybe): modify the clause in place. Not doing it currently as
        // the loop might early return.
        info!( "\n lhs time:" ) ;
        for lhs in clause.lhs() {
          info!( "  {}", lhs ) ;
          let lhs_vars = lhs.vars() ;
          info!("  - vars {{") ;
          for var in & lhs_vars {
            info!("    {}", clause[* var])
          }
          info!("  }}") ;
          if lhs_vars.is_subset(& vars) {
            info!("  - subset") ;
            terms.push( lhs.clone() )
          } else {
            info!("  - not subset") ;
            continue 'pred_loop
          }
        }

        self.obsolete_clauses.push(clause_index) ;

        info!("\n everything okay, pushing") ;

        let prev = self.pred_map.insert(pred, (terms, var_map)) ;
        if prev.is_some() {
          bail!(
            "unfolding predicate {} twice with different definitions...",
            conf.sad(& instance[pred].name)
          )
        }
      }
    }
    Ok(())
  }

  /// Propagate predicates and forget clauses.
  fn propagate(& mut self, instance: & mut Instance) -> Res<()> {
    debug_assert_eq!( self.pred_map.len(), self.obsolete_clauses.len() ) ;
    instance.forget_clauses( self.obsolete_clauses.drain(0..).collect() ) ;
    Ok(())
  }
}
impl RedStrat for SimpleOneRhs {
  fn name(& self) -> & 'static str { "simple one rhs" }
  fn apply(& mut self, instance: & mut Instance) -> Res<bool> {
    self.find_preds_to_subst(instance) ? ;
    if ! self.pred_map.is_empty() {
      self.propagate(instance) ? ;
      log_info!{
        "instance:\n{}\n\n", instance.to_string_info(()) ?
      }
    }
    bail!("unimplemented") ;
    // Ok(false)
  }
}