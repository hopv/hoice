#![doc = r#"Reduction strategies.

The strategies are attached `struct`s so that they can be put in a
vector using single dispatch. That way, they can be combined however we want.
"#]

use common::* ;
use instance::* ;


/// Returns the active strategies.
fn strategies() -> Vec< Box<RedStrat> > {
  let mut strats: Vec< Box<RedStrat> > = vec![
    Box::new( LhsOnlyToFalse {} ),
    Box::new( RhsOnlyToTrue {} ),
    Box::new( TrueImplies::mk() ),
  ] ;
  if conf.simple_red {
    strats.push( Box::new( SimpleOneRhs::mk() ) )
  }
  strats
}


/// Reduces an instance.
pub fn work(instance: & mut Instance) -> Res<()> {
  let mut strategies = strategies() ;
  let mut changed = true ;
  'all_strats_fp: while changed {
    if instance.clauses.is_empty() { break 'all_strats_fp }
    changed = false ;
    for strat in & mut strategies {
      if instance.clauses.is_empty() { break 'all_strats_fp }
      log_info!("\napplying {}", conf.emph( strat.name() )) ;
      let mut this_changed = strat.apply(instance) ? ;
      changed = changed || this_changed ;
      'strat_fp: while this_changed {
        this_changed = strat.apply(instance) ?
      }
    }
  }
  log_info!("") ;
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


/// Forces to false predicates appearing only in the lhs of the clauses.
pub struct LhsOnlyToFalse {}
impl RedStrat for LhsOnlyToFalse {
  fn name(& self) -> & 'static str { "lhs only" }
  fn apply(& mut self, instance: & mut Instance) -> Res<bool> {
    let mut found_one = false ;
    // Used when draining the clauses a predicate appears in.
    let (mut lhs_pred, mut rhs_pred) = (
      ClsSet::new(), ClsSet::new()
    ) ;
    'find_lhs_only: loop {
      let mut lhs_only = None ;
      for pred in instance.pred_indices() {
        if instance.terms_of(pred).is_none()
        && instance.pred_to_clauses[pred].1.is_empty() {
          lhs_only = Some(pred)
        }
      }
      if let Some(pred) = lhs_only {
        found_one = true ;
        let term = instance.bool(false) ;
        log_info!{
          "  trivial predicate {}: forcing to {}",
          conf.emph(& instance[pred].name), term
        }
        instance.force_pred(pred, vec![ TTerm::T(term) ]) ? ;
        instance.drain_unlink_pred(pred, & mut lhs_pred, & mut rhs_pred) ;
        debug_assert!( rhs_pred.is_empty() ) ;
        instance.forget_clauses( lhs_pred.drain().collect() )
      } else {
        // No predicate of interest found.
        break 'find_lhs_only
      }
    }
    Ok(found_one)
  }
}


/// Forces to false predicates appearing only in the lhs of the clauses.
pub struct RhsOnlyToTrue {}
impl RedStrat for RhsOnlyToTrue {
  fn name(& self) -> & 'static str { "rhs only" }
  fn apply(& mut self, instance: & mut Instance) -> Res<bool> {
    let mut found_one = false ;
    // Used when draining the clauses a predicate appears in.
    let (mut lhs_pred, mut rhs_pred) = (
      ClsSet::new(), ClsSet::new()
    ) ;
    'find_rhs_only: loop {
      let mut rhs_only = None ;
      for pred in instance.pred_indices() {
        if instance.terms_of(pred).is_none()
        && instance.pred_to_clauses[pred].0.is_empty() {
          rhs_only = Some(pred)
        }
      }
      if let Some(pred) = rhs_only {
        found_one = true ;
        let term = instance.bool(true) ;
        log_info!{
          "  trivial predicate {}: forcing to {}",
          conf.emph(& instance[pred].name), term
        }
        instance.force_pred(pred, vec![ TTerm::T(term) ]) ? ;
        instance.drain_unlink_pred(pred, & mut lhs_pred, & mut rhs_pred) ;
        debug_assert!( lhs_pred.is_empty() ) ;
        instance.forget_clauses( rhs_pred.drain().collect() )
      } else {
        // No predicate of interest found.
        break 'find_rhs_only
      }
    }
    Ok(found_one)
  }
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
          "  trivial predicate {}: forcing to {}",
          conf.emph(& instance[pred].name), term
        }
        instance.force_pred(pred, vec![ TTerm::T(term) ]) ? ;
        let _clause = instance.forget_clause(cls_idx) ;
        // log_info!{
        //   "dropped associated clause {}",
        //   _clause.string_do( & instance.preds, |s| s.to_string() ) ?
        // }
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
  /// Constructor.
  fn mk() -> Self {
    SimpleOneRhs {
      pred_map: PrdHMap::with_capacity(7),
      obsolete_clauses: Vec::with_capacity(7),
    }
  }

  /// Finds predicates satisfying the constraints above and creates the maps.
  fn find_preds_to_subst(& mut self, instance: & mut Instance) -> Res<()> {
    'pred_loop: for pred in instance.pred_indices() {
      if instance.pred_to_clauses[pred].1.len() == 1 {
        let clause_index = * instance.pred_to_clauses[
          pred
        ].1.iter().next().unwrap() ;

        // Skip if predicate also appears in lhs.
        if instance.pred_to_clauses[pred].0.contains(& clause_index) {
          continue 'pred_loop
        }

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

        // At this point we know all the variables the predicate application
        // uses. We now split the lhs of the clause between the terms that 
        // mention only these variables.
        // We skip the clause if there are term linking variables in `vars` and
        // other variables.

        // To do (maybe): modify the clause in place. Not doing it currently as
        // the loop might early return.
        for lhs in clause.lhs() {
          let lhs_vars = lhs.vars() ;
          if lhs_vars.is_subset(& vars) {
            // If this term is a predicate application we're already reducing,
            // skip. Otherwise, we would create circular dependencies.
            if let Some(lhs_pred) = lhs.pred() {
              debug_assert!( pred != lhs_pred ) ;
              if self.pred_map.contains_key(& lhs_pred) {
                continue 'pred_loop
              }
            }
            terms.push( lhs.clone() )
          } else {
            continue 'pred_loop
          }
        }

        self.obsolete_clauses.push(clause_index) ;

        let prev = self.pred_map.insert(pred, (terms, var_map)) ;
        log_info!{ "unfolding predicate {}", conf.emph(& instance[pred].name) }
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

  /// Applies a substitution to a top term.
  fn tterm_subst(
    factory: & Factory, subst: & VarHMap<Term>, tterm: & TTerm
  ) -> Res<TTerm> {
    match * tterm {
      TTerm::P { pred, ref args } => {
        let mut new_args = VarMap::with_capacity( args.len() ) ;
        for term in args {
          if let Some((term, _)) = factory.subst_total(
            subst, term
          ) {
            new_args.push(term)
          } else {
            bail!("total substitution failed")
          }
        }
        Ok( TTerm::P { pred, args: new_args } )
      },
      TTerm::T(ref term) => if let Some((term, _)) = factory.subst_total(
        subst, term
      ) {
        Ok( TTerm::T(term) )
      } else {
        bail!("total substitution failed")
      },
    }
  }

  /// Propagate predicates and forget clauses.
  fn propagate(& mut self, instance: & mut Instance) -> Res<()> {
    debug_assert_eq!( self.pred_map.len(), self.obsolete_clauses.len() ) ;

    let (mut lhs, mut rhs) = (
      ClsSet::with_capacity(7), ClsSet::with_capacity(7)
    ) ;
    let mut terms_to_add = vec![] ;

    for (pred, (tterms, var_map)) in self.pred_map.drain() {
      log_info!{ "forcing pred {}", instance[pred] }
      debug_assert!( terms_to_add.is_empty() ) ;
      instance.drain_unlink_pred(pred, & mut lhs, & mut rhs) ;

      for clause in lhs.drain() {
        if self.obsolete_clauses.contains(& clause) {
          continue
        }
        debug_assert!( terms_to_add.is_empty() ) ;

        {
          let mut cnt = 0 ;
          let lhs = & mut instance.clauses[clause].lhs ;
          'iter_lhs: while cnt < lhs.len() {
            match lhs[cnt] {
              TTerm::P { pred: this_pred, ref args } if pred == this_pred => {
                let mut subst = VarHMap::with_capacity(
                  instance.preds[pred].sig.len()
                ) ;
                for (from, to) in var_map.index_iter() {
                  let _prev = subst.insert(* to, args[from].clone()) ;
                  debug_assert!( _prev.is_none() )
                }
                for tterm in & tterms {
                  terms_to_add.push(
                    Self::tterm_subst(& instance.factory, & subst, tterm) ?
                  )
                }
              },
              _ => { cnt += 1 ; continue 'iter_lhs },
            }
            lhs.swap_remove(cnt) ;
          }
        }
        instance.clause_lhs_extend( clause, & mut terms_to_add )
      }

      for clause in rhs.drain() {
        if self.obsolete_clauses.contains(& clause) {
          continue
        }
        let tterms_for_new_clauses = {
          let rhs = & mut instance.clauses[clause].rhs ;
          match * rhs {
            TTerm::P { pred: _this_pred, ref args } => {
              debug_assert_eq!(pred, _this_pred) ;
              let mut subst = VarHMap::with_capacity(
                instance.preds[pred].sig.len()
              ) ;
              for (from, to) in var_map.index_iter() {
                let _prev = subst.insert(* to, args[from].clone()) ;
                debug_assert!( _prev.is_none() )
              }
              for tterm in & tterms {
                terms_to_add.push(
                  Self::tterm_subst(& instance.factory, & subst, tterm) ?
                )
              }
            },
            _ => bail!("inconsistency in predicate and clause links"),
          }

          let mut tterms = terms_to_add.drain(0..) ;
          if let Some(tterm) = tterms.next() {
            * rhs = tterm ;
            tterms
          } else {
            bail!("trying to force predicate to empty term")
          }
        } ;
        for tterm in tterms_for_new_clauses {
          let clause = Clause::mk(
            instance.clauses[clause].vars.clone(),
            instance.clauses[clause].lhs.clone(),
            tterm
          ) ;
          instance.push_clause(clause)
        }
      }


      let mut force_tterms = Vec::with_capacity( tterms.len() ) ;
      let mut subst = VarHMap::with_capacity(
        instance.preds[pred].sig.len()
      ) ;
      for (from, to) in var_map.index_iter() {
        let _prev = subst.insert(* to, instance.var(from)) ;
        debug_assert!( _prev.is_none() )
      }
      for tterm in tterms {
        force_tterms.push(
          Self::tterm_subst(& instance.factory, & subst, & tterm) ?
        )
      }
      instance.force_pred(pred, force_tterms) ? ;

    }

    instance.forget_clauses( self.obsolete_clauses.drain(0..).collect() ) ;
    Ok(())
  }
}
impl RedStrat for SimpleOneRhs {
  fn name(& self) -> & 'static str { "simple one rhs" }
  fn apply(& mut self, instance: & mut Instance) -> Res<bool> {
    debug_assert!( self.pred_map.is_empty() ) ;
    debug_assert!( self.obsolete_clauses.is_empty() ) ;
    self.find_preds_to_subst(instance) ? ;
    if ! self.pred_map.is_empty() {
      self.propagate(instance) ? ;
      Ok(true)
    } else {
      Ok(false)
    }
  }
}