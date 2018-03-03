//! A pre-instance wraps an instance and provides functionalities used by the
//! pre-processing.

use common::* ;
use common::smt::{ SmtConj, SmtImpl } ;

use instance::info::* ;
use instance::Clause ;


/// Wraps an instance for pre-processing.
pub struct PreInstance<'a> {
  /// The instance wrapped.
  instance: & 'a mut Instance,
  /// Solver used for triviality-checking.
  solver: Solver<()>,
  /// Clause simplifier.
  simplifier: ClauseSimplifier,

  /// Factored vector of clauses to check for simplification.
  ///
  /// Be **super careful** of swap removes.
  clauses_to_check: ClsSet,
  /// Factored vector of clauses to simplify.
  clauses_to_simplify: Vec<ClsIdx>,
}
impl<'a> PreInstance<'a> {
  /// Constructor.
  pub fn new(instance: & 'a mut Instance) -> Res<Self> {
    let solver = conf.solver.spawn("preproc", ()) ? ;

    let simplifier = ClauseSimplifier::new() ;
    let clauses_to_check = ClsSet::with_capacity(7) ;
    let clauses_to_simplify = Vec::with_capacity(7) ;

    Ok(
      PreInstance {
        instance, solver, simplifier,
        clauses_to_check, clauses_to_simplify
      }
    )
  }

  /// Destroys the pre instance, kills the internal solver.
  pub fn destroy(mut self) -> Res<()> {
    self.solver.kill().chain_err(
      || "While killing preproc solver"
    ) ? ;
    Ok(())
  }

  /// Forces to false (true) all the predicates that only appear in clauses'
  /// lhs (rhs).
  pub fn force_trivial(& mut self) -> Res< RedInfo > {
    let mut info: RedInfo = (0, 0, 0).into() ;
    let mut fixed_point = false ;
    while ! fixed_point {
      fixed_point = true ;
      for pred in PrdRange::zero_to( self.instance.preds.len() ) {
        if ! self.instance.is_known(pred) {
          if self.instance.pred_to_clauses[pred].1.is_empty() {
            info.preds += 1 ;
            fixed_point = false ;
            info += self.force_false(pred) ?
          } else if self.instance.pred_to_clauses[pred].0.is_empty() {
            info.preds += 1 ;
            fixed_point = false ;
            info += self.force_true(pred) ?
          }
        }
      }
    }
    Ok(info)
  }



  /// Simplifies all the clauses.
  pub fn simplify_all(& mut self) -> Res<RedInfo> {
    let mut info = RedInfo::new() ; // self.force_trivial() ? ;

    // Go through the clauses in reverse so that swap removes are safe.
    let mut clause = self.instance.clauses.next_index() ;

    while clause > 0 {
      clause.dec() ;
      info += self.simplify_clause(clause) ? ;
      conf.check_timeout() ?
    }

    info += self.force_trivial() ? ;

    Ok(info)
  }



  /// Simplifies some clauses.
  ///
  /// - can change **all** clause indices because of potential swap removes
  /// - does not run `force_trivial`
  fn simplify_clauses(& mut self) -> Res<RedInfo> {
    let mut info = RedInfo::new() ;
    // We're **popping**, so sort lowest to highest to avoid problems with swap
    // removes.
    self.clauses_to_simplify.sort_unstable_by(
      |c_1, c_2| c_1.cmp( c_2 )
    ) ;
    log_debug! { "    simplify clauses ({})", self.clauses_to_simplify.len() }
    let mut prev = None ;
    while let Some(clause) = self.clauses_to_simplify.pop() {
      prev = {
        if let Some(prev) = prev {
          if clause == prev { continue }
        }
        Some(clause)
      } ;
      info += self.simplify_clause(clause) ?
    }
    self.check("after `simplify_clauses`") ? ;
    Ok(info)
  }


  /// Simplifies a clause.
  ///
  /// This function might create new clauses. Potentially voids the semantics
  /// of clause indices *after* `clause`. Modifying this function by making it
  /// void clause indices *before* `clause` will break the whole
  /// pre-processing.
  fn simplify_clause(& mut self, clause: ClsIdx) -> Res<RedInfo> {
    macro_rules! rm_return {
      ($clause:ident if $should_remove:expr => $blah:expr) => (
        if $should_remove {
          info! {
            "  removing clause #{} by {}", clause, $blah
          }
          self.instance.forget_clause(clause) ? ;
          return Ok( RedInfo::of_clauses_rmed(1) )
        }
      ) ;
    }

    log_debug! { "simplifying clause #{}", clause }

    if self.instance[clause].is_unsat() {
      bail!( ErrorKind::Unsat )
    }

    // log_debug! {
    //   "{}", self[clause].to_string_info(self.preds()).unwrap()
    // }


    if self.instance[clause].terms_changed() {
      // Propagate.
      rm_return! {
        clause if self.simplifier.clause_propagate(
          & mut self.instance[clause]
        ) ? => "propagation"
      }

      // Check for triviality.
      rm_return! {
        clause if self.is_clause_trivial(clause) ? => "clause trivial"
      }
    }

    rm_return! {
      clause if self.is_redundant(clause) => "clause redundant"
    }

    if self.instance[clause].terms_changed() {
      // Remove redundant atoms.
      if conf.preproc.prune_terms {
        self.prune_atoms(clause) ?
      }
    }

    self.instance[clause].lhs_terms_checked() ;

    // Try to split the clause.
    self.split_disj(clause)
  }

  /// Splits disjunctions.
  ///
  /// Splits a clause if it contains exactly one disjunction, if its rhs
  /// predicate appear in the rhs of other clauses too.
  ///
  /// Returns the number of clauses created.
  fn split_disj(& mut self, clause_idx: ClsIdx) -> Res< RedInfo > {
    let mut info: RedInfo = (0, 0, 0).into() ;

    macro_rules! clause {
      ($idx:expr) => ( self.instance.clauses[clause_idx] ) ;
    }

    // Skip those for which the predicate in the rhs only appears in this
    // rhs.
    if let Some((pred, _)) = clause!(clause_idx).rhs() {
      if self.instance.pred_to_clauses[pred].1.len() == 1 {
        return Ok(info)
      }
    }

    // Skip if one of the predicates in the lhs only appears (once) in this
    // lhs.
    for (pred, argss) in self[clause_idx].lhs_preds() {
      if argss.len() == 1 {
        if self.clauses_of(* pred).0.len() == 1 {
          return Ok(info)
        }
      }
    }

    // Skip if clause contains more than 2 disjunctions.
    let mut disj = None ;
    for term in clause!(clause_idx).lhs_terms() {
      if let Some(args) = term.disj_inspect() {
        // More than one disjunction, skipping.
        if disj.is_some() {
          return Ok(info)
        }
        disj = Some((term.clone(), args.clone()))
      }
    }

    if let Some((disj, mut kids)) = disj {
      let was_there = clause!(clause_idx).rm_term(& disj) ;
      debug_assert!(was_there) ;
      if let Some(kid) = kids.pop() {
        let clause = clause!(clause_idx).clone() ;

        clause!(clause_idx).insert_term(kid) ;
        info += self.simplify_clause( clause_idx ) ? ;

        for kid in kids {
          let mut clause = clause.clone() ;
          clause.insert_term(kid) ;
          if let Some(this_clause_idx) = self.instance.push_clause(clause) ? {
            info.clauses_added += 1 ;
            info += self.simplify_clause( this_clause_idx ) ?
          }
        }
        Ok(info)
      } else {
        Ok(info)
      }
    } else {
      Ok(info)
    }
  }

  /// Removes redundant atoms.
  fn prune_atoms(& mut self, clause: ClsIdx) -> Res<()> {
    let atoms: Vec<Term> = self.instance[clause].lhs_terms().iter().map(
      |atom| atom.clone()
    ).collect() ;

    if atoms.is_empty() { return Ok(()) }

    let clause = & mut self.instance[clause] ;

    self.solver.push(1) ? ;

    self.solver.comment("Pruning atoms...") ? ;

    clause.declare(& mut self.solver) ? ;

    for atom in atoms {
      let keep = if let Some(implication) = SmtImpl::new(
        clause.lhs_terms(), & atom
      ) {
        let actlit = self.solver.get_actlit() ? ;
        self.solver.assert_act(& actlit, & implication) ? ;
        let res = self.solver.check_sat_act( Some(& actlit) ) ? ;
        self.solver.de_actlit(actlit) ? ;
        res
      } else {
        bail!("failed to construct implication wrapper")
      } ;
      if ! keep {
        let was_there = clause.rm_term(& atom) ;
        debug_assert! { was_there }
      }
      conf.check_timeout() ? ;
    }

    self.solver.comment("Done pruning atoms...") ? ;

    self.solver.pop(1) ? ;

    Ok(())
  }

  /// Checks whether a clause is trivial.
  ///
  /// Returns true if
  ///
  /// - the terms in the lhs are equivalent to `false`, or
  /// - the rhs is a predicate application contained in the lhs.
  fn is_clause_trivial(& mut self, clause: ClsIdx) -> Res<bool> {
    let mut lhs: Vec<Term> = Vec::with_capacity(17) ;
    let clause = & self.instance[clause] ;

    for term in clause.lhs_terms() {
      match term.bool() {
        Some(true) => (),
        Some(false) => return Ok(true),
        _ => {
          let neg = term::not( term.clone() ) ;
          for term in & lhs {
            if neg == * term {
              return Ok(true)
            }
          }
          lhs.push( term.clone() )
        },
      }
    }

    let conj = SmtConj::new( lhs.iter() ) ;

    if clause.rhs().is_none() && clause.lhs_preds().is_empty() {

      // Either it is trivial, or falsifiable regardless of the predicates.
      if conj.is_unsat(
        & mut self.solver, clause.vars()
      ) ? {
        return Ok(true)
      } else {
        log_debug!{
          "unsat because of {}",
          clause.to_string_info( self.instance.preds() ) ?
        }
        bail!( ErrorKind::Unsat )
      }

    } else {

      if let Some((pred, args)) = clause.rhs() {
        if clause.lhs_preds().get(& pred).map(
          |set| set.contains(args)
        ).unwrap_or(false) {
          return Ok(true)
        }
      }

      if lhs.is_empty() {
        Ok(false)
      } else {
        conj.is_unsat(
          & mut self.solver, clause.vars()
        )
      }

    }

  }







  /// Checks the underlying instance is correct.
  pub fn check(& self, blah: & 'static str) -> Res<()> {
    if ! self.clauses_to_check.is_empty() {
      bail!("clauses_to_check is not empty: {}", blah)
    }
    self.instance.check(blah)
  }





  /// Forces all the remaining predicates to some DNFs at the same time.
  ///
  /// Checks that the positive and negative constraints are respected. Returns
  /// `true` if they are, *i.e.* the definitions are a legal model, and `false`
  /// otherwise.
  pub fn force_all_preds(
    & mut self, defs: PrdHMap< Vec<(Quantfed, TTermSet)> >
  ) -> Res< (bool, RedInfo) > {
    for (pred, def_opt) in self.pred_terms.index_iter() {
      if def_opt.is_none() && defs.get(& pred).is_none() {
        bail!(
          format!(
            "error in `force_all_preds`, no definition for {}", self[pred]
          )
        )
      }
    }
    log_debug! { "  forcing all {} remaining predicates", defs.len() }

    let mut info = RedInfo::new() ;
    info.clauses_rmed += self.instance.clauses.len() ;

    // Force predicates.
    for (pred, def) in defs {
      log_debug! { "    forcing {}", self[pred] }
      let def = TTerms::dnf(
        def.into_iter().map(
          |(quantfed, conj)| (
            Quant::exists(quantfed), conj
          )
        ).collect()
      ) ;
      debug_assert! { self.instance.pred_terms[pred].is_none() }
      self.instance.pred_terms[pred] = Some(def)
    }

    // Drop all clauses.
    log_debug! { "  unlinking all predicates" }
    for & mut (
      ref mut lhs, ref mut rhs
    ) in self.instance.pred_to_clauses.iter_mut() {
      lhs.clear() ;
      rhs.clear()
    }
    log_debug! { "  dropping non pos/neg clauses" }
    let mut clause: ClsIdx = 0.into() ;
    while clause < self.instance.clauses.len() {
      if self.instance.clauses[clause].rhs().is_none()
      || self.instance.clauses[clause].lhs_preds().is_empty() {
        clause.inc() ;
        continue
      } else {
        self.instance.clauses.swap_remove(clause) ;
      }
    }
    log_debug! { "  checking pred defs" }
    let is_sat = self.check_pred_defs() ? ;
    self.instance.clauses.clear() ;

    Ok( (is_sat, info) )
  }





  /// Forces a predicate to be equal to something.
  ///
  /// Does not impact `pred_to_clauses`.
  fn force_pred(
    & mut self, pred: PrdIdx, tterms: TTerms
  ) -> Res<()> {
    if let Some(_) = self.instance.pred_terms[pred].as_ref() {
      let mut s: Vec<u8> = Vec::new() ;
      tterms.write_smt2(
        & mut s, |w, pred, args| {
          write!(w, "({}", self[pred]) ? ;
          for arg in args.iter() {
            write!(w, " {}", arg) ?
          }
          write!(w, ")")
        }
      ).chain_err(
        || "while dumping top terms during error on `force_pred`"
      ) ? ;
      bail!(
        "[bug] trying to force predicate {} twice\n{}",
        conf.sad(& self.instance[pred].name),
        String::from_utf8_lossy(& s)
      )
    } else {
      self.instance.pred_terms[pred] = Some(tterms)
    }
    Ok(())
  }











  /// Forces some predicate to false.
  ///
  /// Simplifies all clauses impacted.
  pub fn force_false(& mut self, pred: PrdIdx) -> Res<RedInfo> {
    self.check("before force false") ? ;

    let mut info = RedInfo::new() ;

    self.force_pred( pred, TTerms::fls() ) ? ;

    // Forget everything in `lhs`.
    debug_assert!( self.clauses_to_simplify.is_empty() ) ;
    self.instance.unlink_pred_lhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    info.clauses_rmed += self.clauses_to_simplify.len() ;
    self.instance.forget_clauses( & mut self.clauses_to_simplify ) ? ;

    // Update `rhs`.
    debug_assert!( self.clauses_to_simplify.is_empty() ) ;
    self.instance.unlink_pred_rhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    for clause in & self.clauses_to_simplify {
      let clause = * clause ;
      debug_assert_eq! {
        self.instance.clauses[clause].rhs().map(|(p, _)| p), Some(pred)
      }
      self.instance.clauses[clause].unset_rhs() ;
    }
    self.check("after force true") ? ;

    // Simplify all clauses that have been modified.
    info += self.simplify_clauses() ? ;

    Ok(info)
  }

  /// Forces some predicates to true.
  ///
  /// Simplifies all clauses impacted.
  pub fn force_true(& mut self, pred: PrdIdx) -> Res<RedInfo> {
    self.check("before force true") ? ;

    let mut info = RedInfo::new() ;

    self.force_pred( pred, TTerms::tru() ) ? ;

    // Forget everything in `rhs`.
    debug_assert!( self.clauses_to_simplify.is_empty() ) ;
    self.instance.unlink_pred_rhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    info.clauses_rmed += self.clauses_to_simplify.len() ;
    self.instance.forget_clauses( & mut self.clauses_to_simplify ) ? ;

    // Update `rhs`.
    debug_assert!( self.clauses_to_simplify.is_empty() ) ;
    self.instance.unlink_pred_lhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    for clause in & self.clauses_to_simplify {
      let prev = self.instance.clauses[* clause].drop_lhs_pred(pred) ;
      debug_assert! { prev.is_some() }
    }
    self.check("after force true") ? ;

    // Simplify all clauses that have been modified.
    info += self.simplify_clauses() ? ;

    Ok(info)
  }


  /// Forces the lhs occurences of a predicate to be equal to something.
  ///
  /// If `pred` appears in `pred /\ apps /\ trms => rhs`, the clause will
  /// become `apps /\ pred_apps /\ trms /\ terms => rhs`.
  ///
  /// # Usage
  ///
  /// This function can only be called if `pred` appears exactly once as a
  /// consequent, say in clause `c`, and `c`'s antecedent has no application
  /// of `pred`.
  ///
  /// Otherwise, it will return an error.
  ///
  /// # Consequences
  ///
  /// - forgets the one clause `pred` is in the rhs of
  /// - forces `pred` to be `exists qvars, pred_apps /\ terms`
  /// - simplifies all clauses impacted
  ///
  /// # Used by
  ///
  /// - `SimpleOneRhs`
  /// - `OneRhs`
  pub fn force_pred_left(
    & mut self, pred: PrdIdx,
    qvars: Quantfed,
    tterm_set: TTermSet,
  ) -> Res<RedInfo> {
    self.check("before `force_pred_left`") ? ;

    // let mut tterm_set = TTermSet::new() ;
    // tterm_set.insert_terms(terms) ;
    // for (pred, args) in pred_apps {
    //   tterm_set.insert_pred_app(pred, args) ;
    // }

    if tterm_set.is_empty() {
      return self.force_true(pred)
    }

    let mut info = RedInfo::new() ;

    log_debug! {
      "  force pred left on {}...", conf.emph(& self.instance[pred].name)
    }

    // Update lhs clauses.
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_lhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    log_debug! {
      "    updating lhs clauses ({})", self.clauses_to_simplify.len()
    }

    'clause_iter: for clause in & self.clauses_to_simplify {
      let clause = * clause ;
      log_debug! {
        "    - working on lhs of clause {}",
        self.instance[clause].to_string_info(
          self.instance.preds()
        ).unwrap()
      }

      let argss = if let Some(
        argss
      ) = self.instance.clauses[clause].drop_lhs_pred(pred) {
        argss
      } else {
        bail!(
          "inconsistent instance state, \
          `pred_to_clauses` and clauses out of sync"
        )
      } ;

      for args in argss {
        // Generate fresh variables for the clause if needed.
        let qual_map = self.instance.clauses[clause].fresh_vars_for(& qvars) ;

        for term in tterm_set.terms() {
          if let Some((term, _)) = term.subst_total( & (& args, & qual_map) ) {
            self.instance.clause_add_lhs_term(clause, term)
          } else {
            bail!("error during total substitution in `force_pred_left`")
          }
        }

        for (pred, app_argss) in tterm_set.preds() {
          let pred = * pred ;
          for app_args in app_argss {
            let mut nu_args = VarMap::with_capacity( args.len() ) ;
            for arg in app_args.iter() {
              if let Some((arg, _)) = arg.subst_total(
                & (& args, & qual_map)
              ) {
                nu_args.push(arg)
              }
            }
            self.instance.clause_add_lhs_pred(clause, pred, nu_args)
          }
        }
      }

      log_debug! {
        "    done with clause: {}",
        self.instance[clause].to_string_info(
          self.instance.preds()
        ).unwrap()
      }

    }

    // Simplify the clauses we just updated.
    info += self.simplify_clauses() ? ;


    // Forget the rhs clause.
    log_debug! {
      "    forgetting rhs clause"
    }
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_rhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    let clause_to_rm = if let Some(clause) = self.clauses_to_simplify.pop() {

      // Fail if illegal.
      if self.clauses_to_simplify.pop().is_some() {
        bail!(
          "illegal context for `force_pred_left`, \
          {} appears in more than one rhs",
          conf.emph(& self.instance[pred].name)
        )
      }
      if self.instance.preds_of_clause(clause).0.get(& pred).is_some() {
        bail!(
          "illegal context for `force_pred_left`, \
          {} appears as both lhs and rhs",
          conf.emph(& self.instance[pred].name)
        )
      }

      clause
    } else {
      bail!(
        "illegal context for `force_pred_left`, \
        {} appears in no rhs", conf.emph(
          & self.instance[pred].name
        )
      )
    } ;

    // Actually force the predicate.
    self.force_pred(
      pred,
      TTerms::conj(
        Quant::exists(qvars), tterm_set
      )
    ) ? ;

    info.clauses_rmed += 1 ;
    self.instance.forget_clause(clause_to_rm) ? ;

    self.check("after `force_pred_left`") ? ;

    info += self.force_trivial() ? ;

    Ok(info)
  }




  /// Forces all lhs occurrences of a predicate to be replaced by a DNF.
  ///
  /// - only legal if `pred` does not appear in any rhs
  /// - in general, will create new clauses
  /// - if `def` is empty, equivalent to `force_false`
  /// - simplifies all clauses impacted
  /// - does not call `force_trivial`
  ///
  /// Used by `GraphRed`.
  pub fn force_dnf_left(
    & mut self, pred: PrdIdx, def: Vec< (Quantfed, TTermSet) >
  ) -> Res<RedInfo> {
    let def: Vec<_> = def.into_iter().map(
      |(qvars, conj)| (
        Quant::exists(qvars), conj
      )
    ).collect() ;

    if def.is_empty() {
      return self.force_false(pred)
    }

    let mut info = RedInfo::new() ;

    self.check("before `force_dnf_left`") ? ;

    log_debug! { "  force_dnf_left {}", self[pred] }

    // Make sure there's no rhs clause for `pred`.
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_rhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    if ! self.clauses_to_simplify.is_empty() {
      bail!(
        "can't force dnf {}, it appears in some rhs", self.instance[pred]
      )
    }

    // Update lhs clauses.
    let mut clauses_to_rm = Vec::with_capacity(
      self.instance.pred_to_clauses[pred].0.len()
    ) ;
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_lhs(
      pred, & mut clauses_to_rm
    ) ;
    // Rev-sorting as we're going to swap remove stuff.
    clauses_to_rm.sort_unstable_by(
      |c_1, c_2| c_2.cmp(c_1)
    ) ;

    for clause in clauses_to_rm {
      info.clauses_rmed += 1 ;

      let pred_argss: Vec< HTArgs > = if let Some(
        argss
      ) = self.instance.clauses[clause].drop_lhs_pred(pred) {
        argss.iter().map(|a| a.clone()).collect()
      } else {
        bail!("inconsistent instance state")
      } ;

      // This is why we rev-sorted:
      let clause = self.instance.forget_clause(clause) ? ;

      // This vector maps indices from `pred_argss` to the disjuncts of `def`.
      let mut def_indices = vec![ 0 ; pred_argss.len() ] ;

      let mut is_done = false ;

      while ! is_done {
        let mut clause = clause.clone() ;

        for arg_idx in 0..def_indices.len() {
          let def_idx = def_indices[arg_idx] ;
          let params = & pred_argss[arg_idx] ;
          let (ref quant, ref conj) = def[def_idx] ;

          let quant_map = clause.nu_fresh_vars_for(& quant) ;

          for term in conj.terms() {
            if let Some((term, _)) = term.subst_total(
              & (params, & quant_map)
            ) {
              clause.insert_term(term) ;
            } else {
              bail!("unexpected total substitution failure on term {}", term)
            }
          }

          for (pred, argss) in conj.preds() {
            let pred = * pred ;
            for args in argss {
              let mut nu_args = VarMap::with_capacity( args.len() ) ;
              for arg in args.iter() {
                if let Some((arg, _)) = arg.subst_total(
                  & (params, & quant_map)
                ) {
                  nu_args.push(arg)
                } else {
                  bail!(
                    "unexpected total substitution failure on arg {} \
                    of ({} {})", arg, self[pred], args
                  )
                }
              }
              clause.insert_pred_app( pred, nu_args.into() ) ;
            }
          }
        }

        // This is a bit dangerous as we're inside a loop iterating over some
        // clause indices `for clause in clauses_to_rm { ... }`.
        //
        // It's fine here since by construction, `this_clause` is at the end of
        // the clause list, meaning simplifying it will not impact other
        // clauses.
        let this_clause = self.instance.clauses.next_index() ;
        let is_new = self.instance.push_clause_unchecked(clause) ;
        if is_new {
          info.clauses_added += 1 ;
          info += self.simplify_clause(this_clause) ?
        }

        // Increment.
        let mut n = def_indices.len() ;
        let mut increase = false ;
        while n > 0 {
          n -= 1 ;
          if def_indices[n] + 1 < def.len() {
            def_indices[n] += 1 ;
            increase = false ;
            break
          } else {
            def_indices[n] = 0 ;
            increase = true
          }
        }
        // If we still need to increase at this point, we went over the max
        // index of the first application, meaning we went over everything.
        is_done = increase

      }

    }

    // Actually force the predicate.
    self.force_pred(
      pred, TTerms::dnf(def)
    ) ? ;

    self.check("after `force_dnf_left`") ? ;

    Ok(info)
  }





  /// Forces the rhs occurrences of a predicate to be equal to something.
  ///
  /// If `pred` appears in `args /\ trms => pred`, the clause will become
  /// `apps /\ pred_apps /\ trms /\ terms => pred_app`.
  ///
  /// Quantified variables are understood as universally quantified.
  ///
  /// # Usage
  ///
  /// This function can only be called if `pred` appears exactly once as an
  /// antecedent, say in clause `c`, and `c`'s consequent is not an application
  /// of `pred`.
  ///
  /// Otherwise, it will return an error.
  ///
  /// # Consequences
  ///
  /// - forgets the one clause `pred` is in the lhs of
  /// - forces `pred` to be `forall qvars, pred_app \/ (not /\ pred_apps) \/
  ///   (not /\ terms)`
  ///
  /// # Used by
  ///
  /// - `SimpleOneLhs`
  pub fn force_pred_right(
    & mut self, pred: PrdIdx,
    qvars: Quantfed,
    pred_app: Option< (PrdIdx, HTArgs) >,
    negated: TTermSet,
  ) -> Res<RedInfo> {
    self.check("before `force_pred_right`") ? ;

    let mut info = RedInfo::new() ;

    let quant = Quant::forall( qvars ) ;

    log_debug! {
      "  force pred right on {}...", conf.emph(& self.instance[pred].name)
    }

    // Update rhs clauses.
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_rhs(
      pred, & mut self.clauses_to_simplify
    ) ;

    'clause_iter: for clause in & self.clauses_to_simplify {
      let clause = * clause ;
      log_debug!{ "    working on clause #{}", clause }
      log_debug! {
        "{}", self.instance[clause].to_string_info(
          self.instance.preds()
        ).unwrap()
      }

      let rhs = self.instance.clauses[clause].unset_rhs() ;

      if let Some((prd, subst)) = rhs {
        let qual_map = self.instance.clauses[clause].nu_fresh_vars_for(
          & quant
        ) ;

        if pred == prd {

          log_debug! { "      generating new rhs" }

          // New rhs.
          if let Some( & (prd, ref args) ) = pred_app.as_ref() {
            let mut nu_args = VarMap::with_capacity( args.len() ) ;

            for arg in args.iter() {
              if let Some((nu_arg, _)) = arg.subst_total(
                & (& subst, & qual_map)
              ) {
                nu_args.push(nu_arg)
              } else {
                bail!("unexpected failure during total substitution")
              }
            }

            self.instance.clause_force_rhs(
              clause, prd, nu_args.into()
            ) ?
          }
          // No `else`, clause's rhs is already `None`.

          log_debug! { "      generating new lhs pred apps" }

          // New lhs predicate applications.
          for (pred, argss) in negated.preds() {
            let pred = * pred ;
            for args in argss {
              let mut nu_args = VarMap::with_capacity( args.len() ) ;
              for arg in args.iter() {
                if let Some((nu_arg, _)) = arg.subst_total(
                  & (& subst, & qual_map)
                ) {
                  nu_args.push(nu_arg)
                } else {
                  bail!("unexpected failure during total substitution")
                }
              }
              self.instance.clause_add_lhs_pred(clause, pred, nu_args)
            }
          }
          
          log_debug! { "      generating new lhs terms" }

          // New lhs terms.
          for term in negated.terms() {
            if let Some((term, _)) = term.subst_total(
              & (& subst, & qual_map)
            ) {
              self.instance.clause_add_lhs_term(clause, term)
            }
          }

          log_debug! { "{}", self.instance[clause].to_string_info(self.instance.preds()).unwrap() }

          // Explicitely continueing, otherwise the factored error message
          // below will fire.
          continue 'clause_iter
        }
      }

      bail!(
        "inconsistent instance state, \
        `pred_to_clauses` and clauses out of sync"
      )
    }

    // Simplify the clause we updated.
    info += self.simplify_clauses() ? ;

    // Make sure there's exactly one lhs clause for `pred`.
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_lhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    let clause_to_rm = if let Some(clause) = self.clauses_to_simplify.pop() {
      if self.clauses_to_simplify.pop().is_some() {
        bail!(
          "illegal context for `force_pred_right`, \
          {} appears in more than one lhs",
          conf.emph(& self.instance[pred].name)
        )
      }
      if self.instance.preds_of_clause(clause).1 == Some(pred) {
        bail!(
          "illegal context for `force_pred_right`, \
          {} appears as both lhs and rhs",
          conf.emph(& self.instance[pred].name)
        )
      }
      clause
    } else {
      bail!(
        "illegal context for `force_pred_right`, \
        {} appears in no lhs",
        conf.emph(& self.instance[pred].name)
      )
    } ;

    // Actually force the predicate.
    self.force_pred(
      pred, TTerms::disj_of_pos_neg(
        quant, pred_app.map(
          |(pred, args)| ( pred, args )
        ), negated
      )
    ) ? ;

    info.clauses_rmed += 1 ;
    self.instance.forget_clause(clause_to_rm) ? ;

    self.check("after `force_pred_right`") ? ;

    Ok(info)
  }


  /// Unrolls some predicates.
  ///
  /// For each clause `(pred args) /\ lhs => rhs`, adds `terms /\ lhs => rhs`
  /// for terms in `pred_terms[p]`.
  ///
  /// Only unrolls negative clauses where `(pred args)` is not the only
  /// application.
  pub fn unroll(
    & mut self, pred: PrdIdx, terms: Vec<(Option<Quant>, TTermSet)>
  ) -> Res<RedInfo> {
    let mut info = RedInfo::new() ;
    let mut to_add = Vec::with_capacity(17) ;
    let fls = term::fls() ;

    info! {
      "  {} appears in {} clause's lhs",
      conf.emph(& self[pred].name),
      self.instance.pred_to_clauses[pred].0.len()
    }

    for clause in & self.instance.pred_to_clauses[pred].0 {
      let clause = & self.instance[* clause] ;

      // Negative clause and `pred` is the only application.
      if clause.rhs().is_none() && clause.lhs_preds().len() == 1 {
        continue
      }

      let argss = if let Some(argss) = clause.lhs_preds().get(& pred) {
        argss
      } else {
        bail!( "inconsistent instance state, `pred_to_clauses` out of sync" )
      } ;

      for & (ref quant, ref tterms) in & terms {
        let mut nu_clause = clause.clone_except_lhs_of(pred, "unrolling") ;
        let qual_map = nu_clause.nu_fresh_vars_for(quant) ;

        for args in argss {
          conf.check_timeout() ? ;
          if ! tterms.preds().is_empty() {
            bail!("trying to unroll predicate by another predicate")
          }
          for term in tterms.terms() {
            if let Some((nu_term, _)) = term.subst_total(
              & (& args, & qual_map)
            ) {
              nu_clause.insert_term(nu_term) ;
            } else {
              bail!("unexpected failure during total substitution")
            }
          }
        }

        println!("propagating in {}", nu_clause.to_string_info(self.preds()).unwrap()) ;
        let mut skip = self.simplifier.clause_propagate(& mut nu_clause) ? ;
        println!("looking for false") ;
        skip = skip || nu_clause.lhs_terms().contains( & fls ) ;

        if ! skip {
          nu_clause.from_unrolling = true ;
          to_add.push( nu_clause )
        }
      }
    }

    info! { "  adding {} clauses", to_add.len() }

    for mut clause in to_add {
      log_debug! {
        "  adding clause {}",
        clause.to_string_info(& self.preds).unwrap()
      }
      if let Some(index) = self.instance.push_clause(clause) ? {
        let mut simplinfo = self.simplify_clause(index) ? ;
        if simplinfo.clauses_rmed > 0 {
          simplinfo.clauses_rmed -= 1
        } else {
          simplinfo.clauses_added += 1
        }
        info += simplinfo
      }
    }

    self.check("after unroll") ? ;

    Ok(info)
  }


  /// Reverse unrolls some predicates.
  ///
  /// For each clause `lhs => (pred args)`, adds `(not terms) /\ lhs => false`
  /// for terms in `pred_terms[p]`.
  ///
  /// Only unrolls clauses which have at least one lhs predicate application.
  pub fn reverse_unroll(
    & mut self, pred: PrdIdx, terms: Vec<(Option<Quant>, HConSet<Term>)>
  ) -> Res<RedInfo> {
    let mut info = RedInfo::new() ;
    let mut to_add = Vec::with_capacity(17) ;
    let fls = term::fls() ;

    for clause in & self.instance.pred_to_clauses[pred].1 {
      let clause = & self.instance[* clause] ;

      // Negative clause and `pred` is the only application.
      if clause.lhs_preds().is_empty() {
        continue
      }

      let args = if let Some((p, args)) = clause.rhs() {
        debug_assert_eq! { p, pred }
        args
      } else {
        bail!("inconsistent instance state")
      } ;

      for & (ref quant, ref terms) in & terms {
        let mut nu_clause = clause.clone_with_rhs(None, "r_unroll") ;
        let qual_map = nu_clause.nu_fresh_vars_for(quant) ;

        for term in terms {
          conf.check_timeout() ? ;
          if let Some((nu_term, _)) = term.subst_total(
            & (& args, & qual_map)
          ) {
            nu_clause.insert_term(nu_term) ;
          } else {
            bail!("unexpected failure during total substitution")
          }
        }

        let mut skip = self.simplifier.clause_propagate(& mut nu_clause) ? ;
        skip = skip || nu_clause.lhs_terms().contains( & fls ) ;

        if ! skip {
          nu_clause.from_unrolling = true ;
          to_add.push( nu_clause )
        }
      }
    }

    for mut clause in to_add {
      log_debug! {
        "  adding clause {}",
        clause.to_string_info(& self.preds).unwrap()
      }
      if let Some(index) = self.instance.push_clause(clause) ? {
        let mut simplinfo = self.simplify_clause(index) ? ;
        if simplinfo.clauses_rmed > 0 {
          simplinfo.clauses_rmed -= 1
        } else {
          simplinfo.clauses_added += 1
        }
        info += simplinfo
      }
    }

    self.check("after runroll") ? ;

    Ok(info)
  }


  /// Removes irrelevant predicate arguments.
  pub fn arg_reduce(& mut self) -> Res<RedInfo> {
    let to_keep = ::instance::preproc::args::to_keep(self) ? ;
    self.rm_args(to_keep)
  }


  /// Removes all predicate arguments not in `to_keep`, and all corresponding
  /// arguments in the clauses. Updates `old_preds`, `pred_terms` and.
  fn rm_args(& mut self, to_keep: PrdHMap<VarSet>) -> Res<RedInfo> {
    if_debug! {
      log_debug! { "  rm_args ({})", to_keep.len() }
      log_debug! { "  to keep {{" }
      for (pred, vars) in to_keep.iter() {
        let mut s = String::new() ;
        for var in vars {
          s.push_str(" ") ;
          s.push_str( & var.default_str() )
        }
        log_debug! { "    {}:{}", self[* pred], s }
      }
      log_debug! { "  }}" }
    }

    self.check("rm_args") ? ;

    let mut info = RedInfo::new() ;

    macro_rules! rm_args {
      (from $args:expr, keep nothing, swap $nu_args:expr) => ({
        debug_assert!( $nu_args.is_empty() ) ;
        ::std::mem::swap($nu_args, $args) ;
        $nu_args.clear() ;
      }) ;
      (from $args:expr, keep $to_keep:expr, to $nu_args:expr) => ({
        debug_assert!( $nu_args.is_empty() ) ;
        for (var, arg) in $args.index_iter() {
          if $to_keep.contains(& var) {
            $nu_args.push( arg.clone() )
          }
        }
      }) ;
    }

    // Remove args from forced predicates.
    for tterms_opt in & mut self.instance.pred_terms {
      if let Some(tterms) = tterms_opt.as_mut() {
        tterms.remove_vars(& to_keep)
      }
    }

    debug_assert! { self.clauses_to_check.is_empty() }

    let mut did_something = false ;

    // Remove args from applications in clauses.
    for (pred, to_keep) in to_keep {
      if to_keep.len() == self[pred].sig.len() { continue }
      did_something = true ;

      log_debug! { "  - {}", self[pred] }
      debug_assert!( to_keep.len() <= self[pred].sig.len() ) ;
      if to_keep.len() == self[pred].sig.len() {
        log_debug! { "    skipping" }
        continue
      }
      log_debug! {
        "  working on {} ({}/{})",
        self[pred], to_keep.len(), self[pred].sig.len()
      }

      let mut var_map = VarMap::with_capacity( to_keep.len() ) ;
      let mut nu_sig = VarMap::with_capacity( to_keep.len() ) ;
      for (var, typ) in self[pred].sig.index_iter() {
        if to_keep.contains(& var) {
          // Re-route current **new** var to the original variable `var` is
          // pointing to.
          var_map.push( self.old_preds[pred].1[var] ) ;
          nu_sig.push(* typ)
        } else {
          info.args_rmed += 1
        }
      }

      // Update `preds` with the new signature.
      self.instance.preds[pred].sig = nu_sig ;
      // Update `old_preds`'s map.
      self.instance.old_preds[pred].1 = var_map ;

      // Propagate removal to clauses.
      let (ref lhs, ref rhs) = self.instance.pred_to_clauses[pred] ;

      for clause in lhs {
        self.clauses_to_check.insert(* clause) ;

        self.instance.clauses[
          * clause
        ].lhs_map_args_of(
          pred, |args| {
            let mut nu_args = VarMap::with_capacity(
              args.len() - to_keep.len()
            ) ;
            rm_args! { from args, keep to_keep, to nu_args }
            nu_args.into()
          }
        ) ;

        conf.check_timeout() ?
      }

      for clause in rhs {
        self.clauses_to_check.insert(* clause) ;
        debug_assert! { self.instance.clauses[* clause].rhs().is_some() }
        self.instance.clauses[* clause].rhs_map_args(
          |p, args| {
            debug_assert_eq!( pred, p ) ;
            let mut nu_args = VarMap::with_capacity(
              args.len() - to_keep.len()
            ) ;
            rm_args! { from args, keep to_keep, to nu_args }
            ( p, nu_args.into() )
          }
        ) ;
        conf.check_timeout() ?
      }

      ()
    }

    if ! did_something { return Ok(info) }

    // Simplify the clauses we just updated.
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.clauses_to_simplify = self.clauses_to_check.drain().collect() ;

    info += self.simplify_clauses() ? ;

    // Force trivial predicates if any.
    info += self.force_trivial() ? ;

    self.check("after `rm_args`") ? ;

    Ok(info)
  }

  /// Removes all clauses in which `pred` is in the rhs.
  ///
  /// Does not run simplifications.
  pub fn rm_rhs_clauses_of(& mut self, pred: PrdIdx) -> Res<RedInfo> {
    debug_assert! { self.clauses_to_simplify.is_empty() }
    let mut info = RedInfo::new() ;
    let to_rm = self.instance.pred_to_clauses[pred].1.clone() ;
    // self.instance.unlink_pred_rhs(pred, & mut self.clauses_to_simplify) ;
    info.clauses_rmed += to_rm.len() ;
    self.instance.forget_clauses( & mut to_rm.into_iter().collect() ) ? ;
    Ok(info)
  }




  /// Checks the predicates' definition verify the current instance.
  ///
  /// Returns `true` if they work (sat).
  ///
  /// # Errors if
  ///
  /// - some predicates are not defined
  pub fn check_pred_defs(& mut self) -> Res<bool> {
    if self.active_pred_count() > 0 {
      bail!(
        "can't check predicate definitions, some predicates are not defined"
      )
    }

    self.solver.reset() ? ;

    let set = PrdSet::new() ;
    self.instance.finalize() ? ;
    for pred in self.instance.sorted_forced_terms() {
      let pred = * pred ;
      log_debug! { "    definining {}", self[pred] }

      let sig: Vec<_> = self.instance[pred].sig.index_iter().map(
        |(var, typ)| (var.default_str(), * typ)
      ).collect() ;

      if let Some(ref def) = self.instance.pred_terms[pred] {
        self.solver.define_fun_with(
          & self.instance[pred].name,
          & sig,
          & Typ::Bool,
          def,
          & (& set, & set, & self.instance.preds)
        ) ?
      } else {
        bail!(
          "can't check predicate definitions, predicate {} is not defined",
          self.instance.preds[pred]
        )
      }
    }

    for clause in & self.instance.clauses {
      self.solver.push(1) ? ;
      for info in clause.vars() {
        if info.active {
          self.solver.declare_const( & info.idx.default_str(), & info.typ ) ?
        }
      }
      self.solver.assert_with(
        clause, & (false, & set, & set, & self.instance.preds)
      ) ? ;

      let sat = self.solver.check_sat() ? ;
      self.solver.pop(1) ? ;
      return Ok(! sat)
    }

    Ok(true)
    
  }

}



impl<'a> ::std::ops::Deref for PreInstance<'a> {
  type Target = Instance ;
  fn deref(& self) -> & Instance {
    self.instance
  }
}
// impl<'a, Slver> ::std::ops::DerefMut for PreInstance<'a, Slver> {
//   fn deref_mut(& mut self) -> & mut Instance {
//     self.instance
//   }
// }





/// Simplifies clauses.
///
/// The goal of this type is to avoid reallocation and compartment the clause
/// simplification process.
pub struct ClauseSimplifier {
  /// Maps variables to their representative.
  var_to_rep: VarHMap<VarIdx>,
  /// Maps variables to their representative as a term.
  var_to_rep_term: VarHMap<Term>,
  /// Maps representatives to their equivalence set.
  rep_to_vars: VarHMap<VarSet>,
  /// Maps representatives to a term they're equal to according to an equality
  /// in the clause's lhs.
  rep_to_term: VarHMap<Term>,
  /// Mpas representatives to the final term they're equal to.
  rep_to_stable_term: VarHMap<Term>,
  /// Terms to add to the clause.
  terms_to_add: Vec<Term>,
  /// Stores equalities found in clauses.
  eqs: Vec<Term>,
  /// Stores equalities found in clauses that have been dismissed.
  other_eqs: Vec<Term>
}
impl ClauseSimplifier {
  /// Constructor.
  pub fn new() -> Self {
    ClauseSimplifier {
      var_to_rep: VarHMap::with_capacity(29),
      var_to_rep_term: VarHMap::with_capacity(29),
      rep_to_vars: VarHMap::with_capacity(29),
      rep_to_term: VarHMap::with_capacity(29),
      rep_to_stable_term: VarHMap::with_capacity(29),
      terms_to_add: Vec::with_capacity(29),
      eqs: Vec::with_capacity(11),
      other_eqs: Vec::with_capacity(11),
    }
  }

  /// Prints its state.
  #[cfg( not(feature = "bench") )]
  #[allow(dead_code)]
  fn print_state(& self, pref: & str) {
    if ! self.var_to_rep.is_empty() {
      log_debug!{ "{}var_to_rep {{", pref }
      for (var, rep) in & self.var_to_rep {
        log_debug!{ "{}  {} -> {}", pref, var, rep }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.var_to_rep_term.is_empty() {
      log_debug!{ "{}var_to_rep_term {{", pref }
      for (var, rep) in & self.var_to_rep_term {
        log_debug!{ "{}  {} -> {}", pref, var, rep }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.rep_to_vars.is_empty() {
      log_debug!{ "{}rep_to_vars {{", pref }
      for (rep, set) in & self.rep_to_vars {
        log_debug!{ "{}  {} -> {}", pref, rep, Self::pretty_varset(set) }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.rep_to_term.is_empty() {
      log_debug!{ "{}rep_to_term {{", pref }
      for (rep, term) in & self.rep_to_term {
        log_debug!{ "{}  {} -> {}", pref, rep, term }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.rep_to_stable_term.is_empty() {
      log_debug!{ "{}rep_to_stable_term {{", pref }
      for (rep, term) in & self.rep_to_stable_term {
        log_debug!{ "{}  {} -> {}", pref, rep, term }
      }
      log_debug!{ "{}}}", pref }
    }
    if ! self.terms_to_add.is_empty() {
      log_debug!{ "{}terms_to_add {{", pref }
      for term in & self.terms_to_add {
        log_debug!{ "{}  {}", pref, term }
      }
      log_debug!{ "{}}}", pref }
    }
  }

  /// Pretty printer set of variables.
  #[cfg( not(feature = "bench") )]
  #[allow(dead_code)]
  fn pretty_varset(set: & VarSet) -> String {
    let mut s = String::new() ;
    s.push('{') ;
    for var in set {
      s.push_str( & format!(" {}", var) )
    }
    s.push(' ') ;
    s.push('}') ;
    s
  }

  /// Checks internal consistency.
  #[cfg(debug_assertions)]
  fn check(& self, vars: & VarMap<VarInfo>) -> Res<()> {
    // Representatives can only be mapped to themselves.
    for (var, rep) in & self.var_to_rep {
      if var != rep {
        for (_, rep) in & self.var_to_rep {
          if var == rep {
            bail!(
              "representative {} is mapped to representative {}",
              vars[* var], vars[* rep]
            )
          }
        }
      }
    }
    // Make sure `var_to_rep` and `rep_to_vars` are consistent.
    for (var, rep) in & self.var_to_rep {
      if var != rep {
        if ! self.rep_to_vars.get(rep).map(
          |set| set.contains(var)
        ).unwrap_or(false) {
          bail!{
            "{} is mapped to representative {}, \
            but does not appear in its equivalence class",
            vars[* var], vars[* rep]
          }
        }
      }
    }
    for (rep, set) in & self.rep_to_vars {
      for var in set {
        if self.var_to_rep.get(var) != Some(rep) {
          bail!{
            "{} is in the equivalence class of {} but is not mapped to it",
            vars[* var], vars[* rep]
          }
        }
      }
    }
    Ok(())
  }
  #[cfg( not(debug_assertions) )]
  #[inline(always)]
  fn check(& self, _: & VarMap<VarInfo>) -> Res<()> {
    Ok(())
  }

  /// Propagates equalities in a clause.
  ///
  /// Returns `true` if the clause should be removed.
  ///
  /// Assumes equalities have arity `2`.
  pub fn clause_propagate(& mut self, clause: & mut Clause) -> Res<bool> {
    self.var_to_rep.clear() ;
    self.var_to_rep_term.clear() ;
    self.rep_to_vars.clear() ;
    self.rep_to_term.clear() ;
    self.rep_to_stable_term.clear() ;
    self.terms_to_add.clear() ;
    self.eqs.clear() ;
    self.other_eqs.clear() ;
    let mut remove ;

    // Find equalities in `lhs`.
    for term in clause.lhs_terms() {
      if let Some((Op::Eql, _)) = term.app_inspect() {
        self.eqs.push( term.clone() )
      }
    }

    loop {
      let mut inlined = false ;

      while let Some(eq) = self.eqs.pop() {
        remove = true ;
        // log_debug!{ "  looking at equality {}", eq }

        let args = if let Some(args) = eq.kids() { args } else {
          unreachable!(
            "clause_propagate: not equality after checking that it is"
          )
        } ;
        if args.len() != 2 {
          bail!(
            "simplification for equality over more \
            than 2 terms is unimplemented"
          )
        }

        match (args[0].var_idx(), args[1].var_idx()) {

          (Some(v_1), Some(v_2)) if v_1 == v_2 => (),

          (Some(v_1), Some(v_2)) => match (
            self.var_to_rep.get(& v_1).map(|rep| * rep),
            self.var_to_rep.get(& v_2).map(|rep| * rep)
          ) {

            // Both already have same rep.
            (Some(rep_1), Some(rep_2)) if rep_1 == rep_2 => (),
            // Different rep.
            (Some(rep_1), Some(rep_2)) => {
              // We keep `rep_1`.
              let set_2 = if let Some(set) = self.rep_to_vars.remove(& rep_2) {
                set
              } else { bail!("simplification error (1)") } ;
              let set_1 = if let Some(set) = self.rep_to_vars.get_mut(& rep_1) {
                set
              } else { bail!("simplification error (2)") } ;
              // Drain `set_2`: update `var_to_rep` and `set_1`.
              use mylib::coll::* ;
              for var in set_2.into_iter().chain_one(rep_2) {
                let _prev = self.var_to_rep.insert(var, rep_1) ;
                debug_assert_eq!( _prev, Some(rep_2) ) ;
                let _is_new = set_1.insert(var) ;
                debug_assert!( _is_new )
              }
              // Re-route `rep_to_term`.
              if let Some(term) = self.rep_to_term.remove(& rep_2) {
                let prev = self.rep_to_term.insert(rep_1, term.clone()) ;
                if let Some(other_term) = prev {
                  self.terms_to_add.push( term::eq(term, other_term) )
                }
              }
            },
            // Only `v_1` has a rep.
            (Some(rep_1), None) => {
              let set_1 = if let Some(set) = self.rep_to_vars.get_mut(& rep_1) {
                set
              } else { panic!("simplification error (3)") } ;
              let _is_new = set_1.insert(v_2) ;
              debug_assert!( _is_new ) ;
              let _prev = self.var_to_rep.insert(v_2, rep_1) ;
              debug_assert!( _prev.is_none() )
            },
            // Only `v_2` has a rep.
            (None, Some(rep_2)) => {
              let set_2 = if let Some(set) = self.rep_to_vars.get_mut(& rep_2) {
                set
              } else { bail!("simplification error (4)") } ;
              let _is_new = set_2.insert(v_1) ;
              debug_assert!( _is_new ) ;
              let _prev = self.var_to_rep.insert(v_1, rep_2) ;
              debug_assert!( _prev.is_none() )
            },
            // No rep, we use `v_1` as the rep.
            (None, None) => {
              let mut set = VarSet::with_capacity(4) ;
              set.insert(v_2) ;
              let _prev = self.rep_to_vars.insert(v_1, set) ;
              debug_assert!( _prev.is_none() ) ;
              let _prev = self.var_to_rep.insert(v_1, v_1) ;
              debug_assert!( _prev.is_none() ) ;
              let _prev = self.var_to_rep.insert(v_2, v_1) ;
              debug_assert!( _prev.is_none() ) ;
            },

          },

          // A variable and a term.
          (Some(var), None) | (None, Some(var)) => {
            let term = if args[0].var_idx().is_some() {
              args[1].clone()
            } else { args[0].clone() } ;

            let rep = if let Some(rep) = self.var_to_rep.get(& var).map(
              |rep| * rep
            ) { rep } else {
              let _prev = self.var_to_rep.insert(var, var) ;
              debug_assert!( _prev.is_none() ) ;
              let _prev = self.rep_to_vars.insert(
                var, VarSet::with_capacity(4)
              ) ;
              debug_assert!( _prev.is_none() ) ;
              var
            } ;

            // Check for cycles.
            let mut skip = false ;
            for is_rep in term::vars(& term) {
              if let Some(rep_term) = self.rep_to_term.get(& is_rep) {
                if term::vars(& rep_term).contains(& rep) {
                  // Cycle, skip this equality.
                  skip = true ;
                  break
                }
              }
            }

            if skip {
              remove = false
            } else {
              // log_debug!{ "rep of {} is {}", var, rep }
              let prev = self.rep_to_term.insert(rep, term.clone()) ;
              if let Some(prev) = prev {
                let eq = term::eq(prev, term) ;
                match eq.eval( & () ) {
                  Ok(Val::B(true)) => (),
                  Ok(Val::B(false)) => return Ok(true),
                  Ok(Val::I(_)) => bail!(
                    "equality evaluation yielded integer"
                  ),
                  _ => self.terms_to_add.push(eq),
                }
              }
            }
          },

          // Two terms.
          (None, None) => {
            let inline = if clause.lhs_terms().contains(& args[0]) {
              Some( args[1].clone() )
            } else if clause.lhs_terms().contains(& args[1]) {
              Some( args[0].clone() )
            } else {
              let not_lhs = term::not( args[0].clone() ) ;
              let not_rhs = term::not( args[1].clone() ) ;
              if clause.lhs_terms().contains(& not_lhs) {
                Some(not_rhs)
              } else if clause.lhs_terms().contains(& not_rhs) {
                Some(not_lhs)
              } else {
                self.other_eqs.push( eq.clone() ) ;
                None
              }
            } ;
            if let Some(term) = inline {
              inlined = true ;
              clause.insert_term( term.clone() ) ;
              remove = true ;
              if term.is_eq() {
                self.eqs.push(term)
              } else {
                self.terms_to_add.push(term)
              }
            } else {
              remove = false
            }
          },

        }

        if remove {
          // log_debug!{ "  removing..." }
          let was_there = clause.rm_term(& eq) ;
          debug_assert!(was_there)
        } else {
          // log_debug!{ "  skipping..." }
        }
      }

      if ! inlined || self.other_eqs.is_empty() {
        break
      } else {
        ::std::mem::swap(& mut self.eqs, & mut self.other_eqs)
      }

    }

    self.check( clause.vars() ) ? ;

    // log_debug!{ "  generating `var_to_rep_term`" }
    self.var_to_rep_term = VarHMap::with_capacity( self.var_to_rep.len() ) ;
    for (rep, set) in & self.rep_to_vars {
      for var in set {
        if var != rep {
          let _prev = self.var_to_rep_term.insert(* var, term::var(* rep)) ;
          debug_assert!( _prev.is_none() )
        }
      }
    }
    // if_debug!{
    //   for (var, rep) in & self.var_to_rep {
    //     log_debug!{ "    {} -> {}", var.default_str(), rep.default_str() }
    //   }
    // }

    // log_debug!{ "  stabilizing `rep_to_term` (first step)" }
    for (_, term) in & mut self.rep_to_term {
      let (nu_term, changed) = term.subst(& self.var_to_rep_term) ;
      if changed { * term = nu_term }
    }
    let mut to_rm = vec![] ;
    for (rep, term) in & self.rep_to_term {
      // log_debug!{ "    {} -> {}", rep.default_str(), term }
      if term::vars(term).contains(rep) {
        // log_debug!{ "      -> recursive, putting equality back." }
        to_rm.push(* rep)
      }
    }
    for to_rm in to_rm {
      let term = self.rep_to_term.remove(& to_rm).ok_or::<Error>(
        "unreachable".into()
      ) ? ;
      self.terms_to_add.push(
        term::eq( term::var(to_rm), term )
      )
    }

    // log_debug!{
    //   "  stabilizing `rep_to_term` (second step, {})",
    //   self.rep_to_term.len()
    // }
    self.rep_to_stable_term = VarHMap::with_capacity(self.rep_to_term.len()) ;
    for (rep, term) in & self.rep_to_term {
      // log_debug! { "    pre subst: {}", term }
      let (nu_term, _) = term.subst_fp(& self.rep_to_term) ;
      // log_debug! { "    post subst" }
      let _prev = self.rep_to_stable_term.insert(* rep, nu_term) ;
      debug_assert!( _prev.is_none() )
    }
    // if_debug!{
    //   for (rep, term) in & self.rep_to_stable_term {
    //     log_debug!{ "    {} -> {}", rep, term }
    //   }
    // }

    // Note that clause variable de-activation is done in this loop.
    // log_debug!{ "  completing substitution" }
    for (rep, vars) in self.rep_to_vars.drain() {
      // log_debug!{"  - rep {}", rep}
      let term = if let Some(term) = self.rep_to_stable_term.get(& rep) {
        clause.vars[rep].active = false ;
        term.clone()
      } else {
        debug_assert!( clause.vars[rep].active ) ;
        term::var(rep)
      } ;
      for var in vars {
        if var != rep {
          // log_debug!{"    var: {}", var}
          clause.vars[var].active = false ;
          let _prev = self.rep_to_stable_term.insert(var, term.clone()) ;
          debug_assert_eq!( _prev, None )
        }
      }
    }
    // if_debug!{
    //   for (rep, term) in & self.rep_to_stable_term {
    //     log_debug!{ "    {} -> {}", rep, term }
    //   }
    // }

    for term in self.terms_to_add.drain(0..) {
      clause.insert_term(term) ;
    }

    // log_debug!{ "  updating clause's terms" }
    clause.subst(& self.rep_to_stable_term) ;

    // log_debug!{ "  done simplifying" }

    Ok(false)
  }

}