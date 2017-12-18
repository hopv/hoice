//! A pre-instance wraps an instance and provides functionalities used by the
//! pre-processing.

use common::* ;
use instance::info::* ;
use super::ClauseSimplifier ;




/// Wrapper around a negated implication for smt printing.
struct NegImplWrap<'a, Terms> {
  /// Lhs.
  lhs: ::std::cell::RefCell<Terms>,
  /// Rhs.
  rhs: & 'a Term,
}
impl<'a, Terms> NegImplWrap<'a, Terms> {
  /// Constructor.
  pub fn new(lhs: Terms, rhs: & 'a Term) -> Self {
    NegImplWrap { lhs: ::std::cell::RefCell::new(lhs), rhs }
  }
}
impl<'a, Terms> ::rsmt2::to_smt::Expr2Smt<()> for NegImplWrap<'a, Terms>
where Terms: Iterator<Item = & 'a Term> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    let mut lhs = self.lhs.borrow_mut() ;
    write!(w, "(not ")? ;
    if let Some(term) = lhs.next() {
      write!(w, "(=> (and") ? ;
      write!(w, " ") ? ;
      term.write(w, |w, var| var.default_write(w)) ? ;
      while let Some(term) = lhs.next() {
        write!(w, " ") ? ;
        term.write(w, |w, var| var.default_write(w)) ?
      }
      write!(w, ") ") ? ;
      self.rhs.write(w, |w, var| var.default_write(w)) ? ;
      write!(w, ")") ?
    } else {
      self.rhs.write(w, |w, var| var.default_write(w)) ?
    }
    write!(w, ")") ? ;
    Ok(())
  }
}




/// Wrapper around a negated conjunction for smt printing.
struct NegConj<Terms> {
  /// Terms.
  terms: ::std::cell::RefCell<Terms>,
}
impl<Terms> NegConj<Terms> {
  /// Constructor.
  pub fn new(terms: Terms) -> Self {
    NegConj { terms: ::std::cell::RefCell::new(terms) }
  }
}
impl<'a, Terms> ::rsmt2::to_smt::Expr2Smt<()> for NegConj<Terms>
where Terms: Iterator<Item = & 'a Term> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    let mut terms = self.terms.borrow_mut() ;
    write!(w, "(not ") ? ;
    if let Some(term) = terms.next() {
      write!(w, "(and") ? ;
      write!(w, " ") ? ;
      term.write(w, |w, var| var.default_write(w)) ? ;
      while let Some(term) = terms.next() {
        write!(w, " ") ? ;
        term.write(w, |w, var| var.default_write(w)) ?
      }
      write!(w, ")") ?
    } else {
      write!(w, "false") ?
    }
    write!(w, ")") ? ;
    Ok(())
  }
}


/// Wraps a solver to provide helper functions.
pub struct SolverWrapper<S> {
  /// The solver.
  solver: S,
}
impl<'kid, S: Solver<'kid, ()>> SolverWrapper<S> {
  /// Constructor.
  pub fn new(solver: S) -> Self {
    SolverWrapper {
      solver // , new_vars: VarSet::with_capacity(17),
    }
  }

  /// True if a conjunction of terms is a tautology.
  ///
  /// True if `terms.is_empty()`.
  pub fn trivial_conj<'a, Terms>(
    & mut self, vars: & VarMap<VarInfo>, terms: Terms
  ) -> Res<bool>
  where Terms: Iterator<Item = & 'a Term> {
    self.solver.push(1) ? ;
    for var in vars {
      if var.active {
        self.solver.declare_const(& var.idx, & var.typ) ?
      }
    }
    self.solver.assert( & NegConj::new(terms) ) ? ;
    let sat = self.solver.check_sat() ? ;
    self.solver.pop(1) ? ;
    Ok(! sat)
  }

  /// True if an implication of terms is a tautology.
  pub fn trivial_impl<'a, Terms>(
    & mut self, vars: & VarMap<VarInfo>, lhs: Terms, rhs: & 'a Term
  ) -> Res<bool>
  where Terms: Iterator<Item = & 'a Term> {
    self.solver.push(1) ? ;
    for var in vars {
      if var.active {
        self.solver.declare_const(& var.idx, & var.typ) ?
      }
    }
    self.solver.assert( & NegImplWrap::new(lhs, rhs) ) ? ;
    let sat = self.solver.check_sat() ? ;
    self.solver.pop(1) ? ;
    Ok(! sat)
  }
}

/// Wraps an instance for pre-processing.
pub struct PreInstance<'a, Slver> {
  /// The instance wrapped.
  instance: & 'a mut Instance,
  /// Solver used for triviality-checking.
  solver: Slver,
  /// Clause simplifier.
  simplifier: ClauseSimplifier,
  /// The term `false`, here for convenience in `is_clause_trivial`.
  fls: Term,
  /// Factored vector of clauses to check for simplification.
  ///
  /// Be **super careful** of swap removes.
  clauses_to_check: ClsSet,
  /// Factored vector of clauses to simplify.
  clauses_to_simplify: Vec<ClsIdx>,
}
impl<'a, 'skid, Slver> PreInstance< 'a, SolverWrapper<Slver> >
where Slver: Solver<'skid, ()> {
  /// Constructor.
  pub fn new(
    instance: & 'a mut Instance,
    solver: SolverWrapper<Slver>,
  ) -> Self {
    let simplifier = ClauseSimplifier::new() ;
    let fls = term::fls() ;
    let clauses_to_check = ClsSet::with_capacity(7) ;
    let clauses_to_simplify = Vec::with_capacity(7) ;
    PreInstance {
      instance, solver, simplifier,
      fls, clauses_to_check, clauses_to_simplify
    }
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
            info += self.instance.internal_force_false( Some(pred) ) ?
          } else if self.instance.pred_to_clauses[pred].0.is_empty() {
            info.preds += 1 ;
            fixed_point = false ;
            info += self.instance.internal_force_true( Some(pred) ) ?
          }
        }
      }
    }
    Ok(info)
  }




  /// Simplifies some clauses.
  ///
  /// Can change **all** clause indices because of potential swap removes.
  fn simplify_clauses(& mut self) -> Res<RedInfo> {
    let mut info = RedInfo::new() ;
    // Sort highest to lowest to avoid problems with swap removes.
    self.clauses_to_simplify.sort_unstable_by(
      |c_1, c_2| c_2.cmp( c_1 )
    ) ;
    while let Some(clause) = self.clauses_to_simplify.pop() {
      info += self.simplify_clause(clause) ?
    }
    self.check("after `simplify_clauses`") ? ;
    info += self.force_trivial() ? ;
    Ok(info)
  }


  /// Simplifies a clause, returns `true` if it was (swap) removed.
  ///
  /// This function might create new clauses. Potentially voids the semantics
  /// of clause indices *after* `clause`. Modifying this function by making it
  /// void clause indices *before* `clause` will break the whole
  /// pre-processing.
  fn simplify_clause(& mut self, clause: ClsIdx) -> Res<RedInfo> {
    macro_rules! rm_return {
      ($clause:ident if $should_remove:expr) => (
        if $should_remove {
          self.instance.forget_clause(clause) ? ;
          return Ok( RedInfo::of_clauses_rmed(1) )
        }
      ) ;
    }

    // Propagate.
    rm_return! {
      clause if self.simplifier.clause_propagate(
        & mut self.instance[clause]
      ) ?
    }
    // Check for triviality.
    rm_return! {
      clause if self.is_clause_trivial(clause) ?
    }

    // Try to split the clause.
    self.split_disj(clause)
  }

  /// Splits disjunctions.
  ///
  /// Splits a clause if it contains exactly one disjunction, if if it's rhs
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
        clause!(clause_idx).insert_term(kid) ;
        info += self.simplify_clause( clause_idx ) ? ;

        for kid in kids {
          let mut clause = clause!(clause).clone() ;
          clause.insert_term(kid) ;
          let this_clause_idx = self.instance.clauses.next_index() ;
          self.instance.push_clause(clause) ? ;
          info += self.simplify_clause( this_clause_idx ) ?
        }
        Ok(info)
      } else {
        Ok(info)
      }
    } else {
      Ok(info)
    }
  }

  /// Checks whether a clause is trivial.
  ///
  /// Returns true if
  ///
  /// - the terms in the lhs are equivalent to `false`, or
  /// - the rhs is a predicate application contained in the lhs.
  fn is_clause_trivial(& mut self, clause: ClsIdx) -> Res<bool> {
    let mut lhs: Vec<& Term> = Vec::with_capacity(17) ;
    let clause = & self.instance[clause] ;

    for term in clause.lhs_terms() {
      match term.bool() {
        Some(true) => (),
        Some(false) => return Ok(true),
        _ => {
          let neg = term::not( term.clone() ) ;
          for term in & lhs {
            if neg == ** term {
              return Ok(true)
            }
          }
          lhs.push( term )
        },
      }
    }

    if clause.rhs().is_none() && clause.lhs_preds().is_empty() {

      // Either it is trivial, or falsifiable regardless of the predicates.
      if self.solver.trivial_impl(
        clause.vars(), lhs.drain(0..), & self.fls
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
      } else if self.solver.trivial_impl(
        clause.vars(), lhs.drain(0..), & self.fls
      ) ? {
        Ok(true)
      } else {
        Ok(false)
      }

    }

  }







  /// Checks the underlying instance is correct.
  pub fn check(& self, blah: & 'static str) -> Res<()> {
    debug_assert! { self.clauses_to_check.is_empty() }
    self.instance.check(blah)
  }











  /// Forces a predicate to be equal to something.
  ///
  /// Does not impact `pred_to_clauses`.
  fn force_pred(
    & mut self, pred: PrdIdx, qualf: Option<Qualf>, tterms: TTerms
  ) -> Res<()> {
    log_debug!("forcing {}", self.instance[pred]) ;
    if let Some(_) = self.instance.pred_terms[pred].as_ref() {
      bail!(
        "[bug] trying to force predicate {} twice\n{}\n{} qualifier(s)",
        conf.sad(& self.instance[pred].name),
        tterms, qualf.map(|q| q.len()).unwrap_or(0)
      )
    }
    if let Some(_) = self.instance.pred_qterms[pred].as_ref() {
      bail!(
        "trying to force predicate {} twice\n{}\n{} qualifier(s)",
        conf.sad(& self.instance[pred].name),
        tterms, qualf.map(|q| q.len()).unwrap_or(0)
      )
    }
    if let Some(qualf) = qualf {
      self.instance.pred_qterms[pred] = Some( (qualf, tterms) )
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

    self.force_pred( pred, None, TTerms::fls() ) ? ;

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
      self.instance.clauses[clause].rhs = None
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

    self.force_pred( pred, None, TTerms::tru() ) ? ;

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
      let prev = self.instance.clauses[* clause].lhs_preds.remove(& pred) ;
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
    pred_apps: Vec<(PrdIdx, VarMap<Term>)>,
    terms: HConSet<Term>,
  ) -> Res<RedInfo> {
    self.check("before `force_pred_left`") ? ;

    let mut info = RedInfo::new() ;

    log_debug! {
      "  force pred left on {}...", conf.emph(& self.instance[pred].name)
    }

    // Forget the rhs clause.
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_rhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    if let Some(clause) = self.clauses_to_simplify.pop() {

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

      info.clauses_rmed += 1 ;
      self.instance.forget_clause(clause) ? ;
      ()
    } else {
      bail!(
        "illegal context for `force_pred_left`, \
        {} appears in no rhs", conf.emph(
          & self.instance[pred].name
        )
      )
    }

    // Update lhs clauses.
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_rhs(
      pred, & mut self.clauses_to_simplify
    ) ;

    'clause_iter: for clause in & self.clauses_to_simplify {
      let clause = * clause ;
      log_debug! {
        "    working on lhs of clause {}",
        self.instance[clause].to_string_info(
          self.instance.preds()
        ).unwrap()
      }

      let argss = if let Some(
        argss
      ) = self.instance.clauses[clause].lhs_preds.remove(& pred) {
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

        for term in & terms {
          if let Some((term, _)) = term.subst_total( & (& args, & qual_map) ) {
            self.instance.clause_add_lhs_term(clause, term)
          } else {
            bail!("error during total substitution in `force_pred_left`")
          }
        }

        for & (pred, ref app_args) in & pred_apps {
          let mut nu_args = VarMap::with_capacity( args.len() ) ;
          for arg in app_args {
            if let Some((arg, _)) = arg.subst_total(
              & (& args, & qual_map)
            ) {
              nu_args.push(arg)
            }
          }
          self.instance.clause_add_lhs_pred(clause, pred, nu_args)
        }
      }

      log_debug! {
        "    done with clause: {}",
        self.instance[clause].to_string_info(
          self.instance.preds()
        ).unwrap()
      }

    }

    // Actually force the predicate.
    let mut tterms = Vec::with_capacity(
      pred_apps.len() + terms.len()
    ) ;
    for (pred, args) in pred_apps {
      tterms.push( TTerm::P { pred, args } )
    }
    for term in terms {
      tterms.push( TTerm::T(term) )
    }
    let tterms = TTerms::conj(tterms) ;
    self.force_pred(pred, Qualf::exists(qvars), tterms) ? ;

    self.check("after `force_pred_left`") ? ;

    // Simplify the clauses we just updated.
    info += self.simplify_clauses() ? ;

    Ok(info)
  }




  /// Forces all lhs occurrences of a predicate to be replaced by a DNF.
  ///
  /// - only legal if `pred` does not appear in any rhs
  /// - in general, will create new clauses
  /// - if `def` is empty, equivalent to `force_false`
  /// - simplifies all clauses impacted
  ///
  /// Used by `GraphRed`.
  pub fn force_dnf_left(
    & mut self, pred: PrdIdx, def: Vec< (Quantfed, Vec<TTerm>) >
  ) -> Res<RedInfo> {
    if def.is_empty() {
      return self.force_false(pred)
    }
    let mut info = RedInfo::new() ;

    self.check("before `force_dnf_left`") ? ;

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
      // This is why we rev-sorted ~~vvvvvvvvvvvvvvvvvvvvv
      let mut clause = self.instance.forget_clause(clause) ? ;

      let pred_argss = if let Some(
        argss
      ) = clause.lhs_preds.remove(& pred) {
        argss
      } else {
        bail!("inconsistent instance state")
      } ;

      // This vector maps indices from `pred_argss` to the disjuncts of `def`.
      let mut def_indices = vec![ 0 ; pred_argss.len() ] ;

      let mut is_done = false ;

      while ! is_done {
        let mut clause = clause.clone() ;

        for arg_idx in 0..def_indices.len() {
          let def_idx = def_indices[arg_idx] ;
          let args = & pred_argss[arg_idx] ;
          let (ref qvars, ref conj) = def[def_idx] ;

          let quant_map = clause.fresh_vars_for(& qvars) ;

          for tterm in conj {
            let tterm = tterm.subst_total( & (args, & quant_map) ) ? ;
            clause.lhs_insert(tterm) ;
          }
        }

        // This is a bit dangerous as we're inside a loop iterating over some
        // clause indices `for clause in clauses_to_rm { ... }`.
        //
        // It's fine here since by construction, `this_clause` is at the end of
        // the clause list, meaning simplifying it will not impact other
        // clauses.
        let this_clause = self.instance.clauses.next_index() ;
        self.instance.push_clause(clause) ? ;
        info += self.simplify_clause(this_clause) ? ;

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
    self.force_pred( pred, None, TTerms::dnf(def) ) ? ;

    self.check("after `force_dnf_left`") ? ;

    info += self.force_trivial() ? ;

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
    pred_app: Option< (PrdIdx, VarMap<Term>) >,
    pred_apps: Vec<(PrdIdx, VarMap<Term>)>, terms: HConSet<Term>
  ) -> Res<RedInfo> {
    self.check("before `force_pred_right`") ? ;

    let mut info = RedInfo::new() ;

    log_debug! {
      "  force pred right on {}...", conf.emph(& self.instance[pred].name)
    }

    // Make sure there's exactly one lhs clause for `pred`.
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_lhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    if let Some(clause) = self.clauses_to_simplify.pop() {
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
      self.instance.forget_clause(clause) ? ;
      ()
    } else {
      bail!(
        "illegal context for `force_pred_right`, \
        {} appears in no lhs",
        conf.emph(& self.instance[pred].name)
      )
    }

    // Update rhs clauses.
    debug_assert! { self.clauses_to_simplify.is_empty() }
    self.instance.unlink_pred_rhs(
      pred, & mut self.clauses_to_simplify
    ) ;
    let mut rhs_swap ;

    'clause_iter: for clause in & self.clauses_to_simplify {
      let clause = * clause ;
      log_debug!{ "    working on clause #{}", clause }

      rhs_swap = None ;
      ::std::mem::swap(
        & mut self.instance.clauses[clause].rhs, & mut rhs_swap
      ) ;

      if let Some((prd, subst)) = rhs_swap {
        let qual_map = self.instance.clauses[clause].fresh_vars_for(& qvars) ;

        if pred == prd {

          log_debug! { "      generating new rhs" }

          // New rhs.
          if let Some( & (ref prd, ref args) ) = pred_app.as_ref() {
            let (prd, mut args) = (* prd, args.clone()) ;
            for arg in & mut args {
              if let Some((nu_arg, _)) = arg.subst_total(
                & (& subst, & qual_map)
              ) {
                * arg = nu_arg
              } else {
                bail!("unexpected failure during total substitution")
              }
            }

            self.instance.clause_force_rhs(clause, prd, args)
          }
          // No `else`, clause's rhs is already `None`.

          log_debug! { "      generating new lhs pred apps" }

          // New lhs predicate applications.
          for & (pred, ref args) in & pred_apps {
            let mut nu_args = VarMap::with_capacity( args.len() ) ;
            for arg in args {
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
          
          log_debug! { "      generating new lhs terms" }

          // New lhs terms.
          for term in & terms {
            if let Some((term, _)) = term.subst_total(
              & (& subst, & qual_map)
            ) {
              self.instance.clause_add_lhs_term(clause, term)
            }
          }

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

    // Actually force the predicate.
    let mut neg_tterms = Vec::with_capacity(
      pred_apps.len() + terms.len()
    ) ;
    for (pred, args) in pred_apps {
      neg_tterms.push( TTerm::P { pred, args } )
    }
    for term in terms {
      neg_tterms.push( TTerm::T(term) )
    }
    let tterms = TTerms::disj(
      if let Some((pred, args)) = pred_app {
        vec![ TTerm::P { pred, args } ]
      } else { vec![] },
      neg_tterms
    ) ;
    self.force_pred(pred, Qualf::forall(qvars), tterms) ? ;

    self.check("after `force_pred_right`") ? ;

    info += self.force_trivial() ? ;

    Ok(info)
  }


}

