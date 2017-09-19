//! Actual instance structure.

use common::* ;
use instance::info::* ;

/// A clause.
///
/// Fields are public because a clause is important only if it's in the
/// instance, from which it can only be accessed immutably.
///
/// # Invariants
///
/// - if `! vars[var].active`, then `var` does not appear in `lhs` or `rhs`
#[derive(Clone)]
pub struct Clause {
  /// Variables of the clause.
  pub vars: VarMap<VarInfo>,
  /// Terms of the left-hand side.
  lhs_terms: HConSet<RTerm>,
  /// Predicate applications of the left-hand side.
  lhs_preds: PredApps,
  /// Single term right-hand side.
  rhs: TTerm,
}
impl Clause {
  /// Creates a clause.
  pub fn new(
    vars: VarMap<VarInfo>, lhs: Vec<TTerm>, rhs: TTerm
  ) -> Self {
    let lhs_terms = HConSet::with_capacity( lhs.len() ) ;
    let lhs_preds = PredApps::with_capacity( lhs.len() ) ;
    let mut clause = Clause { vars, lhs_terms, lhs_preds, rhs } ;
    for tterm in lhs { clause.lhs_insert(tterm) ; }
    clause.lhs_terms.shrink_to_fit() ;
    clause.lhs_preds.shrink_to_fit() ;
    clause
  }

  /// Checks a clause is well-formed.
  #[cfg(debug_assertions)]
  pub fn check(& self, blah: & 'static str) -> Res<()> {
    use std::iter::Extend ;
    let mut vars = VarSet::with_capacity( self.vars.len() ) ;
    for term in & self.lhs_terms {
      vars.extend( term.vars() )
    }
    for (_, argss) in & self.lhs_preds {
      for args in argss {
        for arg in args {
          vars.extend( arg.vars() )
        }
      }
    }
    vars.extend( self.rhs.vars() ) ;
    for var in vars {
      if ! self.vars[var].active {
        bail!(
          "ill-formed clause: {}, \
          variable {} appears in the clause but is not active",
          blah, self[var]
        )
      }
    }
    Ok(())
  }
  #[cfg(not(debug_assertions))]
  #[inline(always)]
  pub fn check(& self, _: & 'static str) -> Res<()> {
    Ok(())
  }

  /// Deactivates a variable.
  pub fn deactivate(& mut self, var: VarIdx) -> Res<()> {
    debug_assert!( self.vars[var].active ) ;
    self.vars[var].active = false ;
    self.check( "after `deactivate`" )
  }

  /// Inserts a top term in the lhs. Returns true if it was not there.
  #[inline(always)]
  pub fn lhs_insert(& mut self, tterm: TTerm) -> bool {
    match tterm {
      TTerm::T(term) => self.insert_term(term),
      TTerm::P { pred, args } => self.insert_pred_app(pred, args),
    }
  }

  /// Inserts a predicate application in the LHS.
  ///
  /// Returns true if the predicate application is new.
  #[inline(always)]
  pub fn insert_pred_app(
    & mut self, pred: PrdIdx, args: VarMap<Term>
  ) -> bool {
    self.lhs_preds.insert_pred_app(pred, args)
  }

  /// Inserts a term in an LHS. Externalized for ownership reasons.
  fn lhs_insert_term(lhs_terms: & mut HConSet<RTerm>, term: Term) -> bool {
    if let Some(kids) = term.and_inspect() {
      let mut new_stuff = false ;
      let mut stack = vec![] ;
      for kid in kids {
        if let Some(kids) = kid.and_inspect() {
          for kid in kids { stack.push(kid) }
        } else {
          let is_new = lhs_terms.insert( kid.clone() ) ;
          new_stuff = new_stuff || is_new
        }
      }
      while let Some(term) = stack.pop() {
        if let Some(kids) = term.and_inspect() {
          for kid in kids { stack.push(kid) }
        } else {
          let is_new = lhs_terms.insert( term.clone() ) ;
          new_stuff = new_stuff || is_new
        }
      }
      return new_stuff
    }
    // Only reachable when `term.and_inspect()` is `None`. Needs to be outside
    // the match because of lexical lifetimes.
    lhs_terms.insert(term)
  }

  /// Inserts a term in the LHS.
  pub fn insert_term(& mut self, term: Term) -> bool {
    Self::lhs_insert_term(& mut self.lhs_terms, term)
  }

  /// Length of a clause's LHS.
  #[inline(always)]
  pub fn lhs_len(& self) -> usize {
    self.lhs_terms.len() + self.lhs_preds.len()
  }
  /// True if the clause's LHS is empty.
  #[inline(always)]
  pub fn lhs_is_empty(& self) -> bool {
    self.lhs_terms.is_empty() && self.lhs_preds.is_empty()
  }

  /// LHS accessor (terms).
  #[inline(always)]
  pub fn lhs_terms(& self) -> & HConSet<RTerm> {
    & self.lhs_terms
  }
  /// LHS accessor (predicate applications).
  #[inline(always)]
  pub fn lhs_preds(& self) -> & PredApps {
    & self.lhs_preds
  }
  /// Number of predicate applications in the lhs (>= number of predicates).
  pub fn lhs_pred_apps_len(& self) -> usize {
    let mut sum = 0 ;
    for argss in self.lhs_preds.values() {
      sum += argss.len()
    }
    sum
  }
  /// RHS accessor.
  #[inline(always)]
  pub fn rhs(& self) -> & TTerm {
    & self.rhs
  }

  /// Variables accessor.
  #[inline(always)]
  pub fn vars(& self) -> & VarMap<VarInfo> {
    & self.vars
  }

  /// Clones a clause but changes the rhs.
  #[inline(always)]
  pub fn clone_with_rhs(& self, rhs: TTerm) -> Self {
    Clause {
      vars: self.vars.clone(),
      lhs_terms: self.lhs_terms.clone(),
      lhs_preds: self.lhs_preds.clone(),
      rhs,
    }
  }



  /// Variable substitution.
  ///
  /// Returns a boolean indicating whether any substitution occured.
  ///
  /// Used for substitutions in the same clause / predicate scope.
  pub fn subst<Map: VarIndexed<Term>>(
    & mut self, map: & Map
  ) -> bool {
    let mut changed = false ;
    let mut lhs_terms = HConSet::with_capacity( self.lhs_terms.len() ) ;
    ::std::mem::swap(& mut lhs_terms, & mut self.lhs_terms) ;
    for term in lhs_terms.drain() {
      let (term, b) = term.subst(map) ;
      self.insert_term(term) ;
      changed = changed || b
    }
    let mut nu_argss = HashSet::with_capacity(7) ;
    for (_, argss) in & mut self.lhs_preds {
      debug_assert!( nu_argss.is_empty() ) ;
      for mut args in argss.drain() {
        for arg in args.iter_mut() {
          let (nu_arg, b) = arg.subst(map) ;
          * arg = nu_arg ;
          changed = changed || b
        }
        nu_argss.insert(args) ;
      }
      ::std::mem::swap(& mut nu_argss, argss)
    }
    let rhs_changed = self.rhs.subst(map) ;
    changed = changed || rhs_changed ;
    changed
  }

  // /// Replaces a predicate application by some top terms.
  // ///
  // /// Does not preserve the order of the top terms.
  // pub fn subst_top(& mut self, pred: PrdIdx, top) -> 

  /// Writes a clause given a special function to write predicates.  
  fn write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    use common::consts::keywords ;

    write!(w, "({} ({}\n  (", keywords::assert, keywords::forall) ? ;
    let mut inactive = 0 ;
    for var in & self.vars {
      if var.active {
        write!(w, " ({} {})", var.name, var.typ) ?
      } else {
        inactive += 1 ;
      }
    }
    write!(w, " )") ? ;
    if inactive > 0 {
      write!(w, " ; {} inactive variable(s)", inactive) ?
    }
    write!(w, "\n") ? ;

    let lhs_len = self.lhs_len() ;

    let (pref, suff) = if lhs_len != 0 {
      write!(w, "  (=>") ? ;
      let (pref, suff) = if lhs_len > 1 {
        write!(w, "\n    (and") ? ;
        ("      ", Some("    )"))
      } else {
        ("    ", None)
      } ;

      for term in & self.lhs_terms {
        write!(w, "\n{}", pref) ? ;
        term.write(w, |w, var| w.write_all( self.vars[var].as_bytes() )) ?
      }
      for (pred, argss) in & self.lhs_preds {
        for args in argss {
          write!(w, "\n{}", pref) ? ;
          write_prd(w, * pred, args) ?
        }
      }

      write!(w, "\n") ? ;
      if let Some(suff) = suff {
        write!(w, "{}\n", suff) ?
      }
      ("    ", Some("  )"))
    } else {
      ("  ", None)
    } ;

    write!(w, "{}", pref) ? ;
    self.rhs.write(
      w, |w, var| w.write_all( self.vars[var].as_bytes() ), & write_prd
    ) ? ;
    write!(w, "\n") ? ;
    if let Some(suff) = suff {
      write!(w, "{}", suff) ?
    }
    write!(w, "\n))")
  }
}
impl ::std::ops::Index<VarIdx> for Clause {
  type Output = VarInfo ;
  fn index(& self, index: VarIdx) -> & VarInfo {
    & self.vars[index]
  }
}
impl<'a> ::rsmt2::Expr2Smt<
  (& 'a PrdSet, & 'a PrdSet, & 'a PrdMap<PrdInfo>)
> for Clause {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, info: & (
      & 'a PrdSet, & 'a PrdSet, & 'a PrdMap<PrdInfo>
    )
  ) -> SmtRes<()> {
    let (ref true_preds, ref false_preds, ref prd_info) = * info ;
    smt_cast_io!{
      "writing clause as smt2" =>
        write!(writer, "(not ") ;
        if self.lhs_is_empty() {
          Ok(())
        } else {
          write!(writer, "(=> (and")
        } ;
        {
          for term in & self.lhs_terms {
            smtry_io!(
              "writing clause's lhs terms" =>
              writer.write_all( " ".as_bytes() ) ;
              term.write( writer, |w, var| var.default_write(w) )
            )
          }
          for (pred, argss) in & self.lhs_preds {
            if true_preds.contains(pred) {
              smtry_io!( "true" => writer.write_all( " true".as_bytes() ) )
            } else if false_preds.contains(pred) {
              smtry_io!( "false" => writer.write_all( " false".as_bytes() ) )
            } else {
              for args in argss {
                smtry_io!(
                  "writing clause's lhs" =>
                  writer.write_all( " (".as_bytes() ) ;
                  writer.write_all( prd_info[* pred].name.as_bytes() )
                ) ;
                for arg in args {
                  smtry_io!(
                    "writing clause's lhs" =>
                    writer.write_all( " ".as_bytes() ) ;
                    arg.write(writer, |w, var| var.default_write(w))
                  )
                }
                smtry_io!(
                  "writing clause's lhs" => writer.write_all( ")".as_bytes() )
                )
              }
            }
          }
          Ok(()) as IoRes<()>
        } ;
        if self.lhs_is_empty() { Ok(()) } else {
          write!(writer, ") ")
        } ;
        self.rhs.write_smt2(
          writer, |w, prd, args| {
            if true_preds.contains(& prd) {
              write!(w, "true")
            } else if false_preds.contains(& prd) {
              write!(w, "false")
            } else {
              write!(w, "({}", prd_info[prd].name) ? ;
              for arg in args {
                write!(w, " ") ? ;
                arg.write(w, |w, var| var.default_write(w)) ?
              }
              write!(w, ")")
            }
          }
        ) ;
        if self.lhs_is_empty() { Ok(()) } else {
          write!(writer, ")")
        } ;
        write!(writer, ")")
    }
  }
}




/// Stores the instance: the clauses, the factory and so on.
///
/// # NB
///
/// Clause indices can vary during instance building, because of the
/// simplifications that can remove clauses.
///
/// So, `pred_to_clauses` has to be carefully maintained, the easiest way to
/// do this is to never access an instance's fields directly from the outside.
pub struct Instance {
  /// Constants constructed so far.
  consts: HConSet<RTerm>,
  /// Predicates.
  preds: PrdMap<PrdInfo>,
  /// Predicates for which a suitable term has been found.
  pred_terms: PrdMap< Option< TTerms > >,
  /// Predicates defined in `pred_terms`, sorted by predicate dependencies.
  ///
  /// Populated by the `finalize` function.
  sorted_pred_terms: Vec<PrdIdx>,
  /// Max arity of the predicates.
  pub max_pred_arity: Arity,
  /// Clauses.
  clauses: ClsMap<Clause>,
  /// Maps predicates to the clauses where they appear in the lhs and rhs
  /// respectively.
  pred_to_clauses: PrdMap< (ClsSet, ClsSet) >,
  /// Maps clauses to the predicates appearing in them.
  clause_to_preds: ClsMap< (PrdSet, Option<PrdIdx>) >,
  /// Clause simplifier.
  simplifier: ClauseSimplifier,
}
impl Instance {
  /// Instance constructor.
  pub fn new() -> Instance {
    let pred_capa = conf.instance.pred_capa ;
    let clause_capa = conf.instance.clause_capa ;
    let mut instance = Instance {
      consts: HConSet::with_capacity(103),
      preds: PrdMap::with_capacity(pred_capa),
      pred_terms: PrdMap::with_capacity(pred_capa),
      sorted_pred_terms: Vec::with_capacity(pred_capa),
      max_pred_arity: 0.into(),
      clauses: ClsMap::with_capacity(clause_capa),
      pred_to_clauses: PrdMap::with_capacity(pred_capa),
      clause_to_preds: ClsMap::with_capacity(clause_capa),
      simplifier: ClauseSimplifier::new(),
    } ;
    // Create basic constants, adding to consts to have mining take them into account.
    let (wan,too) = (term::one(), term::zero()) ;
    instance.consts.insert(wan) ;
    instance.consts.insert(too) ;
    instance
  }

  /// Returns the model corresponding to the input predicates and the forced
  /// predicates.
  ///
  /// The model is sorted in topological order.
  pub fn model_of(& self, candidates: Candidates) -> Res<Model> {
    use std::iter::Extend ;
    let mut res = Model::with_capacity( self.preds.len() ) ;
    res.extend(
      candidates.into_index_iter().filter_map(
        |(pred, tterms_opt)| tterms_opt.map(
          |term| (pred, TTerms::of_tterm( TTerm::T(term) ))
        )
      )
    ) ;
    for pred in & self.sorted_pred_terms {
      let pred = * pred ;
      if let Some(ref tterms) = self.pred_terms[pred] {
        res.push( (pred, tterms.clone()) )
      } else {
        bail!("inconsistency in sorted forced predicates")
      }
    }
    Ok(res)
  }

  /// Returns a model for the instance when all the predicates have terms
  /// assigned to them.
  pub fn is_trivial(& self) -> Res< Option<Model> > {
    for term_opt in & self.pred_terms {
      if term_opt.is_none() { return Ok(None) }
    }
    // Only reachable if all elements of `self.pred_terms` are `Some(_)`.
    self.model_of( vec![].into() ).map(|res| Some(res))
  }


  /// Clauses a predicate appears in. Lhs and rhs.
  pub fn clauses_of_pred(& self, pred: PrdIdx) -> ( & ClsSet, & ClsSet ) {
    ( & self.pred_to_clauses[pred].0, & self.pred_to_clauses[pred].1 )
  }
  /// Clauses a predicate appears in. Lhs and rhs.
  pub fn preds_of_clause(
    & self, clause: ClsIdx
  ) -> ( & PrdSet, Option<PrdIdx> ) {
    (& self.clause_to_preds[clause].0, self.clause_to_preds[clause].1)
  }


  /// Prints some top terms as a model.
  ///
  /// Meaning variables are printed with default printing: `<var_idx>` is
  /// printed as `v_<var_idx>`.
  pub fn print_tterms_as_model<W: Write>(
    & self, w: & mut W, tterms: & TTerms
  ) -> ::std::io::Result<()> {
    tterms.write(
      w, |w, var| var.default_write(w),
      |w, pred, args| {
        write!(w, "({}", self[pred]) ? ;
        for arg in args {
          write!(w, " {}", arg) ?
        }
        write!(w, ")")
      }
    )
  }

  /// Finalizes instance creation.
  ///
  /// - shrinks all collections
  /// - sorts forced predicates by dependencies
  ///
  /// # TO DO
  ///
  /// - optimize sorting of forced preds by dependencies (low priority)
  pub fn finalize(& mut self) {
    self.consts.shrink_to_fit() ;
    self.preds.shrink_to_fit() ;
    self.pred_terms.shrink_to_fit() ;
    self.clauses.shrink_to_fit() ;

    let mut tmp: Vec< (PrdIdx, PrdSet) > = Vec::with_capacity(
      self.preds.len()
    ) ;

    // Populate `sorted_pred_terms`.
    for (pred, tterms) in self.pred_terms.index_iter() {
      if let Some(ref tterms) = * tterms {
        tmp.push( (pred, tterms.preds()) )
      }
    }

    // Sort by dependencies.
    let mut known_preds = PrdSet::with_capacity( self.preds.len() ) ;
    for (pred, want_none) in self.pred_terms.index_iter() {
      if want_none.is_none() { known_preds.insert(pred) ; () }
    }
    while ! tmp.is_empty() {
      let mut cnt = 0 ; // Will use swap remove.
      'find_preds: while cnt < tmp.len() {
        for pred in & tmp[cnt].1 {
          if ! known_preds.contains(pred) {
            // Don't know this predicate, keep going in `tmp`.
            cnt += 1 ;
            continue 'find_preds
          }
        }
        // Reachable only we already have all of the current pred's
        // dependencies.
        let (pred, _) = tmp.swap_remove(cnt) ;
        self.sorted_pred_terms.push(pred) ;
        known_preds.insert(pred) ;
        () // No `cnt` increment after swap remove.
      }
    }

    self.sorted_pred_terms.shrink_to_fit()
  }


  /// Returns the term we already know works for a predicate, if any.
  pub fn forced_terms_of(& self, pred: PrdIdx) -> Option<& TTerms> {
    self.pred_terms[pred].as_ref()
  }

  /// If the input predicate is forced to a constant boolean, returns its
  /// value.
  pub fn bool_value_of(& self, pred: PrdIdx) -> Option<bool> {
    self.forced_terms_of(pred).and_then(
      |terms| terms.bool()
    )
  }

  /// Forced predicates in topological order.
  pub fn sorted_forced_terms(& self) -> & Vec<PrdIdx> {
    & self.sorted_pred_terms
  }

  /// Returns the clauses in which the predicate appears in the lhs and rhs
  /// respectively.
  pub fn clauses_of(& self, pred: PrdIdx) -> (& ClsSet, & ClsSet) {
    (& self.pred_to_clauses[pred].0, & self.pred_to_clauses[pred].1)
  }

  /// Adds some terms to the lhs of a clause.
  ///
  /// Updates `pred_to_clauses`.
  pub fn clause_lhs_extend<I: IntoIterator<Item = TTerm>>(
    & mut self, clause_idx: ClsIdx, tterms: I
  ) {
    let clause = & mut self.clauses[clause_idx] ;
    for tterm in tterms.into_iter() {
      match tterm {
        TTerm::P { pred, args } => {
          self.pred_to_clauses[pred].0.insert(clause_idx) ;
          self.clause_to_preds[clause_idx].0.insert(pred) ;
          clause.insert_pred_app(pred, args) ;
        },
        TTerm::T(term) => {
          clause.insert_term(term) ;
        },
      }
    }
  }

  /// Replaces the rhs of a clause.
  pub fn clause_rhs_force(
    & mut self, clause: ClsIdx, tterm: TTerm
  ) {
    if let TTerm::P { pred, .. } = self.clauses[clause].rhs {
      self.pred_to_clauses[pred].1.remove(& clause) ;
    }
    if let TTerm::P { pred, .. } = tterm {
      self.pred_to_clauses[pred].1.insert(clause) ;
    }
    self.clauses[clause].rhs = tterm
  }

  // /// Evaluates the term a predicate is forced to, if any.
  // pub fn eval_term_of(
  //   & self, pred: PrdIdx, model: & VarMap<Val>
  // ) -> Res< Option<bool> > {
  //   if let Some(term) = self.term_of(pred) {
  //     match term.bool_eval(model) {
  //       Ok(None) => bail!("partial model during predicate term evaluation"),
  //       res => res,
  //     }
  //   } else {
  //     Ok(None)
  //   }
  // }

  /// Set of int constants **appearing in the predicates**. If more constants
  /// are created after the instance building step, they will not appear here.
  pub fn consts(& self) -> & HConSet<RTerm> {
    & self.consts
  }

  /// Range over the predicate indices.
  pub fn pred_indices(& self) -> PrdRange {
    PrdRange::zero_to( self.preds.len() )
  }
  /// Range over the clause indices.
  pub fn clause_indices(& self) -> ClsRange {
    ClsRange::zero_to( self.clauses.len() )
  }

  /// Predicate accessor.
  pub fn preds(& self) -> & PrdMap<PrdInfo> {
    & self.preds
  }
  /// Clause accessor.
  pub fn clauses(& self) -> & ClsMap<Clause> {
    & self.clauses
  }

  /// Removes all predicate applications of some predicate in the lhs of a
  /// clause.
  fn rm_pred_apps_in_lhs(& mut self, pred: PrdIdx, clause: ClsIdx) {
    self.pred_to_clauses[pred].0.remove(& clause) ;
    self.clause_to_preds[clause].0.remove(& pred) ;
    self.clauses[clause].lhs_preds.remove(& pred) ;
  }


  /// Strengthens some predicate by some terms using the clauses lhs where the
  /// predicate appears.
  ///
  /// Returns the number of clauses created.
  ///
  /// Currently pseudo-inactive. Can only remove predicate applications if they
  /// are found to be trivial given the strengthening.
  ///
  /// For all clauses `c` where `pred` appears in the lhs, creates a new clause
  /// that is `c` with every application of `pred` replaced by `tterms`
  /// instantiated on `pred`'s application arguments.
  pub fn strengthen_in_lhs(
    & mut self, pred: PrdIdx, tterms: Vec<TTerm>
  ) -> Res<usize> {
    // let mut nu_clauses = Vec::with_capacity(
    //   self.pred_to_clauses[pred].0.len()
    // ) ;
    let mut nu_tterms = HashSet::with_capacity( 29 ) ;
    let mut pred_apps_to_rm = Vec::with_capacity(11) ;

    'clause_iter: for clause in & self.pred_to_clauses[pred].0 {
      // debug_assert!( nu_tterms.is_empty() ) ;
      nu_tterms.clear() ;

      log_debug!{ "  - #{}", clause }

      if let Some(argss) = self[* clause].lhs_preds.get(& pred) {

        log_debug!{ "    {} applications", argss.len() }
        for args in argss {
          'tterm_iter: for tterm in & tterms {
            let tterm = tterm.subst_total(args) ? ;
            if let Some(b) = tterm.bool() {
              if ! b {
                log_debug!{ "      new clause is trivial, skipping" }
                continue 'clause_iter
              }
            } else {
              match tterm {
                TTerm::T(ref term) if self[
                  * clause
                ].lhs_terms.contains(term) => continue 'tterm_iter,
                TTerm::P { ref pred, ref args } if self[
                  * clause
                ].lhs_preds.get(pred).map(
                  |argss| argss.contains(args)
                ).unwrap_or(false) => continue 'tterm_iter,
                _ => ()
              }
              log_debug!{ "    - {}", tterm }
              nu_tterms.insert( tterm ) ;
            }
          }
        }

      } else {
        bail!(
          "inconsistent instance state \
          (`pred_to_clauses` in `strengthen_in_lhs`)"
        )
      }

      if nu_tterms.is_empty() {
        log_debug!{
          "    no new terms, can remove applications of this predicate"
        }
        pred_apps_to_rm.push( (pred, * clause) )
      } else {
        // let mut nu_clause = self[* clause].clone() ;

        // for tterm in nu_tterms.drain() {
        //   nu_clause.lhs_insert(tterm) ;
        // }

        // let should_remove = self.simplifier.clause_propagate(
        //   & mut nu_clause
        // ) ? ;
        // if should_remove {
        //   log_info!{
        //     "    new clause is trivial after propagation"
        //   }
        // } else {
        //   nu_clauses.push(nu_clause)
        // }
      }

    }

    for (pred, clause) in pred_apps_to_rm {
      self.rm_pred_apps_in_lhs(pred, clause)
    }
    // let count = nu_clauses.len() ;
    // log_info!{ "    adding {} clauses", count }
    // for clause in nu_clauses { self.push_clause(clause) ? }
    self.check("after strengthening (lhs)") ? ;

    // Ok(count)
    Ok(0)
  }

  /// Pushes a new predicate and returns its index.
  pub fn push_pred(
    & mut self, name: String, sig: VarMap<Typ>
  ) -> PrdIdx {
    self.max_pred_arity = ::std::cmp::max(
      self.max_pred_arity, sig.len().into()
    ) ;
    let idx = self.preds.next_index() ;
    self.preds.push( PrdInfo { name, idx, sig } ) ;
    self.pred_terms.push(None) ;
    self.pred_to_clauses.push(
      ( ClsSet::with_capacity(17), ClsSet::with_capacity(17) )
    ) ;
    idx
  }

  /// Forces a predicate to be equal to something.
  ///
  /// Does not impact `pred_to_clauses`.
  fn force_pred(& mut self, pred: PrdIdx, tterms: TTerms) -> Res<()> {
    if let Some(ts) = self.pred_terms[pred].as_ref() {
      if ts != & tterms {
        bail!(
          "[bug] trying to force predicate {} twice",
          conf.sad(& self[pred].name)
        )
      }
    }
    self.pred_terms[pred] = Some(tterms) ;
    Ok(())
  }

  /// Unlinks a predicate from all the clauses it's linked to, and conversely.
  fn drain_unlink_pred(
    & mut self, pred: PrdIdx, lhs: & mut ClsSet, rhs: & mut ClsSet
  ) -> () {
    for clause in self.pred_to_clauses[pred].0.drain() {
      let was_there = self.clause_to_preds[clause].0.remove(& pred) ;
      debug_assert!( was_there ) ;
      let _ = lhs.insert(clause) ;
    }
    for clause in self.pred_to_clauses[pred].1.drain() {
      debug_assert_eq!( self.clause_to_preds[clause].1, Some(pred) ) ;
      self.clause_to_preds[clause].1 = None ;
      let _ = rhs.insert(clause) ;
    }
  }

  /// Goes trough the predicates in `from`, and updates `pred_to_clauses` so
  /// that they point to `to` instead.
  ///
  /// - swaps `clause_to_preds[from]` and `clause_to_preds[to]`
  /// - only legal if `clause_to_preds[to].0.is_empty()` and
  ///   `clause_to_preds[to].1.is_none()`
  fn relink_preds_to_clauses(
    & mut self, from: ClsIdx, to: ClsIdx
  ) -> Res<()> {
    if ! self.clause_to_preds[to].0.is_empty() {
      bail!("illegal relinking, clause `{}` still has lhs links", to)
    }
    if self.clause_to_preds[to].1.is_some() {
      bail!("illegal relinking, clause `{}` is still has an rhs link", to)
    }
    self.clause_to_preds.swap(from, to) ;
    for pred in self.clauses[from].lhs_preds.keys() {
      let pred = * pred ;
      let was_there = self.pred_to_clauses[pred].0.remove(& from) ;
      let _ = self.pred_to_clauses[pred].0.insert(to) ;
      debug_assert!(was_there)
    }
    if let TTerm::P { pred, .. } = * self.clauses[from].rhs() {
      let was_there = self.pred_to_clauses[pred].1.remove(& from) ;
      let _ = self.pred_to_clauses[pred].1.insert(to) ;
      debug_assert!(was_there)
    }
    Ok(())
  }

  // /// Unlinks a predicate from a clause.
  // fn unlink_pred_and_clause(
  //   & mut self, pred: PrdIdx, clause: ClsIdx
  // ) -> Res<()> {
  //   let in_lhs = self.pred_to_clauses[pred].0.remove(& clause) ;
  //   let in_rhs = self.pred_to_clauses[pred].1.remove(& clause) ;
  //   if ! (in_lhs && in_rhs ) {
  //     bail!(
  //       "predicate {} is not linked to clause number {}, failed to unlink",
  //       conf.sad(& self[pred].name), clause
  //     )
  //   } else {
  //     Ok(())
  //   }
  // }

  /// Forget some clauses.
  pub fn forget_clauses(& mut self, mut clauses: Vec<ClsIdx>) -> Res<()> {
    // Forgetting is done by swap remove, so we sort in DESCENDING order so
    // that indices always make sense.
    clauses.sort_unstable_by(
      |c_1, c_2| c_2.cmp(c_1)
    ) ;
    for clause in clauses {
      let _ = self.forget_clause(clause) ? ;
    }
    self.check("after `forget_clause`") ? ;
    Ok(())
  }

  /// Forget a clause. **Does not preserve the order of the clauses.**
  ///
  /// Also unlinks predicates from `pred_to_clauses`.
  pub fn forget_clause(& mut self, clause: ClsIdx) -> Res<Clause> {
    for pred in self.clauses[clause].lhs_preds.keys() {
      let pred = * pred ;
      let was_there = self.pred_to_clauses[pred].0.remove(& clause) ;
      debug_assert!(
        was_there || self.pred_terms[pred].is_some()
      ) ;
      let was_there = self.clause_to_preds[clause].0.remove(& pred) ;
      debug_assert!(
        was_there || self.pred_terms[pred].is_some()
      )
    }
    if let TTerm::P { pred, .. } = * self.clauses[clause].rhs() {
      let was_there = self.pred_to_clauses[pred].1.remove(& clause) ;
      debug_assert!(
        was_there || self.pred_terms[pred].is_some()
      ) ;
      debug_assert!(
        self.clause_to_preds[clause].1 == Some(pred) ||
        self.pred_terms[pred].is_some()
      ) ;
      self.clause_to_preds[clause].1 = None
    }
    // Relink the last clause as its index is going to be `clause`. Except if
    // `clause` is already the last one.
    let last_clause: ClsIdx = ( self.clauses.len() - 1 ).into() ;
    if clause != last_clause {
      self.relink_preds_to_clauses(last_clause, clause) ?
    }
    let res = self.clauses.swap_remove(clause) ;
    let (_lhs, _rhs) = self.clause_to_preds.pop().expect(
      "empty clause_to_preds, illegal internal state"
    ) ;
    debug_assert!( _lhs.is_empty() ) ;
    debug_assert_eq!( _rhs, None ) ;
    // self.check("forgetting clause") ? ;
    Ok(res)
  }

  /// Pushes a new clause.
  pub fn push_clause(& mut self, clause: Clause) -> Res<()> {
    let clause_index = self.clauses.next_index() ;
    let mut lhs_preds = PrdSet::with_capacity( clause.lhs_preds.len() ) ;
    let mut rhs_pred = None ;
    for pred in clause.lhs_preds.keys() {
      let pred = * pred ;
      let is_new = self.pred_to_clauses[pred].0.insert(clause_index) ;
      let is_new_too = lhs_preds.insert(pred) ;
      debug_assert!(is_new) ;
      debug_assert!(is_new_too)
    }
    if let Some(pred) = clause.rhs.pred() {
      rhs_pred = Some(pred) ;
      let is_new = self.pred_to_clauses[pred].1.insert(clause_index) ;
      debug_assert!(is_new)
    }
    self.clause_to_preds.push( (lhs_preds, rhs_pred) ) ;
    self.clauses.push(clause) ;
    self.check("after `push_clause`")
  }


  /// Simplifies a cause. Returns `true` if the clause was (swap) removed.
  pub fn simplify_clause(& mut self, clause: ClsIdx) -> Res<bool> {
    let remove = self.simplifier.clause_propagate(
      & mut self.clauses[clause]
    ).chain_err(
      || format!(
        "on clause {}",
        self.clauses[clause].to_string_info(& self.preds).unwrap()
      )
    ) ? ;
    // log_debug!{ "{}", self.clauses[clause].to_string_info(& self.preds) ? }
    if remove {
      self.clauses.swap_remove(clause) ;
    }
    Ok(remove)
  }



  /// Simplifies the clauses.
  ///
  /// - propagates variable equalities in clauses' lhs
  ///
  /// # TO DO
  ///
  /// - currently kind of assumes equalities are binary, fix?
  pub fn simplify_clauses(& mut self) -> Res<()> {
    let mut clause: ClsIdx = 0.into() ;
    while clause < self.clauses.len() {
      let removed = self.simplify_clause(clause) ? ;
      if ! removed { clause.inc() }
    }

    Ok(())
  }

  /// Extracts some qualifiers from all clauses.
  pub fn qualifiers(& self) -> HConSet<RTerm> {
    let mut set = HConSet::new() ;
    for clause in & self.clauses {
      self.qualifiers_of_clause(clause, & mut set)
    }
    set
  }

  /// Extracts some qualifiers from a clause.
  ///
  /// # TO DO
  ///
  /// - write an explanation of what actually happens
  /// - and some tests, probably
  pub fn qualifiers_of_clause(
    & self, clause: & Clause, quals: & mut HConSet<RTerm>
  ) {
    // println!(
    //   "looking at clause {}", clause.to_string_info(self.preds()).unwrap()
    // ) ;

    // Extraction of the variables map based on the way the predicates are
    // used.
    let mut maps = vec![] ;

    let rhs_opt = if let TTerm::P { ref pred, ref args } = clause.rhs {
      let mut set = HashSet::with_capacity(1) ;
      set.insert(args.clone()) ;
      Some((pred, set))
    } else { None } ;
    let rhs_opt = rhs_opt.as_ref().map( |& (pred, ref set)| (pred, set) ) ;

    for (_, argss) in clause.lhs_preds.iter().chain(rhs_opt.into_iter()) {
      for args in argss {
        // All the *clause var* to *pred var* maps for this predicate
        // application.
        let mut these_maps = vec![ VarHMap::with_capacity( args.len() ) ] ;

        for (pred_var_index, term) in args.index_iter() {
          if let Some(clause_var_index) = term.var_idx() {
            // Stores the new maps to add in case a clause variable is bound
            // several times.
            let mut to_add = vec![] ;
            for map in & mut these_maps {
              if map.contains_key(& clause_var_index) {
                // Current clause variable is already bound in this map,
                // clone it, change the binding, and remember to add it
                // later.
                let mut map = map.clone() ;
                let _ = map.insert(
                  clause_var_index, term::var(pred_var_index)
                ) ;
                to_add.push(map)
              } else {
                // Current clause variable not bound in this map, just add
                // the new binding.
                let _ = map.insert(
                  clause_var_index, term::var(pred_var_index)
                ) ;
              }
            }
            use std::iter::Extend ;
            these_maps.extend( to_add )
          }
        }

        for map in these_maps {
          // Push if non-empty.
          if ! map.is_empty() {
            maps.push(map)
          }
        }
      }
    }

    // println!("maps {{") ;
    // for map in & maps {
    //   let mut is_first = true ;
    //   for (idx, term) in map.iter() {
    //     println!("  {} {} -> {}", if is_first {"-"} else {" "}, idx, term) ;
    //     is_first = false
    //   }
    // }
    // println!("}} quals {{") ;

    // Now look for atoms and try to apply the mappings above.
    for term in clause.lhs_terms.iter().chain( clause.rhs().term() ) {

      for map in & maps {
        if let Some( (term, true) ) = term.subst_total(map) {
          let term = if let Some(term) = term.rm_neg() {
            term
          } else { term } ;
          let _ = quals.insert(term) ;
        }
        // else if let Some(kids) = term.kids() {
        //   for kid in kids {
        //     if kid.is_relation() {
        //       if let Some( (term, true) ) = self.subst_total(map, kid) {
        //         log_info!("-> {}", term) ;
        //         let term = if let Some(term) = term.rm_neg() {
        //           term
        //         } else { term } ;
        //         let _ = quals.insert(term) ;
        //       }
        //     }
        //   }
        // }
      }

    }
    // println!("}}")

  }

  /// Turns a teacher counterexample into learning data.
  pub fn cexs_to_data(
    & self, data: & mut ::common::data::Data, cexs: Cexs
  ) -> Res<()> {

    for (clause, cex) in cexs.into_iter() {
      log_debug!{ "    working on clause {}...", clause }
      let clause = & self[clause] ;
      log_debug!{ "    getting antecedents..." }
      let mut antecedents = Vec::with_capacity( clause.lhs_len() ) ;
      log_debug!{ "    translating tterms..." }


      log_debug!{ "    working on lhs..." }
      for (pred, argss) in & clause.lhs_preds {
        let pred = * pred ;
        log_debug!{
          "        pred: {} / {} ({})",
          pred, self.preds.len(), self.pred_terms.len()
        }
        if self.pred_terms[pred].is_none() {
          log_debug!{ "        -> is none, {} args", argss.len() }
          for args in argss {
            let mut values = VarMap::with_capacity( args.len() ) ;
            for arg in args {
              values.push(
                arg.eval(& cex).chain_err(
                  || "during argument evaluation to generate learning data"
                ) ?
              )
            }
            antecedents.push(
              (pred, values)
            )
          }
        } else {
          log_debug!{ "      -> is some" }
        }
      }
      antecedents.shrink_to_fit() ;
      
      log_debug!{ "    working on rhs..." }
      let consequent = match * clause.rhs() {
        TTerm::P { pred, ref args } => {
          log_debug!{ "        pred: {} / {} ({})", pred, self.preds.len(), self.pred_terms.len() }
          let mut values = VarMap::with_capacity( args.len() ) ;
          'pred_args: for arg in args {
            values.push(
              arg.eval(& cex).chain_err(
                || "during argument evaluation to generate learning data"
              ) ?
            )
          }
          Some( (pred, values) )
        },
        _ => None,
      } ;

      log_debug!{ "    antecedent: {:?}", antecedents }
      log_debug!{ "    consequent: {:?}", consequent }

      match ( antecedents.len(), consequent ) {
        (0, None) => bail!(
          "[unimplemented] clause with no predicate has a cex (unsafe)"
        ),
        (1, None) => {
          let (pred, args) = antecedents.pop().unwrap() ;
          data.stage_raw_neg(pred, args) ?
        },
        (0, Some( (pred, args) )) => data.stage_raw_pos(pred, args) ?,
        (_, consequent) => data.add_cstr(antecedents, consequent) ?,
      }
    }

    Ok(())
  }



  /// Checks that the instance has no inconsistencies.
  ///
  /// Only active in debug.
  #[cfg(not(debug_assertions))]
  #[inline(always)]
  pub fn check(& self, _: & 'static str) -> Res<()> { Ok(()) }

  #[cfg(debug_assertions)]
  pub fn check(& self, s: & 'static str) -> Res<()> {
    self.check_pred_to_clauses().chain_err(
      || format!("while checking `{}`", conf.sad("pred_to_clauses"))
    ).chain_err(
      || format!("instance consistency check failed: {}", conf.emph(s))
    ) ? ;

    self.check_clause_to_preds().chain_err(
      || format!("while checking `{}`", conf.sad("clause_to_preds"))
    ).chain_err(
      || format!("instance consistency check failed: {}", conf.emph(s))
    ) ? ;
    Ok(())
  }

  /// Pretty printer for a set of predicates.
  #[cfg(debug_assertions)]
  fn pretty_preds(& self, preds: & PrdSet) -> String {
    let mut s = String::new() ;
    s.push('{') ;
    for pred in preds {
      s.push(' ') ;
      s.push_str(& self[* pred].name)
    }
    s.push(' ') ;
    s.push('}') ;
    s
  }

  /// Pretty printer for a predicate option.
  #[cfg(debug_assertions)]
  fn pretty_pred_opt(& self, pred: & Option<PrdIdx>) -> String {
    if let Some(pred) = * pred {
      format!("{}", self[pred].name)
    } else {
      "none".into()
    }
  }

  /// Pretty printer for a set of clauses.
  #[cfg(debug_assertions)]
  fn pretty_clauses(& self, clauses: & ClsSet) -> String {
    let mut s = String::new() ;
    s.push('{') ;
    for clause in clauses {
      s.push(' ') ;
      s.push_str(& format!("{}", clause))
    }
    s.push(' ') ;
    s.push('}') ;
    s
  }

  /// Checks the consistency of `pred_to_clauses`.
  #[cfg(debug_assertions)]
  fn check_pred_to_clauses(& self) -> Res<()> {
    for (cls_idx, clause) in self.clauses.index_iter() {
      for (pred, _) in & clause.lhs_preds {
        let pred = * pred ;
        if ! self.pred_to_clauses[pred].0.contains(& cls_idx) {
          bail!(
            "predicate {} appears in lhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
      if let Some(pred) = clause.rhs.pred() {
        if ! self.pred_to_clauses[pred].1.contains(& cls_idx) {
          bail!(
            "predicate {} appears in rhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
    }

    for (pred, & (ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
      'pred_clauses: for clause in lhs {
        if self.clauses[* clause].lhs_preds.get(& pred).is_none() {
          bail!(
            "predicate {} is registered as appearing in lhs of clause {} \
            but it's not the case\n{}\nlhs: {}\nrhs: {}",
            self[pred], clause,
            self.clauses[* clause].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
      for clause in rhs {
        if let Some(this_pred) = self.clauses[* clause].rhs.pred() {
          if this_pred == pred {
            continue
          }
        }
        bail!(
          "predicate {} is registered to appear in rhs of clause {} \
          but it's not the case\n{}\nlhs: {}\nrhs: {}",
          self[pred], clause,
          self.clauses[* clause].to_string_info(self.preds()) ?,
          self.pretty_clauses(
            & self.pred_to_clauses[pred].0
          ), self.pretty_clauses(
            & self.pred_to_clauses[pred].1
          )
        )
      }
    }
    Ok(())
  }

  /// Checks the consistency of `clause_to_preds`.
  #[cfg(debug_assertions)]
  fn check_clause_to_preds(& self) -> Res<()> {
    for (cls_idx, clause) in self.clauses.index_iter() {
      for pred in clause.lhs_preds.keys() {
        if ! self.clause_to_preds[cls_idx].0.contains(pred) {
          bail!(
            "predicate {} appears in lhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[* pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_preds(
              & self.clause_to_preds[cls_idx].0
            ), self.pretty_pred_opt(
              & self.clause_to_preds[cls_idx].1
            )
          )
        }
      }
      if let Some(pred) = clause.rhs.pred() {
        if self.clause_to_preds[cls_idx].1 != Some(pred) {
          bail!(
            "predicate {} appears in rhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_preds(
              & self.clause_to_preds[cls_idx].0
            ), self.pretty_pred_opt(
              & self.clause_to_preds[cls_idx].1
            )
          )
        }
      }
    }
    for (clause, & (ref lhs, ref rhs)) in self.clause_to_preds.index_iter() {
      'pred_clauses: for pred in lhs {
        if self.clauses[clause].lhs_preds.get(& pred).is_none() {
          bail!(
            "predicate {} is registered to appear in lhs of clause {} \
            but it's not the case\n{}\nlhs: {}\nrhs: {}",
            self[* pred], clause,
            self.clauses[clause].to_string_info(self.preds()) ?,
            self.pretty_preds(
              & self.clause_to_preds[clause].0
            ), self.pretty_pred_opt(
              & self.clause_to_preds[clause].1
            )
          )
        }
      }
      if let Some(pred) = * rhs {
        if self.clauses[clause].rhs.pred() != Some(pred) {
          bail!(
            "predicate {} is registered to appear in rhs of clause {} \
            but it's not the case\n{}\nlhs: {}\nrhs: {}",
            self[pred], clause,
            self.clauses[clause].to_string_info(self.preds()) ?,
            self.pretty_preds(
              & self.clause_to_preds[clause].0
            ), self.pretty_pred_opt(
              & self.clause_to_preds[clause].1
            )
          )
        }
      }
    }
    Ok(())
  }


  // Forces some predicates to false.
  pub fn force_false<Preds: IntoIterator<Item = PrdIdx>>(
    & mut self, preds: Preds
  ) -> Res<usize> {
    let mut clauses_dropped = 0 ;
    let (mut clause_lhs, mut clause_rhs) = (ClsSet::new(), ClsSet::new()) ;
    let fls = TTerms::fls() ;
    for pred in preds.into_iter() {
      debug_assert!( clause_lhs.is_empty() ) ;
      debug_assert!( clause_rhs.is_empty() ) ;
      info!("  forcing {} to false", self[pred]) ;
      self.force_pred( pred, fls.clone() ) ? ;
      self.drain_unlink_pred(pred, & mut clause_lhs, & mut clause_rhs) ;
      clauses_dropped += clause_lhs.len() ;
      self.forget_clauses( clause_lhs.drain().collect() ) ? ;
      for clause in clause_rhs.drain() {
        debug_assert_eq!{ self.clauses[clause].rhs.pred(), Some(pred) }
        self.clauses[clause].rhs = TTerm::T( term::fls() )
      }
    }
    self.check("force_false") ? ;
    Ok(clauses_dropped)
  }



  // Forces some predicates to true.
  pub fn force_true<Preds: IntoIterator<Item = PrdIdx>>(
    & mut self, preds: Preds
  ) -> Res<usize> {
    let mut clauses_dropped = 0 ;
    let (mut clause_lhs, mut clause_rhs) = (ClsSet::new(), ClsSet::new()) ;
    let tru = TTerms::tru() ;
    
    for pred in preds.into_iter() {
      debug_assert!( clause_lhs.is_empty() ) ;
      debug_assert!( clause_rhs.is_empty() ) ;

      info!("  forcing {} to true", self[pred]) ;
      self.force_pred( pred, tru.clone() ) ? ;
      self.drain_unlink_pred(pred, & mut clause_lhs, & mut clause_rhs) ;

      for clause in clause_lhs.drain() {
        self.clauses[clause].lhs_preds.remove(& pred) ;
      }
      clauses_dropped += clause_rhs.len() ;
      self.forget_clauses( clause_rhs.drain().collect() ) ? ;
    }
    self.check("force_true") ? ;
    Ok(clauses_dropped)
  }




  /// Forces some predicates to be something.
  pub fn force_preds<Preds: IntoIterator<
    Item = (PrdIdx, TTerms)
  >>(
    & mut self, preds: Preds
  ) -> Res<usize> {
    let (mut clause_lhs, mut clause_rhs) = (ClsSet::new(), ClsSet::new()) ;
    let mut terms_to_add = vec![] ;
    let mut clauses_to_rm = ClsSet::new() ;
    let mut clauses_rmed = 0 ;
    // We need to add clauses when forcing a predicate to be a disjunction.
    let mut clauses_to_add = Vec::with_capacity(10) ;
    let mut _clauses_added = 0 ;

    log_debug!{ "  force preds..." }

    for (pred, tterms) in preds.into_iter() {
      debug_assert!( clause_lhs.is_empty() ) ;
      debug_assert!( clause_rhs.is_empty() ) ;
      debug_assert!( clauses_to_add.is_empty() ) ;
      debug_assert!( clauses_to_rm.is_empty() ) ;
      
      log_debug!{ "  - {}", self[pred] }

      self.drain_unlink_pred(pred, & mut clause_lhs, & mut clause_rhs) ;

      // LHS.
      'clause_iter_lhs: for clause in clause_lhs.drain() {
        debug_assert!( terms_to_add.is_empty() ) ;
        
        if clauses_to_rm.contains(& clause) { continue 'clause_iter_lhs }

        // log_debug!{ "    working on lhs of clause #{}", clause }

        if let Some(argss) = self.clauses[clause].lhs_preds.remove(& pred) {
          for args in argss {

            match tterms.subst_total(& args)?.simplify() {
              TTerms::True => (),
              TTerms::False => {
                terms_to_add.clear() ;
                clauses_to_rm.insert(clause) ;
                continue 'clause_iter_lhs
              },
              TTerms::And(tterms) => {
                // log_debug!{ "    extending..." }
                // for tterm in & tterms {
                //   log_debug!{ "    - {}", tterm }
                // }
                self.clause_lhs_extend(clause, tterms)
              },
              TTerms::Dnf(mut ttermss) => {
                // Need to create new clauses.
                if let Some(tterms) = ttermss.pop() {
                  self.clause_lhs_extend(clause, tterms) ;
                  // terms_to_add.extend( ttermss ) ;
                  unimplemented!("clause creation when forcing lhs to dnf")

                } else {
                  bail!("empty tterms dnf should not happen")
                }
              },
            }
          }
        } else {
          bail!(
            "inconsistent instance state, \
            `pred_to_clauses` and clauses out of sync"
          )
        }

        // self.clauses[clause].lhs.extend( terms_to_add.drain(0..) ) ;

        let remove = self.simplifier.clause_propagate(
          & mut self.clauses[clause]
        ).chain_err(
          || format!(
            "on clause {}",
            self.clauses[clause].to_string_info(& self.preds).unwrap()
          )
        ) ? ;
        if remove { clauses_to_rm.insert(clause) ; () }

      }

      // RHS.
      'clause_iter_rhs: for clause in clause_rhs.drain() {
        // log_debug!{ "    rhs..." }

        if clauses_to_rm.contains(& clause) { continue 'clause_iter_rhs }

        debug_assert!( terms_to_add.is_empty() ) ;

        let tterms = if let TTerm::P {
          pred: _this_pred, ref args
        } = self[clause].rhs {
          debug_assert_eq!( _this_pred, pred ) ;
          tterms.subst_total(args)?.simplify()
        } else {
          bail!("inconsistent instance")
        } ;

        match tterms {
          TTerms::True => {
            clauses_to_rm.insert(clause) ;
            continue 'clause_iter_rhs
          },
          TTerms::False => {
            self.clauses[clause].rhs = TTerm::T( term::fls() )
          },
          TTerms::And(mut tterms) => {
            // Need to create more clauses.
            if let Some(tterm) = tterms.pop() {
              self.clauses[clause].rhs = tterm ;
              terms_to_add.extend( tterms )
            } else {
              bail!("illegal empty conjunction of top terms")
            }
          },
          TTerms::Dnf(_) => bail!(
            "trying to force a rhs to a dnf"
          ),
        }

        let mut tterms = terms_to_add.drain(0..) ;
        if let Some(tterm) = tterms.next() {
          if let Some(pred) = tterm.pred() {
            self.pred_to_clauses[pred].1.insert(clause) ;
            self.clause_to_preds[clause].1 = Some(pred) ;
          }
          self.clauses[clause].rhs = tterm ;
          for tterm in tterms {
            let clause = self.clauses[clause].clone_with_rhs(tterm) ;
            self.push_clause(clause) ?
          }
        }

        let remove = self.simplifier.clause_propagate(
          & mut self.clauses[clause]
        ).chain_err(
          || format!(
            "on clause {}",
            self.clauses[clause].to_string_info(& self.preds).unwrap()
          )
        ) ? ;
        if remove { clauses_to_rm.insert(clause) ; () }

      }

      if ! tterms.mention_pred(pred) {
        self.force_pred(pred, tterms) ?
      }
      clauses_rmed += clauses_to_rm.len() ;
      self.forget_clauses( clauses_to_rm.drain().collect() ) ? ;
      _clauses_added += clauses_to_add.len() ;
      for clause in clauses_to_add.drain(0..) {
        self.push_clause(clause) ?
      }
    }

    Ok(clauses_rmed)
  }
}
impl ::std::ops::Index<ClsIdx> for Instance {
  type Output = Clause ;
  fn index(& self, index: ClsIdx) -> & Clause {
    & self.clauses[index]
  }
}
impl ::std::ops::Index<PrdIdx> for Instance {
  type Output = PrdInfo ;
  fn index(& self, index: PrdIdx) -> & PrdInfo {
    & self.preds[index]
  }
}








// impl<'a> PebcakFmt<'a> for TTerm {
//   type Info = (& 'a VarMap<VarInfo>, & 'a PrdMap<PrdInfo>) ;
//   fn pebcak_err(& self) -> ErrorKind {
//     "during top term pebcak formatting".into()
//   }
//   fn pebcak_io_fmt<W: Write>(
//     & self, w: & mut W,
//     (vars, prds): (& 'a VarMap<VarInfo>, & 'a PrdMap<PrdInfo>)
//   ) -> IoRes<()> {
//     self.write(
//       w,
//       |w, var| w.write_all( vars[var].as_bytes() ),
//       |w, prd| w.write_all( prds[prd].as_bytes() )
//     )
//   }
// }

impl<'a> PebcakFmt<'a> for Clause {
  type Info = & 'a PrdMap<PrdInfo> ;
  fn pebcak_err(& self) -> ErrorKind {
    "during clause pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, prds: & 'a PrdMap<PrdInfo>
  ) -> IoRes<()> {
    self.write(
      w, |w, prd, args| {
        write!(w, "(") ? ;
        w.write_all( prds[prd].as_bytes() ) ? ;
        for arg in args {
          write!(w, " ") ? ;
          arg.write(w, |w, var| w.write_all( self.vars[var].as_bytes() )) ?
        }
        write!(w, ")")
      }
    )
  }
}

impl<'a> PebcakFmt<'a> for Instance {
  type Info = () ;
  fn pebcak_err(& self) -> ErrorKind {
    "during instance pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, _: ()
  ) -> IoRes<()> {
    use common::consts::keywords ;

    for (pred_idx, pred) in self.preds.index_iter() {
      if self.pred_terms[pred_idx].is_none() {
        write!(
          w, "({}\n  {}\n  (", keywords::prd_dec, pred.name
        ) ? ;
        for typ in & pred.sig {
          write!(w, " {}", typ) ?
        }
        write!(w, " ) Bool\n)\n") ?
      }
    }

    if self.sorted_pred_terms.is_empty() {
      // Either there's no forced predicate, or we are printing before
      // finalizing.
      for (pred, tterms) in self.pred_terms.index_iter().filter_map(
        |(pred, tterms_opt)| tterms_opt.as_ref().map(|tt| (pred, tt))
      ) {
        write!(w, "({} {}\n  (", keywords::prd_def, self[pred]) ? ;
        for (var, typ) in self[pred].sig.index_iter() {
          write!(w, " (v_{} {})", var, typ) ?
        }
        write!(w, " ) Bool\n  {}\n)\n", tterms) ?
      }
    } else {
      for pred in & self.sorted_pred_terms {
        write!(w, "({} {}\n  (", keywords::prd_def, self[* pred]) ? ;
        for (var, typ) in self[* pred].sig.index_iter() {
          write!(w, " (v_{} {})", var, typ) ?
        }
        let tterms = self.pred_terms[* pred].as_ref().unwrap() ;
        write!(w, " ) Bool\n  {}\n)\n", tterms) ?
      }
    }

    for (idx, clause) in self.clauses.index_iter() {
      write!(w, "\n; Clause #{}\n", idx) ? ;
      clause.pebcak_io_fmt(w, & self.preds) ?
    }

    write!(w, "\npred to clauses:\n") ? ;
    for (pred, & (ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
      write!(w, "  {}: lhs {{", self[pred]) ? ;
      for lhs in lhs {
        write!(w, " {}", lhs) ?
      }
      write!(w, " }}, rhs {{") ? ;
      for rhs in rhs {
        write!(w, " {}", rhs) ?
      }
      write!(w, " }}\n") ?
    }

    write!(w, "\nclause to preds:\n") ? ;
    for (clause, & (ref lhs, ref rhs)) in self.clause_to_preds.index_iter() {
      write!(w, "  {}: lhs {{", clause) ? ;
      if ! lhs.is_empty() {
        write!(w, "\n   ") ? ;
        for pred in lhs {
          write!(w, " {}", self[* pred]) ?
        }
        write!(w, "\n") ?
      }
      write!(w, "  }}, rhs ") ? ;
      if let Some(pred) = * rhs {
        write!(w, "{}\n", self[pred])
      } else {
        write!(w, "none\n")
      } ?
    }

    Ok(())
  }
}






/// Simplifies clauses.
///
/// The goal of this type is to avoid reallocation and compartment the clause
/// simplification process.
struct ClauseSimplifier {
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
  /// Returns `true` if the clause should_be_removed.
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
    let mut remove ;

    // Find equalities in `lhs`.
    for term in & clause.lhs_terms {
      if let Some((Op::Eql, _)) = term.app_inspect() {
        self.eqs.push( term.clone() )
      }
    }

    for eq in self.eqs.drain(0..) {
      remove = true ;
      log_debug!{ "  looking at equality {}", eq }

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
            let mut set_1 = if let Some(set) = self.rep_to_vars.get_mut(& rep_1) {
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
          },
          // Only `v_1` has a rep.
          (Some(rep_1), None) => {
            let mut set_1 = if let Some(set) = self.rep_to_vars.get_mut(& rep_1) {
              set
            } else { panic!("simplification error (3)") } ;
            let _is_new = set_1.insert(v_2) ;
            debug_assert!( _is_new ) ;
            let _prev = self.var_to_rep.insert(v_2, rep_1) ;
            debug_assert!( _prev.is_none() )
          },
          // Only `v_2` has a rep.
          (None, Some(rep_2)) => {
            let mut set_2 = if let Some(set) = self.rep_to_vars.get_mut(& rep_2) {
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
            let _prev = self.rep_to_vars.insert(var, VarSet::with_capacity(4)) ;
            debug_assert!( _prev.is_none() ) ;
            var
          } ;
          let prev = self.rep_to_term.insert(rep, term.clone()) ;
          if let Some(prev) = prev {
            let eq = term::eq(prev, term) ;
            match eq.eval( & VarMap::with_capacity(0) ) {
              Ok(Val::B(true)) => (),
              Ok(Val::B(false)) => return Ok(true),
              Ok(Val::I(_)) => bail!("equality evaluation yielded integer"),
              _ => self.terms_to_add.push(eq),
            }
          }
        },

        (None, None) => remove = false,

      }

      if remove {
        log_debug!{ "  removing..." }
        let was_there = clause.lhs_terms.remove(& eq) ;
        debug_assert!(was_there)
      } else {
        log_debug!{ "  skipping..." }
      }
    }

    self.check( clause.vars() ) ? ;

    log_debug!{ "  generating `var_to_rep_term`" }
    self.var_to_rep_term = VarHMap::with_capacity( self.var_to_rep.len() ) ;
    for (rep, set) in & self.rep_to_vars {
      for var in set {
        if var != rep {
          let _prev = self.var_to_rep_term.insert(* var, term::var(* rep)) ;
          debug_assert!( _prev.is_none() )
        }
      }
    }
    if_debug!{
      for (var, rep) in & self.var_to_rep {
        log_debug!{ "    {} -> {}", var, rep }
      }
    }

    log_debug!{ "  stabilizing `rep_to_term` (first step)" }
    for (_, term) in & mut self.rep_to_term {
      let (nu_term, changed) = term.subst(& self.var_to_rep_term) ;
      if changed { * term = nu_term }
    }
    if_debug!{
      for (rep, term) in & self.rep_to_term {
        log_debug!{ "    {} -> {}", rep, term }
      }
    }

    log_debug!{ "  stabilizing `rep_to_term` (second step)" }
    self.rep_to_stable_term = VarHMap::with_capacity(self.rep_to_term.len()) ;
    for (rep, term) in & self.rep_to_term {
      let (nu_term, _) = term.subst_fp(& self.rep_to_term) ;
      let _prev = self.rep_to_stable_term.insert(* rep, nu_term) ;
      debug_assert!( _prev.is_none() )
    }
    if_debug!{
      for (rep, term) in & self.rep_to_stable_term {
        log_debug!{ "    {} -> {}", rep, term }
      }
    }

    // Note that clause variable de-activation is done in this loop.
    log_debug!{ "  completing substitution" }
    for (rep, vars) in self.rep_to_vars.drain() {
      let term = if let Some(term) = self.rep_to_stable_term.get(& rep) {
        clause.vars[rep].active = false ;
        term.clone()
      } else {
        debug_assert!( clause.vars[rep].active ) ;
        term::var(rep)
      } ;
      for var in vars {
        clause.vars[var].active = false ;
        let _prev = self.rep_to_stable_term.insert(var, term.clone()) ;
        debug_assert_eq!( _prev, None )
      }
    }
    if_debug!{
      for (rep, term) in & self.rep_to_stable_term {
        log_debug!{ "    {} -> {}", rep, term }
      }
    }

    for term in self.terms_to_add.drain(0..) {
      clause.insert_term(term) ;
    }

    log_debug!{ "  updating clause's terms" }
    clause.subst(& self.rep_to_stable_term) ;

    Ok(false)
  }
}