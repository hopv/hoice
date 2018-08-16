//! Contains the clause structure for encapsulation.

use common::* ;
use var_to::terms::VarTermsSet ;
use instance::info::VarInfo ;

/// Creates a clause.
///
/// Only accessible from the instance.
pub fn new(
  vars: VarInfos, lhs: Vec<TTerm>, rhs: Option<PredApp>,
  info: & 'static str, cls: ClsIdx,
) -> Clause {
  let from = cls ;
  let lhs_terms = TermSet::with_capacity( lhs.len() ) ;
  let lhs_preds = PredApps::with_capacity( lhs.len() ) ;
  let mut clause = Clause {
    vars, lhs_terms, lhs_preds, rhs,
    terms_changed: true, preds_changed: true,
    from_unrolling: false, info, from,
    has_fun_apps: false,
  } ;
  for tterm in lhs { clause.lhs_insert(tterm) ; }
  clause
}


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
  pub vars: VarInfos,
  /// Terms of the left-hand side.
  lhs_terms: TermSet,
  /// Predicate applications of the left-hand side.
  lhs_preds: PredApps,
  /// Single term right-hand side.
  rhs: Option<PredApp>,
  /// Indicates wether `lhs_terms` has changed since the last call to
  /// `lhs_terms_checked`.
  terms_changed: bool,
  /// Indicates wether the predicate applications have changed since the last
  /// call to `preds_checked`.
  preds_changed: bool,
  /// True if the clause is the result of unrolling.
  ///
  /// Means the terms will be ignored during mining.
  pub from_unrolling: bool,
  /// Info about who created this clause.
  pub info: & 'static str,

  /// Index of the original clause this comes from.
  from: ClsIdx,
  /// True if the clause contains function applications.
  has_fun_apps: bool,
}

/// Updates the `has_fun_apps` flag.
///
/// Doesn't do anything if `has_fun_apps` is already false.
macro_rules! update_has_fun_apps {
  ($slf:expr) => (
    if $slf.has_fun_apps {
      $slf.has_fun_apps = false ;
      update_has_fun_apps!(@ $slf, (terms, lhs preds, rhs))
    }
  ) ;
  ($slf:expr, $tail:tt) => (
    if $slf.has_fun_apps {
      $slf.has_fun_apps = false ;
      update_has_fun_apps!(@ $slf, $tail)
    }
  ) ;

  (@ $slf:expr, (, $($tail:tt)*)) => (
    update_has_fun_apps!($slf, ($($tail)*))
  ) ;

  (@ $slf:expr, (terms $($tail:tt)*)) => ({
    if ! $slf.has_fun_apps {
      for term in & $slf.lhs_terms {
        if term.has_fun_apps() {
          $slf.has_fun_apps = true ;
          break
        }
      }
    }
    update_has_fun_apps!($slf, ($($tail)*))
  }) ;

  (@ $slf:expr, (lhs preds $($tail:tt)*)) => ({
    if ! $slf.has_fun_apps {
      for argss in $slf.lhs_preds.values() {
        for args in argss {
          for arg in args.iter() {
            if arg.has_fun_apps() {
              $slf.has_fun_apps = true ;
              break
            }
          }
        }
      }
    }
    update_has_fun_apps!($slf, ($($tail)*))
  }) ;

  (@ $slf:expr, (rhs $($tail:tt)*)) => ({
    if ! $slf.has_fun_apps {
      if let Some((_, args)) = $slf.rhs.as_ref() {
        for arg in args.iter() {
          if arg.has_fun_apps() {
            $slf.has_fun_apps = true ;
            break
          }
        }
      }
    }
    update_has_fun_apps!($slf, ($($tail)*))
  }) ;

  (@ $slf:expr, ()) => (()) ;
}



/// Functions mutating the clauses.
impl Clause {
  /// Sets the internal flag `terms_changed` to false.
  ///
  /// Also shrinks the variables.
  pub fn lhs_terms_checked(& mut self) {
    self.terms_changed = false ;
    self.shrink_vars()
  }

  /// Sets the internal flag `preds_changed` to false.
  pub fn preds_checked(& mut self) {
    self.preds_changed = false ;
    self.shrink_vars()
  }


  /// Inserts a top term in the lhs.
  ///
  /// Returns true if it was not there (`is_new`).
  #[inline]
  pub fn lhs_insert(& mut self, tterm: TTerm) -> bool {
    match tterm {
      TTerm::T(term) => if let Some(true) = term.bool() {
        false
      } else {
        let is_new = self.insert_term(term) ;
        self.terms_changed = self.terms_changed || is_new ;
        is_new
      },
      TTerm::P { pred, args } => {
        let is_new = self.insert_pred_app(pred, args) ;
        self.preds_changed = self.preds_changed || is_new ;
        is_new
      },
    }
  }



  /// Removes all predicate application of `pred` in the LHS.
  ///
  /// Returns true if the predicate application was there.
  #[inline]
  pub fn drop_lhs_pred(
    & mut self, pred: PrdIdx
  ) -> Option< VarTermsSet > {
    let res = self.lhs_preds.remove(& pred) ;
    if res.is_some() {
      update_has_fun_apps!(self) ;
      self.preds_changed = true ;
      if self.lhs_preds.is_empty()
      && self.rhs.is_none() {
        self.terms_changed = true
      }
    }
    res
  }

  /// Inserts a predicate application in the LHS.
  ///
  /// Returns true if the predicate application is new.
  #[inline]
  pub fn insert_pred_app(
    & mut self, pred: PrdIdx, args: VarTerms
  ) -> bool {
    if ! self.has_fun_apps {
      for arg in args.iter() {
        if arg.has_fun_apps() {
          self.has_fun_apps = true ;
          break
        }
      }
    }

    let is_new = self.lhs_preds.insert_pred_app(pred, args) ;
    self.preds_changed = self.preds_changed || is_new ;
    is_new
  }

  /// Inserts a term in the LHS.
  pub fn insert_term(
    & mut self, term: Term
  ) -> bool {
    if ! self.has_fun_apps && term.has_fun_apps() {
      self.has_fun_apps = true
    }
    let is_new = Self::lhs_insert_term(& mut self.lhs_terms, term) ;
    self.terms_changed = self.terms_changed || is_new ;
    is_new
  }

  /// Removes a term from the LHS.
  pub fn rm_term(& mut self, term: & Term) -> bool {
    let was_there = self.lhs_terms.remove(term) ;
    update_has_fun_apps!(self) ;
    self.terms_changed = self.terms_changed || was_there ;
    was_there
  }

  /// Drains all LHS applications.
  #[inline]
  pub fn drain_lhs_preds(
    & mut self
  ) -> ::std::collections::hash_map::Drain<PrdIdx, VarTermsSet> {
    self.terms_changed = self.terms_changed || self.rhs.is_none() ;
    self.preds_changed = true ;

    update_has_fun_apps!(self, (terms, rhs)) ;

    self.lhs_preds.drain()
  }

  /// Maps over the arguments of a predicate in the lhs.
  #[inline]
  pub fn lhs_map_args_of<F>(
    & mut self, pred: PrdIdx, mut f: F
  ) where F: FnMut(& VarTerms) -> VarTerms {
    let changed = if let Some(argss) = self.lhs_preds.get_mut(& pred) {
      self.preds_changed = true ;
      let mut nu_argss = VarTermsSet::with_capacity( argss.len() ) ;
      for args in argss.iter() {
        nu_argss.insert( f(args) ) ;
      }
      ::std::mem::swap( & mut nu_argss, argss ) ;
      true
    } else {
      false
    } ;
    if changed {
      update_has_fun_apps!(self)
    }
  }

  /// Map over the arguments of a predicate in the rhs.
  #[inline]
  pub fn rhs_map_args<F>(& mut self, mut f: F)
  where F: FnMut(PrdIdx, & VarTerms) -> (PrdIdx, VarTerms) {
    let changed = if let Some(
      & mut (ref mut pred, ref mut args)
    ) = self.rhs.as_mut() {
      self.preds_changed = true ;
      let (nu_pred, mut nu_args) = f(* pred, args) ;
      * args = nu_args ;
      * pred = nu_pred ;
      true
    } else {
      false
    } ;
    if changed {
      update_has_fun_apps!(self)
    }
  }

  /// Discards the RHS of a clause.
  ///
  /// Turns the clause into a negative one.
  #[inline]
  pub fn unset_rhs(& mut self) -> Option<PredApp> {
    let mut old_rhs = None ;
    ::std::mem::swap( & mut self.rhs, & mut old_rhs ) ;
    self.terms_changed = self.terms_changed || (
      old_rhs.is_some() && self.lhs_preds.is_empty()
    ) ;
    self.preds_changed = self.preds_changed || old_rhs.is_some() ;
    if old_rhs.is_some() {
      update_has_fun_apps!(self)
    }
    old_rhs
  }

  /// Forces the RHS of a clause.
  #[inline]
  #[cfg_attr(
    feature = "cargo-clippy", allow(block_in_if_condition_stmt)
  )]
  pub fn set_rhs(& mut self, pred: PrdIdx, args: VarTerms) -> Res<()> {
    debug_assert! {{
      let mut vars = VarSet::new() ;

      for arg in args.iter() {
        term::map_vars(arg, |v| { vars.insert(v) ; () })
      }
      for var in vars {
        if var >= self.vars.len() {
          err_chain! {
            "while forcing a clause's rhs"
            => format!(
              "illegal variable {}, current clause only has {} variables",
              conf.bad(& var.default_str() ), self.vars.len()
            )
          }
        } else if ! self.vars[var].active {
          err_chain! {
            "while forcing a clause's rhs"
            => format!(
              "found variable {}, but it is currently inactive",
              conf.bad(& self.vars[var].name)
            )
          }
        }
      }
      true
    }}

    self.rhs = Some((pred, args)) ;
    self.preds_changed = true ;
    update_has_fun_apps!(self) ;
    Ok(())
  }

  /// Clones a clause without the lhs predicate applications of `pred`.
  pub fn clone_except_lhs_of(
    & self, pred: PrdIdx, info: & 'static str
  ) -> Self {
    let mut lhs_preds = PredApps::with_capacity( self.lhs_preds.len() ) ;
    let mut was_there = false ;
    for (p, argss) in & self.lhs_preds {
      if pred != * p {
        let prev = lhs_preds.insert(* p, argss.clone()) ;
        debug_assert_eq! { prev, None }
      } else {
        was_there = true
      }
    }

    let (terms_changed, preds_changed) = (
      self.terms_changed || (
        was_there && lhs_preds.is_empty()
      ),
      self.preds_changed || was_there
    ) ;

    let mut clause = Clause {
      vars: self.vars.clone(),
      lhs_terms: self.lhs_terms.clone(), lhs_preds,
      rhs: self.rhs.clone(),
      terms_changed, preds_changed,
      from_unrolling: self.from_unrolling,
      info,
      from: self.from,
      has_fun_apps: self.has_fun_apps,
    } ;

    update_has_fun_apps!(clause) ;

    clause
  }

  /// Clones a clause but changes the rhs.
  #[inline]
  pub fn clone_with_rhs(
    & self, rhs: Option<TTerm>, info: & 'static str
  ) -> Self {
    let mut lhs_terms = self.lhs_terms.clone() ;

    let (rhs, terms_changed, preds_changed) = match rhs {
      Some( TTerm::P { pred, args } ) => (
        Some((pred, args)), self.terms_changed, true
      ),
      Some( TTerm::T(term) ) => {
        let added = if term.bool() != Some(false) {
          lhs_terms.insert( term::not(term) )
        } else {
          false
        } ;
        (
          None,
          self.terms_changed || added,
          self.preds_changed || self.rhs.is_some()
        )
      },
      None => (
        None,
        self.terms_changed || self.rhs.is_some(),
        self.preds_changed || self.rhs.is_some(),
      ),
    } ;

    let mut clause = Clause {
      vars: self.vars.clone(),
      lhs_terms,
      lhs_preds: self.lhs_preds.clone(),
      rhs,
      terms_changed, preds_changed,
      from_unrolling: self.from_unrolling,
      info,
      from: self.from,
      has_fun_apps: true,
    } ;

    update_has_fun_apps!(clause) ;

    clause
  }


  /// Removes all redundant terms from `lhs_terms`.
  ///
  /// # TODO
  ///
  /// - can be optimized by using `retain` (probably)
  fn prune(& mut self) {
    use std::cmp::Ordering::* ;
    use term::simplify::SimplRes::* ;
    let mut to_rm = TermSet::new() ;
    let mut to_add = TermSet::new() ;

    let mut prune_things = true ;
    let mut pruned = false ;

    while prune_things {
      prune_things = false ;
      debug_assert! { to_rm.is_empty() }
      debug_assert! { to_add.is_empty() }

      scoped! {
        let mut terms = self.lhs_terms.iter() ;
        while let Some(term) = terms.next() {
          for t in terms.clone() {
            match t.conj_simpl(term) {
              // `t` is more generic, `term` is redundant, keep `t`.
              Cmp(Equal) | Cmp(Greater) => {
                to_rm.insert( term.clone() ) ;
              },
              // `term` is more generic, discard `t`.
              Cmp(Less) => {
                to_rm.insert( t.clone() ) ;
              },
              // No relation.
              None => (),
              Yields(nu_term) => {
                to_rm.insert( t.clone() ) ;
                to_rm.insert( term.clone() ) ;
                to_add.insert(nu_term) ;
                ()
              },
            }
          }
        }
      }

      pruned = pruned || ! to_rm.is_empty() || ! to_add.is_empty() ;

      self.terms_changed = self.terms_changed
      || ! to_rm.is_empty() || ! to_add.is_empty() ;

      for to_rm in to_rm.drain() {
        let was_there = self.lhs_terms.remove(& to_rm) ;
        debug_assert! { was_there }
      }

      for to_add in to_add.drain() {
        let is_new = self.lhs_terms.insert(to_add) ;
        prune_things = prune_things || is_new
      }

    }

    if pruned {
      update_has_fun_apps!(self)
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
    let mut lhs_terms = TermSet::with_capacity( self.lhs_terms.len() ) ;
    ::std::mem::swap(& mut lhs_terms, & mut self.lhs_terms) ;
    for term in lhs_terms.drain() {
      let (term, b) = term.subst(map) ;
      self.insert_term(term) ;
      changed = changed || b
    }
    for (_, argss) in & mut self.lhs_preds {
      let mut nu_argss = VarTermsSet::with_capacity( argss.len() ) ;
      debug_assert!( nu_argss.is_empty() ) ;
      for args in argss.iter() {
        let mut nu_args = VarMap::with_capacity( args.len() ) ;
        for arg in args.iter() {
          let (nu_arg, b) = arg.subst(map) ;
          changed = changed || b ;
          nu_args.push(nu_arg)
        }
        nu_argss.insert( nu_args.into() ) ;
      }
      ::std::mem::swap(& mut nu_argss, argss) ;
      self.preds_changed = true ;
    }

    self.rhs_map_args(
      |pred, args| {
        let mut nu_args = VarMap::with_capacity( args.len() ) ;
        for arg in args.iter() {
          let (nu_arg, b) = arg.subst(map) ;
          nu_args.push(nu_arg) ;
          changed = changed || b
        }
        ( pred, nu_args.into() )
      }
    ) ;

    if changed {
      update_has_fun_apps!(self) ;
      self.terms_changed = true ;
      self.preds_changed = true ;
      self.prune()
    }

    changed
  }

  /// Adds fresh variables to the clause for each of the input variables.
  /// Returns a map from the input variables to the fresh ones (as terms).
  ///
  /// Used when inlining a predicate with quantified variables.
  pub fn fresh_vars_for(& mut self, vars: & Quantfed) -> VarHMap<Term> {
    let mut map = VarHMap::with_capacity( vars.len() ) ;
    for (var, typ) in vars {
      let fresh = self.vars.next_index() ;
      let fresh_name = format!("hoice_fresh_var@{}", fresh) ;
      let info = VarInfo::new(fresh_name, typ.clone(), fresh) ;
      self.vars.push(info) ;
      let _prev = map.insert(* var, term::var(fresh, typ.clone())) ;
      debug_assert!( _prev.is_none() )
    }
    map
  }

  /// Adds fresh variables to the clause for each of the input variables.
  /// Returns a map from the input variables to the fresh ones (as terms).
  ///
  /// Used when inlining a predicate with quantified variables.
  pub fn nu_fresh_vars_for(
    & mut self, quant: & Option<Quant>
  ) -> VarHMap<Term> {
    if let Some(quant) = quant.as_ref() {
      let vars = quant.vars() ;
      let mut map = VarHMap::with_capacity( vars.len() ) ;
      for (var, typ) in vars {
        let fresh = self.vars.next_index() ;
        let fresh_name = format!("hoice_fresh_var@{}", fresh) ;
        let info = VarInfo::new(fresh_name, typ.clone(), fresh) ;
        self.vars.push(info) ;
        let _prev = map.insert(* var, term::var(fresh, typ.clone())) ;
        debug_assert!( _prev.is_none() )
      }
      map
    } else {
      VarHMap::new()
    }
  }






  /// Deactivates a variable.
  pub fn deactivate(& mut self, var: VarIdx) -> Res<()> {
    debug_assert!( self.vars[var].active ) ;
    self.vars[var].active = false ;
    self.check( "after `deactivate`" )
  }

  /// Shrinks the clause: detects inactive variables.
  pub fn shrink_vars(& mut self) {
    let mut active = 0 ;
    for var in & self.vars {
      if var.active { active += 1 }
    }
    let mut vars = VarSet::with_capacity( active ) ;

    for term in & self.lhs_terms {
      term::map_vars(term, |v| { vars.insert(v) ; () }) ;
      if vars.len() == active {
        return ()
      }
    }

    for (_, argss) in & self.lhs_preds {
      for args in argss {
        for arg in args.iter() {
          term::map_vars(arg, |v| { vars.insert(v) ; () }) ;
        }
      }
      if vars.len() == active {
        return ()
      }
    }

    if let Some(& (_, ref args)) = self.rhs.as_ref() {
      for arg in args.iter() {
        term::map_vars(arg, |v| { vars.insert(v) ; () }) ;
      }
    }

    for (index, info) in self.vars.index_iter_mut() {
      if ! vars.contains(& index) {
        info.active = false
      }
    }
  }

  /// Inserts a term in an LHS. Externalized for ownership reasons.
  fn lhs_insert_term(lhs_terms: & mut TermSet, term: Term) -> bool {
    // println!("inserting {}", term) ;
    let mut new_stuff = false ;
    let mut stack = vec![term] ;

    while let Some(term) = stack.pop() {
      debug_assert! { term.typ().is_bool() }
      if let Some(kids) = term.conj_inspect() {
        for kid in kids {
          stack.push( kid.clone() )
        }
      } else if let Some(b) = term.bool() {
        if ! b {
          lhs_terms.clear() ;
          lhs_terms.insert( term::fls() ) ;
          return true
        }
      } else {
        let is_new = Self::clever_insert(term.clone(), lhs_terms) ;
        new_stuff = new_stuff || is_new
      }
    }

    new_stuff
  }

  /// Checks if `term` is implied by a term in `set`.
  ///
  /// Removes the terms from `set` that are implied (strictly) by `term`.
  fn clever_insert(
    mut term: Term, set: & mut TermSet
  ) -> bool {
    use std::cmp::Ordering::* ;
    use term::simplify::SimplRes::* ;

    let mut redundant = false ;
    let mut rmed_stuff = false ;
    let mut keep_checking = true ;

    while keep_checking {
      keep_checking = false ;

      set.retain(
        |t| match t.conj_simpl(& term) {
          // `t` is more generic, `term` is redundant, keep `t`.
          Cmp(Equal) | Cmp(Greater) => {
            redundant = true ;
            true
          },
          // `term` is more generic, discard.
          Cmp(Less) => {
            rmed_stuff = true ;
            // println!("  removing {}", t) ;
            false
          },
          // No relation, keep `t`.
          None => true,
          // New term.
          Yields(nu_term) => {
            rmed_stuff = true ;
            redundant = false ;
            keep_checking = true ;
            term = nu_term ;
            false
          },
        }
      )
    }
    // If we removed stuff, it means the term should not be redundant.
    assert! { ! rmed_stuff || ! redundant }
    if ! redundant {
      let is_new = set.insert(term) ;
      debug_assert! { is_new }
      true
    } else {
      false
    }
  }
}



impl Clause {

  /// Checks if two clauses are the same.
  pub fn same_as(& self, other: & Self) -> bool {
    self.rhs == other.rhs &&
    self.lhs_preds == other.lhs_preds &&
    self.lhs_terms == other.lhs_terms
  }

  /// Cheap unsat check.
  ///
  /// Does not use smt-solving, as this is the responsability of the
  /// preprocessing.
  pub fn is_unsat(& self) -> bool {
    self.lhs_terms.is_empty()
    && self.lhs_preds.is_empty()
    && self.rhs.is_none()
  }

  /// True if the clause is positive (lhs is empty).
  pub fn is_positive(& self) -> bool {
    self.lhs_preds.is_empty() && self.rhs.is_some()
  }

  /// True if the clause is a strictly negative clause.
  ///
  /// True if
  ///
  /// - no rhs
  /// - only one predicate application
  pub fn is_strict_neg(& self) -> bool {
    self.rhs.is_none()
    && self.lhs_preds.len() == 1
    && self.lhs_preds().iter().next().map(
      |(_, argss)| argss.len() == 1
    ).unwrap_or(false)
  }


  /// True if the same predicate application appears both in the lhs and the
  /// rhs.
  pub fn is_pred_trivial(& self) -> bool {
    if let Some((pred, args)) = self.rhs() {
      if let Some(argss) = self.lhs_preds.get(& pred) {
        argss.contains(args)
      } else {
        false
      }
    } else {
      false
    }
  }

  /// True iff the lhs terms changed since the last call to
  /// [`lhs_terms_checked`][checked].
  ///
  /// [checked]: #methods.lhs_terms_checked
  /// (lhs_terms_checked method)
  pub fn terms_changed(& self) -> bool { self.terms_changed }

  /// True iff the predicate applications have changed since the last call to
  /// [`preds_checked`][checked].
  ///
  /// [checked]: #methods.preds_checked
  /// (preds_checked method)
  pub fn preds_changed(& self) -> bool { self.preds_changed }

  /// Checks a clause is well-formed.
  #[cfg(debug_assertions)]
  pub fn check(& self, blah: & 'static str) -> Res<()> {
    use std::iter::Extend ;
    let mut vars = VarSet::with_capacity( self.vars.len() ) ;
    for term in & self.lhs_terms {
      vars.extend( term::vars( term ) )
    }

    scoped! {
      let mut terms = self.lhs_terms.iter() ;

      while let Some(term) = terms.next() {
        for t in terms.clone() {
          if term.conj_simpl(t).is_some() {
            bail!(
              "redundant atoms in clause:\n  {}\n  {}\n{}",
              term, t, conf.bad(blah)
            )
          }
        }
      }
    }

    for (_, argss) in & self.lhs_preds {
      for args in argss {
        for arg in args.iter() {
          vars.extend( term::vars(arg) )
        }
      }
    }
    if let Some((_, ref args)) = self.rhs {
      for arg in args.iter() {
        vars.extend( term::vars(arg) )
      }
    }
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
  #[inline]
  pub fn check(& self, _: & 'static str) -> Res<()> {
    Ok(())
  }

  /// Length of a clause's LHS.
  #[inline]
  pub fn lhs_len(& self) -> usize {
    self.lhs_terms.len() + self.lhs_preds.len()
  }
  /// True if the clause's LHS is empty.
  #[inline]
  pub fn lhs_is_empty(& self) -> bool {
    self.lhs_terms.is_empty() && self.lhs_preds.is_empty()
  }

  /// LHS accessor (terms).
  #[inline]
  pub fn lhs_terms(& self) -> & TermSet {
    & self.lhs_terms
  }
  /// LHS accessor (predicate applications).
  #[inline]
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
  #[inline]
  pub fn rhs(& self) -> Option<(PrdIdx, & VarTerms)> {
    if let Some((prd, ref args)) = self.rhs {
      Some((prd, args))
    } else {
      None
    }
  }

  /// Iterator over all predicate applications (including the rhs).
  pub fn all_pred_apps_do<F>(& self, mut f: F) -> Res<()>
  where F: FnMut(PrdIdx, & VarTerms) -> Res<()> {
    for (pred, argss) in & self.lhs_preds {
      for args in argss {
        f(* pred, args) ?
      }
    }
    if let Some(& (pred, ref args)) = self.rhs.as_ref() {
      f(pred, args) ?
    }
    Ok(())
  }

  /// Variables accessor.
  #[inline]
  pub fn vars(& self) -> & VarInfos {
    & self.vars
  }

  /// Returns the source clauses.
  ///
  /// Source clauses are original clauses this clause stems from.
  pub fn from(& self) -> ClsIdx {
    self.from
  }

  /// Declares all active clause variables.
  pub fn declare<Parser>(
    & self, solver: & mut Solver<Parser>
  ) -> Res<()> {
    for var in self.vars() {
      if var.active {
        solver.declare_const(& var.idx, var.typ.get()) ?
      }
    }
    Ok(())
  }

  /// Writes a clause given a special function to write predicates.
  pub fn write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {
    writeln!(w, "({} ", keywords::cmd::assert) ? ;
    self.internal_naked_write(w, write_prd, true, 2) ? ;
    writeln!(w, ")") ? ;
    Ok(())
  }

  /// Writes a clause without the `assert` around it.
  pub fn naked_write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd, indent: usize
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {
    self.internal_naked_write(w, write_prd, false, indent)
  }

  /// Writes a clause without the `assert` around it.
  fn internal_naked_write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd, info: bool, indent: usize
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {
    write!(
      w, "{nil: >indent$}({}\n{nil: >indent$}  (",
      keywords::forall, nil="", indent=indent
    ) ? ;

    let mut inactive = 0 ;
    for var in & self.vars {
      if var.active {
        write!(w, " ({} {})", var.name, var.typ) ?
      } else {
        inactive += 1 ;
      }
    }
    if inactive == self.vars.len() {
      write!(w, " (unused Bool)") ?
    }
    writeln!(w, " )") ? ;

    if info {
      writeln!(
        w, "{nil: >indent$}  \
          ; {} inactive variable(s)\n{nil: >indent$}  \
          ; unroll: {}\n{nil: >indent$}  \
          ; terms_changed: {}\n{nil: >indent$}  \
          ; preds_changed: {}\n{nil: >indent$}  \
          ; created by `{}`\
        ",
        inactive, self.from_unrolling,
        self.terms_changed, self.preds_changed, self.info,
        nil="", indent=indent
      ) ?
    }

    self.internal_qf_write(w, write_prd, indent + 2) ? ;

    writeln!(w, "{nil: >indent$})", nil="", indent=indent) ? ;

    Ok(())
  }


  /// Writes a clause without the quantifiers around it.
  fn internal_qf_write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd, indent: usize
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {
    write!(
      w, "{nil: >indent$}(=>\n{nil: >indent$}  (and\n{nil: >indent$}   ",
      nil="", indent=indent
    ) ? ;

    if self.lhs_terms.is_empty() {
      write!(w, " true") ?
    } else {
      for term in & self.lhs_terms {
        write!(w, " ") ? ;
        term.write(
          w,
          |w, var| w.write_all( self.vars[var].as_bytes() )
        ) ?
      }
    }

    write!(w, "\n{nil: >indent$}   ", nil="", indent=indent) ? ;

    if self.lhs_preds.is_empty() {
      write!(w, " true") ?
    } else {
      for (pred, argss) in & self.lhs_preds {
        for args in argss {
          write!(w, " ") ? ;
          write_prd(w, * pred, args) ?
        }
      }
    }

    write!(
      w, "\n{nil: >indent$}  )\n{nil: >indent$}  ", nil="", indent=indent
    ) ? ;

    if let Some((pred, ref args)) = self.rhs {
      write_prd(w, pred, args) ?
    } else {
      write!(w, "false") ?
    }
    writeln!(
      w, "\n{nil: >indent$})", nil="", indent=indent
    ) ? ;

    Ok(())
  }



  /// Asserts a clause.
  pub fn assert<P, W, WritePrd>(
    & self, solver: Solver<P>, write_pred: WritePrd, need_model: bool
  ) -> Res<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & VarTerms) -> IoRes<()> {

    if ! need_model && self.has_fun_apps {

    } else {

    }

    Ok(())
  }

}

impl ::std::ops::Index<VarIdx> for Clause {
  type Output = VarInfo ;
  fn index(& self, index: VarIdx) -> & VarInfo {
    & self.vars[index]
  }
}

impl<'a, 'b> ::rsmt2::print::Expr2Smt<
  & 'b (bool, & 'a PrdSet, & 'a PrdSet, & 'a PrdInfos)
> for Clause {
  /// Writes the clause in SMT-LIB format.
  ///
  /// The boolean flag in the info specifies whether the clause should be
  /// asserted positively (when `true`) or negatively (when `false`).
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, info: & 'b (
      bool, & 'a PrdSet, & 'a PrdSet, & 'a PrdInfos
    )
  ) -> SmtRes<()> {
    let (
      pos, ref true_preds, ref false_preds, ref prd_info
    ) = * info ;

    if ! pos {
      write!(writer, "(not ") ?
    }

    if ! self.lhs_is_empty() {
      write!(writer, "(=> (and") ?
    }

    for term in & self.lhs_terms {
      write!(writer, " ") ? ;
      term.write( writer, |w, var| var.default_write(w) ) ?
    }

    for (pred, argss) in & self.lhs_preds {
      if true_preds.contains(pred) {
        write!(writer, " true") ?
      } else if false_preds.contains(pred) {
        write!(writer, " false") ?
      } else {
        for args in argss {
          write!(writer, " (") ? ;
          writer.write_all( prd_info[* pred].name.as_bytes() ) ? ;
          for arg in args.iter() {
            write!(writer, " ") ? ;
            arg.write(writer, |w, var| var.default_write(w)) ?
          }
          write!(writer, ")") ?
        }
      }
    }

    if ! self.lhs_is_empty() {
      write!(writer, ") ") ?
    }

    if let Some((prd, ref args)) = self.rhs {
      if true_preds.contains(& prd) {
        write!(writer, "true") ?
      } else if false_preds.contains(& prd) {
        write!(writer, "false") ?
      } else {
        if ! args.is_empty() {
          write!(writer, "(") ?
        }
        write!(writer, "{}", prd_info[prd].name) ? ;
        for arg in args.iter() {
          write!(writer, " ") ? ;
          arg.write(writer, |w, var| var.default_write(w)) ?
        }
        if ! args.is_empty() {
          write!(writer, ")") ?
        }
      }
    } else {
      write!(writer, "false") ?
    }

    if ! self.lhs_is_empty() {
      write!(writer, ")") ?
    }

    if ! pos {
      write!(writer, ")") ?
    }

    Ok(())
  }
}