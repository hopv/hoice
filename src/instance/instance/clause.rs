//! Contains the clause structure for encapsulation.

use common::* ;
use instance::info::VarInfo ;

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
  lhs_terms: HConSet<Term>,
  /// Predicate applications of the left-hand side.
  lhs_preds: PredApps,
  /// Single term right-hand side.
  rhs: Option<PredApp>,
  /// Indicates wether `lhs_terms` has changed since the last call to
  /// [`lhs_terms_checked`][checked].
  ///
  /// Used by `PreInstance`'s `prune_atom`.
  ///
  /// [checked]: #methods.lhs_terms_checked
  /// (lhs_terms_checked method)
  terms_changed: bool,
  /// True if the clause is the result of unrolling.
  ///
  /// Means the terms will be ignored during mining.
  pub from_unrolling: bool,
  /// Info about who created this clause.
  pub info: & 'static str,
}
impl Clause {
  /// Creates a clause.
  pub fn new(
    vars: VarInfos, lhs: Vec<TTerm>, rhs: Option<PredApp>,
    info: & 'static str
  ) -> Self {
    let lhs_terms = HConSet::with_capacity( lhs.len() ) ;
    let lhs_preds = PredApps::with_capacity( lhs.len() ) ;
    let mut clause = Clause {
      vars, lhs_terms, lhs_preds, rhs,
      terms_changed: true, from_unrolling: false,
      info
    } ;
    for tterm in lhs { clause.lhs_insert(tterm) ; }
    clause
  }

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

  /// Sets the internal flag `terms_changed` to false.
  ///
  /// Also shrinks the variables.
  pub fn lhs_terms_checked(& mut self) {
    self.terms_changed = false ;
    self.shrink_vars()
  }

  /// True iff some terms have been added since the last call to
  /// [`lhs_terms_checked`][checked].
  ///
  /// [checked]: #methods.lhs_terms_checked
  /// (lhs_terms_checked method)
  pub fn terms_changed(& self) -> bool { self.terms_changed }

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
          if term.atom_implies(t).is_some() {
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

  /// Deactivates a variable.
  pub fn deactivate(& mut self, var: VarIdx) -> Res<()> {
    debug_assert!( self.vars[var].active ) ;
    self.vars[var].active = false ;
    self.check( "after `deactivate`" )
  }

  /// Inserts a top term in the lhs. Returns true if it was not there.
  #[inline]
  pub fn lhs_insert(& mut self, tterm: TTerm) -> bool {
    match tterm {
      TTerm::T(term) => if let Some(true) = term.bool() {
        false
      } else {
        self.insert_term(term)
      },
      TTerm::P { pred, args } => self.insert_pred_app(pred, args),
    }
  }

  /// Removes all predicate application of `pred` in the LHS.
  ///
  /// Returns true if the predicate application was there.
  #[inline]
  pub fn drop_lhs_pred(
    & mut self, pred: PrdIdx
  ) -> Option< HTArgss > {
    self.lhs_preds.remove(& pred)
  }

  /// Inserts a predicate application in the LHS.
  ///
  /// Returns true if the predicate application is new.
  #[inline]
  pub fn insert_pred_app(
    & mut self, pred: PrdIdx, args: HTArgs
  ) -> bool {
    self.lhs_preds.insert_pred_app(pred, args)
  }

  /// Checks if `term` is implied by a term in `set`.
  ///
  /// Removes the terms from `set` that are implied (strictly) by `term`.
  fn is_redundant(term: & Term, set: & mut HConSet<Term>) -> bool {
    use std::cmp::Ordering::* ;
    let mut redundant = false ;
    let mut rmed_stuff = false ;
    // println!("is redundant {}", term) ;
    set.retain(
      |t| match t.atom_implies(term) {
        // `t` is more generic, `term` is redundant, keep `t`.
        Some(Equal) | Some(Greater) => {
          redundant = true ;
          true
        },
        // `term` is more generic, discard.
        Some(Less) => {
          rmed_stuff = true ;
          // println!("  removing {}", t) ;
          false
        },
        // No relation, keep `t`.
        None => true,
      }
    ) ;
    // If we removed stuff, it means the term should not be redundant.
    assert! { ! rmed_stuff || ! redundant }
    redundant
  }

  /// Inserts a term in an LHS. Externalized for ownership reasons.
  fn lhs_insert_term(lhs_terms: & mut HConSet<Term>, term: Term) -> bool {
    // println!("inserting {}", term) ;
    let mut new_stuff = false ;
    let mut stack = vec![term] ;

    while let Some(term) = stack.pop() {
      debug_assert! { term.typ() == Typ::Bool }
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
        if ! Self::is_redundant(& term, lhs_terms) {
          let is_new = lhs_terms.insert( term.clone() ) ;
          // Should be true since term is not redundant.
          debug_assert! { is_new }
          new_stuff = new_stuff || is_new
        }
      }
    }

    return new_stuff
  }

  /// Inserts a term in the LHS.
  pub fn insert_term(& mut self, term: Term) -> bool {
    let is_new = Self::lhs_insert_term(& mut self.lhs_terms, term) ;
    if is_new {
      self.terms_changed = true ;
      true
    } else {
      false
    }
  }
  /// Removes a term from the LHS.
  pub fn rm_term(& mut self, term: & Term) -> bool {
    self.lhs_terms.remove(term)
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
  pub fn lhs_terms(& self) -> & HConSet<Term> {
    & self.lhs_terms
  }
  /// LHS accessor (predicate applications).
  #[inline]
  pub fn lhs_preds(& self) -> & PredApps {
    & self.lhs_preds
  }

  /// Drains all LHS applications.
  #[inline]
  pub fn drain_lhs_preds(
    & mut self
  ) -> ::std::collections::hash_map::Drain<PrdIdx, HTArgss> {
    self.lhs_preds.drain()
  }

  /// LHS accessor for a predicate, mutable.
  #[inline]
  pub fn lhs_pred_mut(& mut self, pred: PrdIdx) -> Option< & mut HTArgss > {
    self.lhs_preds.get_mut(& pred)
  }

  /// Maps over the arguments of a predicate in the lhs.
  #[inline]
  pub fn lhs_map_args_of<F>(& mut self, pred: PrdIdx, mut f: F)
  where F: FnMut(& HTArgs) -> HTArgs {
    if let Some(argss) = self.lhs_preds.get_mut(& pred) {
      let mut nu_argss = HTArgss::with_capacity( argss.len() ) ;
      for args in argss.iter() {
        nu_argss.insert( f(args) ) ;
      }
      ::std::mem::swap( & mut nu_argss, argss )
    }
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
  pub fn rhs(& self) -> Option<(PrdIdx, & HTArgs)> {
    if let Some((prd, ref args)) = self.rhs {
      Some((prd, args))
    } else {
      None
    }
  }
  /// RHS accessor, mutable.
  #[inline]
  pub fn rhs_mut(& mut self) -> Option<(PrdIdx, & mut HTArgs)> {
    if let Some(& mut (pred, ref mut args)) = self.rhs.as_mut() {
      Some((pred, args))
    } else {
      None
    }
  }
  /// Map over the arguments of a predicate in the rhs.
  #[inline]
  pub fn rhs_map_args<F>(& mut self, mut f: F)
  where F: FnMut(PrdIdx, & HTArgs) -> (PrdIdx, HTArgs) {
    if let Some(& mut (ref mut pred, ref mut args)) = self.rhs.as_mut() {
      let (nu_pred, mut nu_args) = f(* pred, args) ;
      * args = nu_args ;
      * pred = nu_pred
    }
  }

  /// Iterator over all predicate applications (including the rhs).
  pub fn all_pred_apps_do<F>(& self, mut f: F) -> Res<()>
  where F: FnMut(PrdIdx, & HTArgs) -> Res<()> {
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

  /// Discards the RHS of a clause.
  ///
  /// Turns the clause into a negative one.
  #[inline]
  pub fn unset_rhs(& mut self) -> Option<PredApp> {
    let mut old_rhs = None ;
    ::std::mem::swap( & mut self.rhs, & mut old_rhs ) ;
    old_rhs
  }
  /// Forces the RHS of a clause.
  #[inline]
  pub fn set_rhs(& mut self, pred: PrdIdx, args: HTArgs) -> Res<()> {
    let mut vars = VarSet::new() ;
    for arg in args.iter() {
      term::map_vars(arg, |v| { vars.insert(v) ; () })
    }
    debug_assert! {{
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
    Ok(())
  }

  /// Variables accessor.
  #[inline]
  pub fn vars(& self) -> & VarInfos {
    & self.vars
  }

  /// Clones a clause without the lhs predicate applications.
  pub fn clone_except_lhs_of(
    & self, pred: PrdIdx, info: & 'static str
  ) -> Self {
    let mut lhs_preds = PredApps::with_capacity( self.lhs_preds.len() ) ;
    for (p, argss) in & self.lhs_preds {
      if pred != * p {
        let prev = lhs_preds.insert(* p, argss.clone()) ;
        debug_assert_eq! { prev, None }
      }
    }
    Clause {
      vars: self.vars.clone(),
      lhs_terms: self.lhs_terms.clone(), lhs_preds,
      rhs: self.rhs.clone(),
      terms_changed: true,
      from_unrolling: self.from_unrolling,
      info,
    }
  }

  /// Clones a clause but changes the rhs.
  #[inline]
  pub fn clone_with_rhs(
    & self, rhs: Option<TTerm>, info: & 'static str
  ) -> Self {
    let mut lhs_terms = self.lhs_terms.clone() ;

    let (rhs, terms_changed) = match rhs {
      Some( TTerm::P { pred, args } ) => (
        Some((pred, args)), self.terms_changed
      ),
      Some( TTerm::T(term) ) => {
        let added = if term.bool() != Some(false) {
          lhs_terms.insert( term::not(term) )
        } else {
          false
        } ;
        (None, self.terms_changed || added)
      },
      None => (None, self.terms_changed),
    } ;

    Clause {
      vars: self.vars.clone(),
      lhs_terms,
      lhs_preds: self.lhs_preds.clone(),
      rhs,
      terms_changed,
      from_unrolling: self.from_unrolling,
      info
    }
  }


  /// Removes all redundant terms from `lhs_terms`.
  fn prune(& mut self) {
    use std::cmp::Ordering::* ;
    let mut to_rm = HConSet::<Term>::new() ;
    scoped! {
      let mut terms = self.lhs_terms.iter() ;
      while let Some(term) = terms.next() {
        for t in terms.clone() {
          match t.atom_implies(term) {
            // `t` is more generic, `term` is redundant, keep `t`.
            Some(Equal) | Some(Greater) => {
              to_rm.insert( term.clone() ) ;
            },
            // `term` is more generic, discard `t`.
            Some(Less) => {
              to_rm.insert( t.clone() ) ;
            },
            // No relation.
            None => (),
          }
        }
      }
    }
    for to_rm in to_rm {
      let was_there = self.lhs_terms.remove(& to_rm) ;
      debug_assert! { was_there }
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
    for (_, argss) in & mut self.lhs_preds {
      let mut nu_argss = HTArgss::with_capacity( argss.len() ) ;
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
      ::std::mem::swap(& mut nu_argss, argss)
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

    if changed { self.prune() }

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
      let info = VarInfo::new(fresh_name, * typ, fresh) ;
      self.vars.push(info) ;
      let _prev = map.insert(* var, term::var(fresh, * typ)) ;
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
        let info = VarInfo::new(fresh_name, * typ, fresh) ;
        self.vars.push(info) ;
        let _prev = map.insert(* var, term::var(fresh, * typ)) ;
        debug_assert!( _prev.is_none() )
      }
      map
    } else {
      return VarHMap::new()
    }
  }

  /// Declares all active clause variables.
  pub fn declare<Parser>(
    & self, solver: & mut Solver<Parser>
  ) -> Res<()> {
    for var in self.vars() {
      if var.active {
        solver.declare_const(& var.idx, & var.typ) ?
      }
    }
    Ok(())
  }

  /// Writes a clause given a special function to write predicates.  
  pub fn write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & HTArgs) -> IoRes<()> {

    write!(w, "({} ({}\n  (", keywords::cmd::assert, keywords::forall) ? ;
    let mut inactive = 0 ;
    for var in & self.vars {
      if var.active {
        write!(w, " ({} {})", var.name, var.typ) ?
      } else {
        inactive += 1 ;
      }
    }
    write!(w, " )") ? ;
    write!(
      w, "\n  \
        ; {} inactive variable(s)\n  \
        ; unroll: {}\n  \
        ; terms_changed: {}\n  \
        ; created by `{}`\n\
      ",
      inactive, self.from_unrolling, self.terms_changed, self.info
    ) ? ;

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
    if let Some((pred, ref args)) = self.rhs {
      write_prd(w, pred, args) ?
    } else {
      write!(w, "false") ?
    }
    write!(w, "\n") ? ;
    if let Some(suff) = suff {
      write!(w, "{}\n", suff) ?
    }
    write!(w, "))")
  }
}
impl ::std::ops::Index<VarIdx> for Clause {
  type Output = VarInfo ;
  fn index(& self, index: VarIdx) -> & VarInfo {
    & self.vars[index]
  }
}
impl<'a, 'b> ::rsmt2::to_smt::Expr2Smt<
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
      writer.write_all( " ".as_bytes() ) ? ;
      term.write( writer, |w, var| var.default_write(w) ) ?
    }

    for (pred, argss) in & self.lhs_preds {
      if true_preds.contains(pred) {
        writer.write_all( " true".as_bytes() ) ?
      } else if false_preds.contains(pred) {
        writer.write_all( " false".as_bytes() ) ?
      } else {
        for args in argss {
          writer.write_all( " (".as_bytes() ) ? ;
          writer.write_all( prd_info[* pred].name.as_bytes() ) ? ;
          for arg in args.iter() {
            writer.write_all( " ".as_bytes() ) ? ;
            arg.write(writer, |w, var| var.default_write(w)) ?
          }
          writer.write_all( ")".as_bytes() ) ?
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
        write!(writer, "({}", prd_info[prd].name) ? ;
        for arg in args.iter() {
          write!(writer, " ") ? ;
          arg.write(writer, |w, var| var.default_write(w)) ?
        }
        write!(writer, ")") ?
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