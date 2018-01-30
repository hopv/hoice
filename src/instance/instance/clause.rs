//! Contains the clause structure for encapsulation.

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
  term_changed: bool
}
impl Clause {
  /// Creates a clause.
  pub fn new(
    vars: VarMap<VarInfo>, lhs: Vec<TTerm>, rhs: Option<PredApp>
  ) -> Self {
    let lhs_terms = HConSet::with_capacity( lhs.len() ) ;
    let lhs_preds = PredApps::with_capacity( lhs.len() ) ;
    let mut clause = Clause {
      vars, lhs_terms, lhs_preds, rhs, term_changed: true
    } ;
    for tterm in lhs { clause.lhs_insert(tterm) ; }
    clause
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

  /// Sets the internal flag `term_changed` to false.
  ///
  /// Also shrinks the variables.
  pub fn lhs_terms_checked(& mut self) {
    self.term_changed = false ;
    self.shrink_vars()
  }

  /// True iff some terms have been added since the last call to
  /// [`lhs_terms_checked`][checked].
  ///
  /// [checked]: #methods.lhs_terms_checked
  /// (lhs_terms_checked method)
  pub fn terms_changed(& self) -> bool { self.term_changed }

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
        for arg in args {
          term::map_vars(arg, |v| { vars.insert(v) ; () }) ;
        }
      }
      if vars.len() == active {
        return ()
      }
    }

    if let Some(& (_, ref args)) = self.rhs.as_ref() {
      for arg in args {
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
    for (_, argss) in & self.lhs_preds {
      for args in argss {
        for arg in args {
          vars.extend( term::vars(arg) )
        }
      }
    }
    if let Some((_, ref args)) = self.rhs {
      for arg in args {
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
  #[inline(always)]
  pub fn drop_lhs_pred(
    & mut self, pred: PrdIdx
  ) -> Option< Vec<TArgs> > {
    self.lhs_preds.remove(& pred)
  }

  /// Inserts a predicate application in the LHS.
  ///
  /// Returns true if the predicate application is new.
  #[inline(always)]
  pub fn insert_pred_app(
    & mut self, pred: PrdIdx, args: TArgs
  ) -> bool {
    self.lhs_preds.insert_pred_app(pred, args)
  }

  /// Inserts a term in an LHS. Externalized for ownership reasons.
  fn lhs_insert_term(lhs_terms: & mut HConSet<Term>, term: Term) -> bool {
    if let Some(kids) = term.conj_inspect() {
      let mut new_stuff = false ;
      let mut stack = vec![] ;
      for kid in kids {
        if let Some(kids) = kid.conj_inspect() {
          for kid in kids { stack.push(kid) }
        } else if let Some(true) = term.bool() {
          ()
        } else {
          let is_new = lhs_terms.insert( kid.clone() ) ;
          new_stuff = new_stuff || is_new
        }
      }
      while let Some(term) = stack.pop() {
        if let Some(kids) = term.conj_inspect() {
          for kid in kids { stack.push(kid) }
        } else if let Some(true) = term.bool() {
          ()
        } else {
          let is_new = lhs_terms.insert( term.clone() ) ;
          new_stuff = new_stuff || is_new
        }
      }
      return new_stuff
    }

    // Only reachable when `term.conj_inspect()` is `None`. Needs to be outside
    // the match because of lexical lifetimes.
    if let Some(true) = term.bool() {
      false
    } else {
      lhs_terms.insert(term)
    }
  }

  /// Inserts a term in the LHS.
  pub fn insert_term(& mut self, term: Term) -> bool {
    let is_new = Self::lhs_insert_term(& mut self.lhs_terms, term) ;
    if is_new {
      self.term_changed = true
    }
    is_new
  }
  /// Removes a term from the LHS.
  pub fn rm_term(& mut self, term: & Term) -> bool {
    self.lhs_terms.remove(term)
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
  pub fn lhs_terms(& self) -> & HConSet<Term> {
    & self.lhs_terms
  }
  /// LHS accessor (predicate applications).
  #[inline(always)]
  pub fn lhs_preds(& self) -> & PredApps {
    & self.lhs_preds
  }

  /// LHS accessor for a predicate, mutable.
  #[inline]
  pub fn lhs_pred_mut(& mut self, pred: PrdIdx) -> Option< & mut Vec<TArgs> > {
    self.lhs_preds.get_mut(& pred)
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
  pub fn rhs(& self) -> Option<(PrdIdx, & TArgs)> {
    if let Some((prd, ref args)) = self.rhs {
      Some((prd, args))
    } else {
      None
    }
  }
  /// RHS accessor, mutable.
  #[inline]
  pub fn rhs_mut(& mut self) -> Option<(PrdIdx, & mut TArgs)> {
    if let Some(& mut (pred, ref mut args)) = self.rhs.as_mut() {
      Some((pred, args))
    } else {
      None
    }
  }

  /// Iterator over all predicate applications (including the rhs).
  pub fn all_pred_apps_do<F>(& self, mut f: F) -> Res<()>
  where F: FnMut(PrdIdx, & TArgs) -> Res<()> {
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
  pub fn set_rhs(& mut self, pred: PrdIdx, args: TArgs) -> Res<()> {
    let mut vars = VarSet::new() ;
    for arg in & args {
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
  #[inline(always)]
  pub fn vars(& self) -> & VarMap<VarInfo> {
    & self.vars
  }

  /// Clones a clause but changes the rhs.
  #[inline(always)]
  pub fn clone_with_rhs(& self, rhs: TTerm) -> Self {
    let mut lhs_terms = self.lhs_terms.clone() ;
    let (rhs, term_changed) = match rhs {
      TTerm::P { pred, args } => (
        Some((pred, args)), self.term_changed
      ),
      TTerm::T(term) => {
        let added = if term.bool() != Some(false) {
          lhs_terms.insert( term::not(term) )
        } else {
          false
        } ;
        (None, self.term_changed || added)
      },
    } ;
    Clause {
      vars: self.vars.clone(),
      lhs_terms,
      lhs_preds: self.lhs_preds.clone(),
      rhs,
      term_changed,
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
      let mut nu_argss = Vec::with_capacity( argss.len() ) ;
      debug_assert!( nu_argss.is_empty() ) ;
      for mut args in argss.drain(0..) {
        for arg in args.iter_mut() {
          let (nu_arg, b) = arg.subst(map) ;
          * arg = nu_arg ;
          changed = changed || b
        }
        nu_argss.push(args) ;
      }
      ::std::mem::swap(& mut nu_argss, argss)
    }
    if let Some(& mut (_, ref mut args)) = self.rhs.as_mut() {
      for arg in args.iter_mut() {
        let (nu_arg, b) = arg.subst(map) ;
        * arg = nu_arg ;
        changed = changed || b
      }
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
      let info = VarInfo::new(fresh_name, * typ, fresh) ;
      self.vars.push(info) ;
      let _prev = map.insert(* var, term::var(fresh)) ;
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
        let _prev = map.insert(* var, term::var(fresh)) ;
        debug_assert!( _prev.is_none() )
      }
      map
    } else {
      return VarHMap::new()
    }
  }

  /// Writes a clause given a special function to write predicates.  
  pub fn write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & TArgs) -> IoRes<()> {

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
  & 'b (& 'a PrdSet, & 'a PrdSet, & 'a PrdMap<PrdInfo>)
> for Clause {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, info: & 'b (
      & 'a PrdSet, & 'a PrdSet, & 'a PrdMap<PrdInfo>
    )
  ) -> SmtRes<()> {
    let (ref true_preds, ref false_preds, ref prd_info) = * info ;
    write!(writer, "(not ") ? ;
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
          for arg in args {
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
        for arg in args {
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
    write!(writer, ")") ? ;
    Ok(())
  }
}