//! Helper types and functions for preprocessing.

use common::* ;
use instance::info::* ;


/// Result of extracting the terms for a predicate application in a clause.
#[derive(Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum ExtractRes<T = Vec<TTerm>> {
  /// The clause was found to be trivially true.
  Trivial,
  /// Terms could not be extracted.
  ///
  /// Returned when the variables appearing in the application and the other
  /// variables `others` of the clause are related, or if there is a predicate
  /// application mentioning variables from `others`.
  Failed,
  /// Success, predicate is equivalent to true.
  SuccessTrue,
  /// Success, predicate is equivalent to false.
  SuccessFalse,
  /// Success, predicate is equivalent to some top terms.
  Success(T),
}
impl<T: PartialEq + Eq> ExtractRes<T> {
  /// True if failed.
  pub fn is_failed(& self) -> bool{ * self == ExtractRes::Failed }
}



/// Creates fresh (quantified) variables for the variables that are not
/// currently known.
///
/// - `$quantifiers` if `false` and quantified variables are needed, early
///   return with `ExtractRes::Failed` instead of creating fresh variables
/// - `$vars` the variables we're considering
/// - `$app_vars` currently known variables
/// - `$map` map from clause variables to predicate variables
/// - `$qvars` map from quantified variables to their `VarInfo`
/// - `$info` the clause's `VarInfo`s (used to retrieve types)
/// - `$fresh` the next fresh variable for the predicate
macro_rules! add_vars {
  (
    if $quantifiers:ident : $vars:expr => $app_vars:ident
    |> $map:expr, $qvars:expr, $info:expr, $fresh:expr
  ) => (
    for var in $vars {
      let is_new = $app_vars.insert(var) ;
      if is_new {
        if ! $quantifiers {
          return Ok( TExtractRes::Failed )
        }
        let _prev = $qvars.insert(* $fresh, $info[var].typ) ;
        debug_assert_eq!( None, _prev ) ;
        log_info! { "    adding fresh v_{} for {}", $fresh, $info[var] }
        let _prev = $map.insert( var, term::var(* $fresh) ) ;
        debug_assert_eq!( None, _prev ) ;
        $fresh.inc()
      }
    }
  ) ;
}




/// Results of term extraction.
pub enum TExtractRes<T> {
  /// Success.
  Success(T),
  /// Failure: need qualifiers.
  Failed,
}


/// Applies a map to some predicate applications, generating quantifiers if
/// necessary and `quantifiers` is true.
///
/// Returns `None` on failure. Failure happens when some quantifiers are
/// needed but `quantifiers` is false.
fn args_of_pred_app(
  quantifiers: bool, var_info: & VarMap<VarInfo>,
  args: & VarMap<Term>,
  app_vars: & mut VarSet, map: & mut VarHMap<Term>,
  qvars: & mut VarHMap<Typ>, fresh: & mut VarIdx
) -> Res< TExtractRes<VarMap<Term>> > {
  log_debug! { "      args_of_pred_app ({})", quantifiers }
  let mut nu_args = VarMap::with_capacity( args.len() ) ;
  for arg in args {
    add_vars! {
      if quantifiers: term::vars(arg) =>
        app_vars |> map, qvars, var_info, fresh
    }
    if let Some((nu_arg, _)) = arg.subst_total(map) {
      nu_args.push(nu_arg)
    } else {
      bail!("unreachable, substitution was not total")
    }
  }
  Ok( TExtractRes::Success( nu_args ) )
}



/// Applies a map to some predicate applications, generating quantifiers if
/// necessary and `quantifiers` is true.
///
/// The `pred` argument is a special predicate that will be skipped when
/// handling `src`, but it's arguments will be returned.
fn terms_of_pred_apps<'a>(
  quantifiers: bool, var_info: & VarMap<VarInfo>,
  src: & 'a PredApps, tgt: & mut Vec<PredApp>,
  pred: PrdIdx, app_vars: & mut VarSet,
  map: & mut VarHMap<Term>,
  qvars: & mut VarHMap<Typ>, fresh: & mut VarIdx
) -> Res< TExtractRes< Option<& 'a Vec<VarMap<Term>> > > > {
  log_debug! { "    terms_of_pred_apps" }
  let mut res = None ;
  for (prd, argss) in src {

    let prd = * prd ;
    if prd == pred {
      res = Some(argss) ;
      continue
    }

    for args in argss {
      match args_of_pred_app(
        quantifiers, var_info, args, app_vars, map, qvars, fresh
      ) ? {
        TExtractRes::Success(nu_args) => tgt.push( (prd, nu_args) ),
        TExtractRes::Failed => {
          log_debug! { "    failed to extract argument {}", args }
          return Ok(TExtractRes::Failed)
        },
      }
    }
  }
  Ok( TExtractRes::Success(res) )
}


/// Applies a map to some terms, generating quantifiers if necessary and
/// `quantifiers` is true.
///
/// Argument `even_if_disjoint` forces to add terms even if its variables
/// are disjoint from `app_vars`.
///
/// Returns `true` if one of the `src` terms is false (think `is_trivial`).
fn terms_of_terms<'a, TermIter, Terms, F>(
  quantifiers: bool, var_info: & VarMap<VarInfo>,
  src: Terms, tgt: & mut HConSet<Term>,
  app_vars: & mut VarSet, map: & mut VarHMap<Term>,
  qvars: & mut VarHMap<Typ>, fresh: & mut VarIdx,
  even_if_disjoint: bool, f: F
) -> Res< TExtractRes<bool> >
where
TermIter: Iterator<Item = & 'a Term> + ExactSizeIterator,
Terms: IntoIterator<IntoIter = TermIter, Item = & 'a Term>,
F: Fn(Term) -> Term {
  log_debug! { "    terms_of_terms" }

  // Finds terms which variables are related to the ones from the predicate
  // applications.
  let src = src.into_iter() ;

  // The terms we're currently looking at.
  let mut lhs_terms_vec: Vec<_> = Vec::with_capacity( src.len() ) ;
  for term in src {
    match term.bool() {
      Some(true) => (),
      Some(false) => return Ok( TExtractRes::Success(true) ),
      _ => lhs_terms_vec.push(term),
    }
  }
  // Terms which variables are disjoint from `app_vars` **for now**. This
  // might change as we generate quantified variables.
  let mut postponed: Vec<_> = Vec::with_capacity( lhs_terms_vec.len() ) ;


  // A fixed point is reached when we go through the terms in `lhs_terms_vec`
  // and don't generate quantified variables.
  loop {
    let mut fixed_point = true ;

    if_not_bench! {
      log_debug! { "      app vars:" }
      for var in app_vars.iter() {
        log_debug! { "      - {}", var_info[* var] }
      }
      log_debug! { "      map:" }
      for (var, term) in map.iter() {
        log_debug! { "      - v_{} -> {}", var, term }
      }
    }

    for term in lhs_terms_vec.drain(0..) {
      log_debug! { "      {}", term.to_string_info(var_info) ? }
      let vars = term::vars(term) ;

      if app_vars.len() == var_info.len()
      || vars.is_subset(& app_vars) {
        let term = if let Some((term, _)) = term.subst_total(map) {
          term
        } else {
          bail!("[unreachable] failure during total substitution (1)")
        } ;
        log_debug! { "      sub {}", term }
        tgt.insert( f(term) ) ;

      } else if ! even_if_disjoint && vars.is_disjoint(& app_vars) {
        log_debug! { "      disjoint" }
        postponed.push(term)

      } else {
        // The term mentions variables from `app_vars` and other variables.
        // We generate quantified variables to account for them and
        // invalidate `fixed_point` since terms that were previously disjoint
        // might now intersect.
        fixed_point = false ;
        add_vars! {
          if quantifiers: vars =>
            app_vars |> map, qvars, var_info, fresh
        }
        let term = if let Some((term, _)) = term.subst_total(map) {
          term
        } else {
          bail!("[unreachable] failure during total substitution (2)")
        } ;
        tgt.insert( f(term) ) ;
      }

    }

    if fixed_point || postponed.is_empty() {
      break
    } else {
      // Iterating over posponed terms next.
      ::std::mem::swap(
        & mut lhs_terms_vec, & mut postponed
      )
    }

  }    

  Ok( TExtractRes::Success(false) )
}




/// Given a predicate application, returns the constraints on the input and a
/// map from the variables used in the arguments to the variables of the
/// predicate.
///
/// # TODO
///
/// - more doc with examples
pub fn terms_of_app(
  quantifiers: bool, var_info: & VarMap<VarInfo>,
  instance: & Instance, pred: PrdIdx, args: & VarMap<Term>,
  fresh: & mut VarIdx, qvars: & mut VarHMap<Typ>
) -> Res<
  Option<(HConSet<Term>, VarHMap<Term>, VarSet)>
> {
  let mut map = VarHMap::with_capacity( instance[pred].sig.len() ) ;
  let mut app_vars = VarSet::with_capacity( instance[pred].sig.len() ) ;
  let mut terms = HConSet::with_capacity( 7 ) ;

  // Will store the arguments that are not a variable or a constant.
  let mut postponed = Vec::with_capacity( args.len() ) ;

  for (index, arg) in args.index_iter() {
    if let Some(var) = arg.var_idx() {
      let _ = app_vars.insert(var) ;
      if let Some(pre) = map.insert(var, term::var(index)) {
        terms.insert(
          term::eq( term::var(index), pre )
        ) ;
      }
    } else if let Some(b) = arg.bool() {
      let var = term::var(index) ;
      terms.insert(
        if b { var } else { term::not(var) }
      ) ;
    } else if let Some(i) = arg.int() {
      terms.insert(
        term::eq( term::var(index), term::int(i) )
      ) ;
    } else {
      postponed.push( (index, arg) ) ;
    }
  }

  for (var, arg) in postponed {
    if let Some( (term, _) ) = arg.subst_total(& map) {
      terms.insert(
        term::eq(term::var(var), term)
      ) ;
    } else if let Some((v, inverted)) = arg.invert(var) {
      let _prev = map.insert(v, inverted) ;
      debug_assert_eq!( _prev, None ) ;
      let is_new = app_vars.insert(v) ;
      debug_assert!( is_new )
    } else {
      if let TExtractRes::Failed = terms_of_terms(
        quantifiers, var_info, Some(arg), & mut terms,
        & mut app_vars, & mut map, qvars, fresh,
        true, |term| term::eq( term::var(var), term )
      ) ? {
        return Ok(None)
      }
    }
  }

  Ok( Some( (terms, map, app_vars) ) )
}



/// Returns the weakest predicate `p` such that `(p args) /\ lhs_terms /\
/// {lhs_preds \ (p args)} => rhs`.
///
/// Quantified variables are understood as universally quantified.
///
/// The result is `(pred_app, pred_apps, terms)` which semantics is `pred_app
/// \/ (not /\ tterms) \/ (not /\ pred_apps)`.
pub fn terms_of_lhs_app(
  quantifiers: bool, instance: & Instance, var_info: & VarMap<VarInfo>,
  lhs_terms: & HConSet<Term>, lhs_preds: & PredApps,
  rhs: Option<(PrdIdx, & VarMap<Term>)>,
  pred: PrdIdx, args: & VarMap<Term>,
) -> Res<
  ExtractRes<(Quantfed, Option<PredApp>, Vec<PredApp>, HConSet<Term>)>
> {
  log_debug!{
    "    terms_of_lhs_app on {} {} ({})", instance[pred], args, quantifiers
  }

  // Index of the first quantified variable: fresh for `pred`'s variables.
  let mut fresh = instance[pred].sig.next_index() ;
  let fresh = & mut fresh ;

  let mut qvars = VarHMap::with_capacity(
    if quantifiers { var_info.len() } else { 0 }
  ) ;

  log_debug!{
    "    extracting application's terms"
  }

  let (
    mut terms, mut map, mut app_vars
  ) = if let Some(res) = terms_of_app(
    quantifiers, var_info, instance, pred, args, fresh, & mut qvars
  ) ? {
    res
  } else {
    log_debug!{ "    failed to extract terms of application" }
    return Ok(ExtractRes::Failed)
  } ;

  if_not_bench! {
    log_debug! { "    terms:" }
    for term in & terms {
      log_debug!{ "    - {}", term }
    }
    log_debug! { "    map:" }
    for (var, term) in & map {
      log_debug! { "    - v_{} -> {}", var, term }
    }
  }

  log_debug! {
    "    working on lhs predicate applications ({})", lhs_preds.len()
  }

  let mut pred_apps = Vec::with_capacity( lhs_preds.len() ) ;

  // Predicate applications need to be in the resulting term. Depending on
  // the definition they end up having, the constraint might be trivial.
  match terms_of_pred_apps(
    quantifiers, var_info, lhs_preds, & mut pred_apps,
    pred, & mut app_vars, & mut map, & mut qvars, fresh
  ) ? {
    TExtractRes::Success( Some(pred_argss) ) => match pred_argss.len() {
      1 => (),
      len => bail!(
        "illegal call to `terms_of_lhs_app`, \
        predicate {} is applied {} time(s), expected 1",
        instance[pred], len
      ),
    },
    TExtractRes::Success(None) => (),
    TExtractRes::Failed => {
      log_debug!{ "    qualifiers required for lhs pred apps" }
      return Ok( ExtractRes::Failed )
    },
  }

  let pred_app = if let Some((pred, args)) = rhs {
    log_debug! {
      "    working on rhs predicate application"
    }
    if let TExtractRes::Success(nu_args) = args_of_pred_app(
      quantifiers, var_info, args, & mut app_vars,
      & mut map, & mut qvars, fresh
    ) ? {
      Some((pred, nu_args))
    } else {
      log_debug!{ "    qualifiers required for rhs pred app" }
      return Ok( ExtractRes::Failed )
    }
  } else {
    log_debug! { "    no rhs predicate application" }
    None
  } ;

  log_debug! {
    "    working on lhs terms ({})", lhs_terms.len()
  }

  if let TExtractRes::Success(trivial) = terms_of_terms(
    quantifiers, var_info, lhs_terms, & mut terms,
    & mut app_vars, & mut map, & mut qvars, fresh, false, identity
  ) ? {
    if trivial { return Ok( ExtractRes::Trivial ) }
  } else {
    log_debug!{ "    qualifiers required for lhs terms" }
    return Ok( ExtractRes::Failed )
  }

  debug_assert! { quantifiers || qvars.is_empty() }

  Ok( ExtractRes::Success( (qvars, pred_app, pred_apps, terms) ) )
}


/// Returns the weakest predicate `p` such that `lhs_terms /\ lhs_preds => (p
/// args)`.
///
/// Quantified variables are understood as existentially quantified.
///
/// The result is `(pred_apps, terms)` which semantics is `pred_app /\
/// tterms`.
pub fn terms_of_rhs_app(
  quantifiers: bool, instance: & Instance, var_info: & VarMap<VarInfo>,
  lhs_terms: & HConSet<Term>, lhs_preds: & PredApps,
  pred: PrdIdx, args: & VarMap<Term>,
) -> Res< ExtractRes<(Quantfed, Vec<PredApp>, HConSet<Term>)> > {
  log_debug!{ "  terms of rhs app on {} {}", instance[pred], args }

  // Index of the first quantified variable: fresh for `pred`'s variables.
  let mut fresh = instance[pred].sig.next_index() ;
  let fresh = & mut fresh ;

  let mut qvars = VarHMap::with_capacity(
    if quantifiers { var_info.len() } else { 0 }
  ) ;

  log_debug!{
    "    extracting application's terms"
  }

  let (
    mut terms, mut map, mut app_vars
  ) = if let Some(res) = terms_of_app(
    quantifiers, var_info, instance, pred, args, fresh, & mut qvars
  ) ? {
    res
  } else {
    log_debug! { "  could not extract terms of app" }
    return Ok(ExtractRes::Failed)
  } ;

  if_not_bench! {
    log_debug! { "    terms:" }
    for term in & terms {
      log_debug! { "    - {}", term }
    }
    log_debug! { "    map:" }
    for (var, term) in & map {
      log_debug! { "    - v_{} -> {}", var, term }
    }
  }

  log_debug! {
    "    working on lhs predicate applications ({})", lhs_preds.len()
  }

  let mut pred_apps = Vec::with_capacity( lhs_preds.len() ) ;

  // Predicate applications need to be in the resulting term. Depending on
  // the definition they end up having, the constraint might be trivial.
  match terms_of_pred_apps(
    quantifiers, var_info, lhs_preds, & mut pred_apps,
    pred, & mut app_vars, & mut map, & mut qvars, fresh
  ) ? {
    TExtractRes::Success( Some(pred_argss) ) => if ! pred_argss.is_empty() {
      bail!(
        "illegal call to `terms_of_rhs_app`, \
        predicate {} appears in the lhs",
        instance[pred]
      )
    },
    TExtractRes::Success(None) => (),
    TExtractRes::Failed => {
      log_debug! {
        "  could not extract terms of predicate app ({})", instance[pred]
      }
      return Ok( ExtractRes::Failed )
    },
  }

  log_debug! {
    "    working on lhs terms ({})", lhs_terms.len()
  }

  if let TExtractRes::Success(trivial) = terms_of_terms(
    quantifiers, var_info, lhs_terms, & mut terms,
    & mut app_vars, & mut map, & mut qvars, fresh, false, identity
  ) ? {
    if trivial { return Ok( ExtractRes::Trivial ) }
  } else {
    log_debug! { "  could not extract terms of terms" }
    return Ok( ExtractRes::Failed )
  }

  debug_assert! { quantifiers || qvars.is_empty() }

  if terms.is_empty() && pred_apps.is_empty() {
    Ok(ExtractRes::SuccessTrue)
  } else {
    Ok(
      ExtractRes::Success( (qvars, pred_apps, terms) )
    )
  }
}