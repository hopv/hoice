#![doc = r#"Reduction strategies.

The strategies are attached `struct`s so that they can be put in a
vector using single dispatch. That way, they can be combined however we want.
"#]

use common::* ;
use instance::* ;



/// Information returned by [`RedStrat`](trait.RedStrat.html)s and
/// [`SolverRedStrat`](trait.SolverRedStrat.html)s.
pub struct RedInfo {
  /// Number of predicates eliminated.
  pub preds: usize,
  /// Number of clauses removed.
  pub clauses_rmed: usize,
  /// Number of clauses created.
  pub clauses_added: usize,
}
impl RedInfo {
  /// True if one or more fields are non-zero.
  pub fn non_zero(& self) -> bool {
    self.preds > 0 || self.clauses_rmed > 0 || self.clauses_added > 0
  }
}
impl From<(usize, usize, usize)> for RedInfo {
  fn from(
    (preds, clauses_rmed, clauses_added): (usize, usize, usize)
  ) -> RedInfo {
    RedInfo { preds, clauses_rmed, clauses_added }
  }
}
impl ::std::ops::AddAssign for RedInfo {
  fn add_assign(
    & mut self, RedInfo { preds, clauses_rmed, clauses_added }: Self
  ) {
    self.preds += preds ;
    self.clauses_rmed += clauses_rmed ;
    self.clauses_added += clauses_added
  }
}



/// Runs pre-processing
pub fn work(
  instance: & mut Instance, profiler: & Profiler
) -> Res<()> {

  profile!{ |profiler| tick "pre-proc" }
  log_info!{ "starting pre-processing" }

  let res = if conf.preproc.simple_red {
    let mut kid = ::rsmt2::Kid::new( conf.solver.conf() ).chain_err(
      || ErrorKind::Z3SpawnError
    ) ? ;
    let solver = ::rsmt2::solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    if let Some(log) = conf.solver.log_file("preproc") ? {
      run(
        instance, profiler, Some( SolverWrapper { solver: solver.tee(log) } )
        )
    } else {
      run( instance, profiler, Some( SolverWrapper { solver } ) )
    }
  } else {
    run(
      instance, profiler,
      None as Option< SolverWrapper<::rsmt2::PlainSolver<Parser>> >
    )
  } ;
  profile!{ |profiler| mark "pre-proc" } ;
  log_info!{ "done with pre-processing" }
  log_info!{
    "done with pre-processing:\n{}\n\n", instance.to_string_info(()) ?
  }
  res

}

pub fn run<'kid, S: Solver<'kid, Parser>>(
  instance: & mut Instance,
  profiler: & Profiler, solver: Option< SolverWrapper<S> >
) -> Res<()> {
  let mut reductor = Reductor::new(solver) ;
  let mut total: RedInfo = (0, 0, 0).into() ;

  log_info!{ "running simplification" }
  instance.check("before simplification") ? ;
  profile!{ |profiler| tick "pre-proc", "simplify" }
  instance.simplify_clauses() ? ;
  profile!{ |profiler| mark "pre-proc", "simplify" }

  profile!{ |profiler| tick "pre-proc", "simplifying" }
  total += reductor.run_simplification(instance, & profiler) ? ;
  profile!{ |profiler| mark "pre-proc", "simplifying" }


  log_info!{
    "|===| after simplification:\n{}\n\n", instance.to_string_info(()) ?
  }



  let mut changed = true ;
  'preproc: while changed {

    log_info!{ "running reduction" }
    profile!{ |profiler| tick "pre-proc", "reducing" }
    let red_info = reductor.run(instance, & profiler) ? ;
    changed = red_info.non_zero() ;
    total += red_info ;
    instance.check("after reduction") ? ;
    profile!{ |profiler| mark "pre-proc", "reducing" }
    log_info!{ "done reducing" }

    log_info!{
      "\n\n\n|===|instance after reduction:\n{}\n\n", instance.to_string_info(()) ?
    }

  }

  profile!{
    |profiler| "predicates eliminated" => add total.preds
  }
  profile!{
    |profiler| "clauses eliminated" => add total.clauses_rmed
  }
  profile!{
    |profiler| "clauses created" => add total.clauses_added
  }

  Ok(())
}





/// Reductor, stores the reduction strategies and a solver.
pub struct Reductor<'kid, S: Solver<'kid, Parser>> {
  /// Strategies.
  strats: Vec< Box<RedStrat> >,
  /// Solver strats.
  solver_strats: Option< (
    SolverWrapper<S>, Vec< Box<SolverRedStrat<'kid, S>> >
  ) >,
}
impl<'kid, S: Solver<'kid, Parser>> Reductor<'kid, S> {
  /// Constructor.
  pub fn new(solver: Option< SolverWrapper<S> >) -> Self {
    let strats: Vec< Box<RedStrat> > = vec![
      Box::new( Trivial {} ),
      // Box::new( ForcedImplies::new() ),
    ] ;
    let mut solver_strats: Vec< Box<SolverRedStrat<'kid, S>> > = vec![
      Box::new( SmtTrivial::new() ),
    ] ;
    if conf.preproc.simple_red {
      solver_strats.push( Box::new( SimpleOneRhs::new() ) ) ;
      // solver_strats.push( Box::new( SimpleOneLhs::new() ) ) ;
      solver_strats.push( Box::new( MonoPredClause::new() ) )
    }
    let solver_strats = solver.map(
      |solver| (solver, solver_strats)
    ) ;

    Reductor { strats, solver_strats }
  }

  /// Runs instance simplification.
  pub fn run_simplification(
    & mut self, instance: & mut Instance, _profiler: & Profiler
  ) -> Res<RedInfo> {
    #![allow(unused_mut, unused_variables)]
    let mut total: RedInfo = (0,0,0).into() ;
    
    let mut changed = true ;
    while changed {
      changed = false ;
      for strat in & mut self.strats {
        log_info!("applying {}", conf.emph( strat.name() )) ;
        profile!{ |_profiler| tick "pre-proc", "simplifying", strat.name() }
        let red_info = strat.apply(instance) ? ;
        changed = changed || red_info.non_zero() ;
        if_not_bench!{
          profile!{ |_profiler| mark "pre-proc", "simplifying", strat.name() }
          profile!{
            |_profiler| format!(
              "{:>25}   pred red", strat.name()
            ) => add red_info.preds
          }
          profile!{
            |_profiler| format!(
              "{:>25} clause red", strat.name()
            ) => add red_info.clauses_rmed
          }
          profile!{
            |_profiler| format!(
              "{:>25} clause add", strat.name()
            ) => add red_info.clauses_added
          }
        }

        total += red_info ;
        instance.check( strat.name() ) ? ;

        // let mut dummy = String::new() ;
        // println!("") ;
        // println!( "; waiting..." ) ;
        // let _ = ::std::io::stdin().read_line(& mut dummy) ;
      }
    }

    Ok(total)
  }

  /// Runs expensive reduction.
  pub fn run(
    & mut self, instance: & mut Instance, _profiler: & Profiler
  ) -> Res<RedInfo> {
    let mut total: RedInfo = (0, 0, 0).into() ;
    
    // let mut changed = true ;
    // while changed {
    //   changed = false ;
    //   for strat in & mut self.strats {
    //     log_info!("applying {}", conf.emph( strat.name() )) ;
    //     profile!{ |_profiler| tick "pre-proc", "reducing", strat.name() }
    //     let (pred_cnt, clse_cnt) = strat.apply(instance) ? ;
    //     changed = changed || pred_cnt + clse_cnt > 0 ;
    //     if_not_bench!{
    //       preds += pred_cnt ;
    //       clauses += clse_cnt ;
    //       profile!{
    //         |_profiler| format!("{} pred red", strat.name()) => add pred_cnt
    //       }
    //       profile!{
    //         |_profiler| format!("{} clause red", strat.name()) => add clse_cnt
    //       }
    //     }
    //     profile!{ |_profiler| mark "pre-proc", "reducing", strat.name() }
    //     instance.check( strat.name() ) ? ;

    //     let mut dummy = String::new() ;
    //     println!("") ;
    //     println!( "; waiting..." ) ;
    //     let _ = ::std::io::stdin().read_line(& mut dummy) ;
    //   }
    // }

    if let Some((ref mut solver, ref mut strats)) = self.solver_strats {
      let mut changed = true ;
      while changed {
        changed = false ;

        for strat in strats.iter_mut() {
          log_info!("applying {}", conf.emph( strat.name() )) ;
          profile!{ |_profiler| tick "pre-proc", "reducing", strat.name() }
          let red_info = strat.apply(instance, solver) ? ;
          changed = changed || red_info.non_zero() ;

          if_not_bench!{
            profile!{ |_profiler| mark "pre-proc", "reducing", strat.name() }
            profile!{
              |_profiler| format!(
                "{:>25}   pred red", strat.name()
              ) => add red_info.preds
            }
            profile!{
              |_profiler| format!(
                "{:>25} clause red", strat.name()
              ) => add red_info.clauses_rmed
            }
            profile!{
              |_profiler| format!(
                "{:>25} clause add", strat.name()
              ) => add red_info.clauses_added
            }
          }

          total += red_info ;
          instance.check( strat.name() ) ? ;

          // let mut dummy = String::new() ;
          // println!("") ;
          // println!( "; waiting..." ) ;
          // let _ = ::std::io::stdin().read_line(& mut dummy) ;
        }
      }
    }

    Ok(total)
  }
}




/// Given a predicate application, returns the constraints on the input and a
/// map from the variables used in the arguments to the variables of the
/// predicate.
///
/// # TODO
///
/// - more doc with examples
/// - try to reverse term before giving up and returning none
pub fn terms_of_app<F: Fn(Term) -> Term>(
  instance: & Instance, pred: PrdIdx, args: & VarMap<Term>, f: F
) -> Res<
  Option<(HConSet<RTerm>, VarHMap<Term>, VarSet)>
> {
  let mut map = VarHMap::with_capacity( instance[pred].sig.len() ) ;
  let mut app_vars = VarSet::with_capacity( instance[pred].sig.len() ) ;
  let mut terms = HConSet::with_capacity( 7 ) ;

  let mut postponed = Vec::with_capacity( args.len() ) ;

  for (index, arg) in args.index_iter() {
    if let Some(var) = arg.var_idx() {
      let _ = app_vars.insert(var) ;
      if let Some(pre) = map.insert(var, term::var(index)) {
        terms.insert(
          f( term::eq( term::var(index), pre ) )
        ) ;
      }
    } else if let Some(b) = arg.bool() {
      let var = term::var(index) ;
      terms.insert(
        f( if b { var } else { term::not(var) } )
      ) ;
    } else if let Some(i) = arg.int() {
      terms.insert(
        f( term::eq( term::var(index), term::int(i) ) )
      ) ;
    } else {
      postponed.push( (* index, arg) )
    }
  }

  for (var, arg) in postponed {
    if let Some( (term, _) ) = arg.subst_total(& map) {
      terms.insert(
        f( term::eq(term::var(var), term) )
      ) ;
    } else {
      // This is where we give up, but we could try to reverse the term.
      return Ok(None)
    }
  }

  Ok( Some( (terms, map, app_vars) ) )
}




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
impl<'a, Terms> ::rsmt2::Expr2Smt<()> for NegImplWrap<'a, Terms>
where Terms: Iterator<Item = & 'a Term> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> {
    let mut lhs = self.lhs.borrow_mut() ;
    let msg = "writing negated implication" ;
    smtry_io!(msg => write!(w, "(not ")) ;
    if let Some(term) = lhs.next() {
      smtry_io!( msg => write!(w, "(=> (and") ) ;
      smtry_io!( msg => write!(w, " ") ) ;
      smtry_io!( msg => term.write(w, |w, var| var.default_write(w)) ) ;
      while let Some(term) = lhs.next() {
        smtry_io!( msg => write!(w, " ") ) ;
        smtry_io!( msg => term.write(w, |w, var| var.default_write(w)) )
      }
      smtry_io!( msg => write!(w, ") ") ) ;
      smtry_io!( msg => self.rhs.write(w, |w, var| var.default_write(w)) ) ;
      smtry_io!( msg => write!(w, ")") )
    } else {
      smtry_io!( msg => self.rhs.write(w, |w, var| var.default_write(w)) )
    }
    smtry_io!( msg => write!(w, ")") ) ;
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
impl<'a, Terms> ::rsmt2::Expr2Smt<()> for NegConj<Terms>
where Terms: Iterator<Item = & 'a Term> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> {
    let mut terms = self.terms.borrow_mut() ;
    let msg = "writing negated implication" ;
    smtry_io!(msg => write!(w, "(not ")) ;
    if let Some(term) = terms.next() {
      smtry_io!( msg => write!(w, "(and") ) ;
      smtry_io!( msg => write!(w, " ") ) ;
      smtry_io!( msg => term.write(w, |w, var| var.default_write(w)) ) ;
      while let Some(term) = terms.next() {
        smtry_io!( msg => write!(w, " ") ) ;
        smtry_io!( msg => term.write(w, |w, var| var.default_write(w)) )
      }
      smtry_io!( msg => write!(w, ")") )
    } else {
      smtry_io!( msg => write!(w, "false") )
    }
    smtry_io!( msg => write!(w, ")") ) ;
    Ok(())
  }
}


/// Result of extracting the terms for a predicate application in a clause.
#[derive(Clone, PartialEq, Eq)]
#[allow(dead_code)]
pub enum ExtractRes {
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
  Success(Vec<TTerm>),
}
impl ExtractRes {
  /// True if failed.
  pub fn is_failed(& self) -> bool{ * self == ExtractRes::Failed }
}



/// Wraps a solver to provide helper functions.
pub struct SolverWrapper<S> {
  /// The solver.
  solver: S,
}
impl<'kid, S: Solver<'kid, Parser>> SolverWrapper<S> {

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
        self.solver.declare_const(& var.idx, & var.typ, & ()) ?
      }
    }
    self.solver.assert( & NegConj::new(terms), & () ) ? ;
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
        self.solver.declare_const(& var.idx, & var.typ, & ()) ?
      }
    }
    self.solver.assert( & NegImplWrap::new(lhs, rhs), & () ) ? ;
    let sat = self.solver.check_sat() ? ;
    self.solver.pop(1) ? ;
    Ok(! sat)
  }


  /// Returns the weakest term such that `(p args) /\ lhs => rhs`.
  ///
  /// # TODO
  ///
  /// - this can fail for `(p v (- v))` although it shouldn't, same for
  ///   `...rhs_app`
  pub fn terms_of_lhs_app(
    & mut self, instance: & Instance,
    lhs: & HConSet<RTerm>, rhs: & TTerm,
    pred: PrdIdx, args: & VarMap<Term>,
    var_info: & VarMap<VarInfo>
  ) -> Res<ExtractRes> {
    log_debug!{ "    terms_of_lhs_app on {} {}", instance[pred], args }

    // Implication trivial?
    if rhs.bool() == Some(true)
    || self.trivial_impl(var_info, lhs.iter(), & term::fls()) ? {
      log_debug!{ "      implication is trivial" }
      return Ok( ExtractRes::Trivial )
    }


    let (mut terms, map, app_vars) = if let Some(res) = terms_of_app(
      instance, pred, args, |term| term::not(term)
    ) ? {
      res
    } else {
      return Ok(ExtractRes::Failed)
    } ;

    if_not_bench!{
      log_debug!{ "      terms:" }
      for term in & terms { log_debug!{ "      - {}", term } }
      log_debug!{ "      map:" }
      for (var, trm) in & map { log_debug!{ "      - v_{} -> {}", var, trm } }
    }

    let lhs_true = lhs.is_empty() || self.trivial_conj(
      var_info, lhs.iter()
    ) ? ;

    if let Some(term) = rhs.term() {
      terms.insert( term.clone() ) ;
    } else if lhs_true && terms.is_empty() {
      if let Ok(rhs) = rhs.subst_total(& map) {
        return Ok( ExtractRes::Success( vec![rhs] ) )
      } else {
        return Ok( ExtractRes::Failed )
      }
    } else {
      return Ok( ExtractRes::Failed )
    }

    if ! lhs_true {
      for term in lhs {
        if let Some(b) = term.bool() {
          // if `b` was false then `trivial_impl` above would have seen it
          debug_assert!(b) ;
          continue
        }
        let vars = term.vars() ;
        if vars.is_subset( & app_vars ) {
          let (term, _) = term.subst_total(& map).ok_or::<Error>(
            "failure during total substitution".into()
          ) ? ;
          terms.insert( term::not(term) ) ;
        } else if vars.is_disjoint(& app_vars) {
        } else {
          return Ok(ExtractRes::Failed)
        }
      }
    }

    if terms.is_empty() {
      Ok( ExtractRes::SuccessTrue )
    } else {
      let res = term::or( terms.into_iter().collect() ) ;
      if res.bool() == Some(false) {
        Ok( ExtractRes::SuccessFalse )
      } else {
        Ok(
          ExtractRes::Success(
            vec![ TTerm::T(res) ]
          )
        )
      }
    }

  }


  /// Returns the strongest term such that `/\ lhs => (pred args)`.
  ///
  /// # TODO
  ///
  /// - move things allocated here to the struct above
  pub fn terms_of_rhs_app(
    & mut self, instance: & Instance,
    lhs_terms: & HConSet<RTerm>, lhs_preds: & PredApps,
    pred: PrdIdx, args: & VarMap<Term>,
    var_info: & VarMap<VarInfo>
  ) -> Res<ExtractRes> {
    log_debug!{ "    terms_of_rhs_app on {} {}", instance[pred], args }

    // Implication trivial?
    if self.trivial_impl(var_info, lhs_terms.iter(), & term::fls()) ? {
      log_debug!{ "      implication is trivial" }
      return Ok( ExtractRes::Trivial )
    }

    let (terms, map, app_vars) = if let Some(res) = terms_of_app(
      instance, pred, args, |term| term
    ) ? { res } else {
      return Ok(ExtractRes::Failed)
    } ;

    if_not_bench!{
      log_debug!{ "      terms:" }
      for term in & terms { log_debug!{ "      - {}", term } }
      log_debug!{ "      map:" }
      for (var, trm) in & map { log_debug!{ "      - v_{} -> {}", var, trm } }
    }

    let mut tterms: Vec<_> = terms.into_iter().map(|t| TTerm::T(t)).collect() ;

    for term in lhs_terms {
      if let Some(b) = term.bool() {
        // if `b` was false then `trivial_impl` above would have caught it
        debug_assert!(b) ;
        continue
      }
      let vars = term.vars() ;
      if vars.is_subset( & app_vars ) {
        let (term, _) = term.subst_total(& map).ok_or::<Error>(
          "failure during total substitution".into()
        ) ? ;
        tterms.push( TTerm::T(term) )
      } else if vars.is_disjoint(& app_vars) {
        // Does not constrain the arguments, as long as we don't enter (later)
        // the next branch of this `if`. In which case we fail.
        ()
      } else {
        return Ok(ExtractRes::Failed)
      }
    }

    for (pred, argss) in lhs_preds {
      for args in argss {
        let mut nu_args = VarMap::with_capacity( args.len() ) ;
        for arg in args {
          if let Some( (nu_arg, _) ) = arg.subst_total(& map) {
            // Total substitution succeeded, all variables are known.
            nu_args.push(nu_arg)
          } else {
            // For all we know, `pred` is false and there's no constraint on
            // the predicate we're resolving. Even if the variables are
            // completely disjoint.
            return Ok(ExtractRes::Failed)
          }
        }
        tterms.push( TTerm::P { pred: * pred, args: nu_args } )
      }
    }

    if tterms.is_empty() {
      Ok(ExtractRes::SuccessTrue)
    } else {
      Ok(
        ExtractRes::Success( tterms.into_iter().collect() )
      )
    }
  }
}





/// Has a name.
pub trait HasName {
  /// Name of the strategy.
  fn name(& self) -> & 'static str ;
}

/// Reduction strategy trait.
///
/// Function `apply` will be applied until fixed point (`false` is returned).
pub trait RedStrat: HasName {
  /// Applies the reduction strategy. Returns the number of predicates reduced
  /// and the number of clauses forgotten.
  fn apply(& mut self, & mut Instance) -> Res<RedInfo> ;
}


/// Forces to false predicates appearing only in the lhs of the clauses.
pub struct Trivial {}
impl HasName for Trivial {
  fn name(& self) -> & 'static str { "trivial" }
}
impl RedStrat for Trivial {

  fn apply(& mut self, instance: & mut Instance) -> Res<RedInfo> {

    let (mut fls_preds, mut tru_preds) = (vec![], vec![]) ;
    for pred in instance.pred_indices() {
      if instance.forced_terms_of(pred).is_some() { continue }
      if instance.clauses_of_pred(pred).1.is_empty() {
        fls_preds.push(pred)
      } else if instance.clauses_of_pred(pred).0.is_empty() {
        tru_preds.push(pred)
      }
    }

    let pred_cnt = fls_preds.len() + tru_preds.len() ;
    let mut clse_cnt = instance.force_false(fls_preds) ? ;
    clse_cnt += instance.force_true(tru_preds) ? ;

    Ok( (pred_cnt, clse_cnt, 0).into() )
  }
}


// /// Simplifies clauses of the form `true => p(v_1, ..., v_n)` where all the
// /// `v_i`s are different. Unfolds `p` to `true`.
// ///
// /// # TODO
// ///
// /// - handle `true => (x >= x)` correctly
// pub struct ForcedImplies {
//   /// Predicates found to be equivalent to true, but not propagated yet.
//   true_preds: PrdSet,
//   /// Predicates found to be equivalent to false, but not propagated yet.
//   false_preds: PrdSet,
//   /// Predicates to propagate.
//   preds: PrdHMap< Vec<TTerm> >,
// }
// impl ForcedImplies {
//   /// Constructor.
//   fn new() -> Self {
//     ForcedImplies {
//       true_preds: PrdSet::with_capacity(7),
//       false_preds: PrdSet::with_capacity(7),
//       preds: PrdHMap::with_capacity(7),
//     }
//   }
// }
// impl RedStrat for ForcedImplies {
//   fn name(& self) -> & 'static str { "true => ..." }
//   fn apply(& mut self, instance: & mut Instance) -> Res<RedInfo> {
//     let mut clauses_rmed = 0 ;

//     let mut clause_idx: ClsIdx = 0.into() ;
//     'iter_clauses: while clause_idx < instance.clauses.len() {

//       if instance[clause_idx].lhs.is_empty() {
//         let clause = instance.forget_clause(clause_idx) ? ;
//         clauses_rmed += 1 ;
//         match clause.rhs {
//           TTerm::P { pred, args } => match terms_of_rhs_app(
//             instance, None, pred, args
//           ) ? {
//             Some( Either::Rgt(true) ) => (),
//             Some( Either::Rgt(false) ) => bail!( ErrorKind::Unsat ),
            
//             Some( Either::Lft(tterms) ) => {
//               if self.true_preds.contains(& pred) {
//                 ()
//               } else if self.false_preds.contains(& pred) {
//                 bail!( ErrorKind::Unsat )
//               } else {
//                 let mut args = VarMap::with_capacity(
//                   instance[pred].sig.len()
//                 ) ;
//                 for (idx, typ) in instance[pred].sig.index_iter() {
//                   args.push(
//                     VarInfo {
//                       name: format!("v{}", idx),
//                       typ: * typ, idx
//                     }
//                   )
//                 }
//                 for tterm in & tterms {
//                   instance.push_clause(
//                     Clause::new( args.clone(), vec![], tterm.clone() )
//                   )
//                 }
//                 let prev = self.preds.insert(pred, tterms) ;
//                 if prev.is_some() { unimplemented!() }
//               }
//             },

//             None => unimplemented!(),
//           },
//           TTerm::T(term) => match term.bool() {
//             Some(true) => (),
//             _ => bail!( ErrorKind::Unsat ),
//           },
//         }
//         continue 'iter_clauses
//       } else {
//         match instance[clause_idx].rhs.bool() {
//           Some(true) => {
//             let _ = instance.forget_clause(clause_idx) ? ;
//             clauses_rmed += 1 ;
//             continue 'iter_clauses
//           },

//           Some(false) => {
//             if instance[clause_idx].lhs.len() == 1 {
//               let clause = instance.forget_clause(clause_idx) ? ;
//               match clause.lhs.into_iter().next().unwrap() {
//                 TTerm::P { pred, args } => match terms_of_rhs_app(
//                   instance, None, pred, & args.into_index_iter().collect()
//                 ) ? {
//                   Some( Either::Rgt(true) ) => bail!( ErrorKind::Unsat ),
//                   Some( Either::Rgt(false) ) => (),

//                   Some( Either::Lft( (tterms, map) ) ) => {
//                     if self.true_preds.contains(& pred) {
//                       bail!( ErrorKind::Unsat )
//                     } else if self.false_preds.contains(& pred) {
//                       ()
//                     } else {
//                       let term = term::app(
//                         Op::Not, vec![
//                           term::app(
//                             Op::And, tterms.into_iter().map(
//                               |tterm| if let TTerm::T(term) = tterm {
//                                 term
//                               } else {
//                                 unreachable!()
//                               }
//                             ).collect()
//                           )
//                         ]
//                       ) ;
//                       let tterms = vec![ TTerm::T(term) ] ;
//                       let prev = self.preds.insert(pred, (tterms, map)) ;
//                       if prev.is_some() { unimplemented!() }
//                     }
//                   },
                  
//                   // Should not be possible with an empty lhs.
//                   None => unimplemented!(),
//                 },
//               }
//               continue 'iter_clauses
//             }
//           },

//           None => (),
//         }
//       }

//       clause_idx.inc()

//     }

//     let pred_count =
//       self.true_preds.len() + self.false_preds.len() + self.preds.len() ;

//     clauses_rmed += instance.force_true(self.true_preds.drain()) ? ;
//     clauses_rmed += instance.force_false(self.false_preds.drain()) ? ;
//     clauses_rmed += force_pred(instance, self.preds.drain()) ? ;

//     Ok( (pred_count, clauses_rmed) )
//   }
// }




/// Reduction strategy trait for strategies requiring a solver.
///
/// Function `apply` will be applied until fixed point (`false` is returned).
pub trait SolverRedStrat< 'kid, Slver: Solver<'kid, Parser> >: HasName {
  /// Applies the reduction strategy. Returns the number of predicates
  /// eliminated, the number of clauses forgotten, and the number of clauses
  /// created.
  fn apply(
    & mut self, & mut Instance, & mut SolverWrapper<Slver>
  ) -> Res<RedInfo> ;
}






/// Works on predicates that appear in only one rhs.
///
/// # Restrictions
///
/// Unfolds a predicate `P` iff
///
/// - it appears in exactly one clause rhs, say in clause `C`
/// - `P` does not appear in the lhs of `C`
/// - the lhs of `C` has no top term relating the variables `vars` appearing in
///   the application of `P` and the other variables `other_vars` of the clause
/// - the predicate applications in the lhs of `C` do not mention `other_vars`
///
/// | This reduction does not run on:        |                           |
/// |:---------------------------------------|:--------------------------|
/// | `(p ...)    and ... => (p ...)`        | `p` appears in lhs        |
/// | `(v'' > v)  and ... => (p v (v' + 1))` | `v''` and `v` are related |
/// | `(p' v'' v) and ... => (p v (v' + 1))` | `p'` mentions `v''`       |
///
/// | But it runs on:                    | `p v_0 v_1 =`               |
/// |:-----------------------------------|:----------------------------|
/// | `(v > v'  + 2)        => (p v v')` | `(v_0 > v_1 + 2)`           |
/// | `(v > 0)              => (p 7 v )` | `(v_0 = 7) and (v_1 > 0)`   |
/// | `(v > 0)              => (p 7 v')` | `(v_0 = 7)`                 |
/// | `(v > 0)              => (p v v )` | `(v_0 = v_1) and (v_0 > 0)` |
/// | `(v > 0) and (v <= 0) => (p 7 v')` | `false` (by check-sat)      |
pub struct SimpleOneRhs {
  /// Predicates found to be equivalent to true, but not propagated yet.
  true_preds: PrdSet,
  /// Predicates found to be equivalent to false, but not propagated yet.
  false_preds: PrdSet,
  /// Predicates to propagate.
  preds: PrdHMap< Vec<TTerm> >,
}
impl SimpleOneRhs {
  /// Constructor.
  fn new() -> Self {
    SimpleOneRhs {
      true_preds: PrdSet::with_capacity(7),
      false_preds: PrdSet::with_capacity(7),
      preds: PrdHMap::with_capacity(7),
    }
  }
}
impl HasName for SimpleOneRhs {
  fn name(& self) -> & 'static str { "simple one rhs" }
}
impl<'kid, Slver> SolverRedStrat<'kid, Slver> for SimpleOneRhs
where Slver: Solver<'kid, Parser> {
  fn apply(
    & mut self, instance: & mut Instance, solver: & mut SolverWrapper<Slver>
  ) -> Res<RedInfo> {
    debug_assert!( self.true_preds.is_empty() ) ;
    debug_assert!( self.false_preds.is_empty() ) ;
    debug_assert!( self.preds.is_empty() ) ;
    let mut clauses_rmed = 0 ;
    let mut pred_count = 0 ;

    for pred in instance.pred_indices() {
      log_debug!{ "looking at {}", instance[pred] }
      if instance.clauses_of_pred(pred).1.len() == 1 {
        let clause =
          * instance.clauses_of_pred(pred).1.iter().next().unwrap() ;
        log_debug!{
          "trying to unfold {}", instance[pred]
        }

        let res = if let TTerm::P {
          pred: _this_pred, ref args
        } = * instance[clause].rhs() {
          debug_assert_eq!( pred, _this_pred ) ;
          solver.terms_of_rhs_app(
            instance,
            instance[clause].lhs_terms(), instance[clause].lhs_preds(),
            pred, args, instance[clause].vars()
          ) ?
        } else {
          bail!("inconsistent instance state")
        } ;

        if res.is_failed() { continue }
        
        log_debug!{
          "from {}",
          instance.clauses()[clause].to_string_info( instance.preds() ) ?
        }

        instance.forget_clause(clause) ? ;
        clauses_rmed += 1 ;

        log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
        use self::ExtractRes::* ;
        match res {
          Trivial => {
            log_info!("  => false") ;
            clauses_rmed += instance.force_false(Some(pred)) ?
          },
          SuccessTrue => {
            log_info!("  => true") ;
            clauses_rmed += instance.force_true(Some(pred)) ? ;
          },
          Success(tterms) => {
            if_not_bench!{
              for tterm in & tterms {
                log_info!("  => {}", tterm ) ;
                if let Some(pred) = tterm.pred() {
                  log_info!("     {}", instance[pred])
                }
              }
            }
            clauses_rmed += instance.force_preds(
              Some((pred, TTerms::conj(tterms)))
            ) ? ;

            instance.check("after unfolding") ?
          },
          // Failed is caught before this match, and false is not possible for
          // the function generating `res`.
          Failed | SuccessFalse => unreachable!(),
        }

        if instance.forced_terms_of(pred).is_some() {
          pred_count += 1
        }
      }
    }

    if pred_count > 1 {
      instance.simplify_clauses() ?
    }

    Ok( (pred_count, clauses_rmed, 0).into() )
  }
}








pub struct SimpleOneLhs {
  /// Predicates found to be equivalent to true, but not propagated yet.
  true_preds: PrdSet,
  /// Predicates found to be equivalent to false, but not propagated yet.
  false_preds: PrdSet,
  /// Predicates to propagate.
  preds: PrdHMap< Vec<TTerm> >,
}
impl SimpleOneLhs {
  /// Constructor.
  pub fn new() -> Self {
    SimpleOneLhs {
      true_preds: PrdSet::with_capacity(7),
      false_preds: PrdSet::with_capacity(7),
      preds: PrdHMap::with_capacity(7),
    }
  }
}
impl HasName for SimpleOneLhs {
  fn name(& self) -> & 'static str { "simple one lhs" }
}
impl<'kid, Slver> SolverRedStrat<'kid, Slver> for SimpleOneLhs
where Slver: Solver<'kid, Parser> {
  fn apply(
    & mut self, instance: & mut Instance, solver: & mut SolverWrapper<Slver>
  ) -> Res<RedInfo> {
    debug_assert!( self.true_preds.is_empty() ) ;
    debug_assert!( self.false_preds.is_empty() ) ;
    debug_assert!( self.preds.is_empty() ) ;
    let mut clauses_rmed = 0 ;
    let mut pred_count = 0 ;

    for pred in instance.pred_indices() {
      let clause_idx = if instance.clauses_of_pred(pred).0.len() == 1 {
        * instance.clauses_of_pred(pred).0.iter().next().unwrap()
      } else {
        continue
      } ;

      log_debug!{
        "trying to unfold {}", instance[pred]
      }

      let res = {
        if instance.preds_of_clause(clause_idx).1 == Some(pred) {
          ExtractRes::SuccessTrue
        } else if instance.preds_of_clause(clause_idx).0.len() > 1 {
          continue
        } else {
          let clause = & instance[clause_idx] ;
          // log_debug!{
          //   "from {}", clause.to_string_info( instance.preds() ) ?
          // }
          let args = if let Some(argss) = clause.lhs_preds().get(& pred) {
            if argss.len() != 1 { continue }
            let mut iter = argss.iter() ;
            let res = iter.next().unwrap() ;
            debug_assert!( iter.next().is_none() ) ;
            res
          } else {
            bail!("inconsistent instance state")
          } ;

          solver.terms_of_lhs_app(
            instance, clause.lhs_terms(), clause.rhs(), pred, args,
            clause.vars()
          ) ?
        }
      } ;

      if res.is_failed() { continue }

      log_debug!{
        "from {}",
        instance.clauses()[clause_idx].to_string_info( instance.preds() ) ?
      }

      instance.forget_clause(clause_idx) ? ;
      clauses_rmed += 1 ;

      log_debug!{ "  unfolding {}", conf.emph(& instance[pred].name) }
      use self::ExtractRes::* ;
      match res {
        SuccessTrue => {
          log_debug!("  => true") ;
          clauses_rmed += instance.force_true(Some(pred)) ? ;
        },
        SuccessFalse => {
          log_debug!("  => false") ;
          clauses_rmed += instance.force_false(Some(pred)) ? ;
        },
        Success(tterms) => {
          if_not_bench!{
            for tterm in & tterms {
              log_debug!("  => {}", tterm ) ;
              if let Some(pred) = tterm.pred() {
                log_debug!("     {}", instance[pred])
              }
            }
            log_debug!( "  {:?}", instance.clauses_of_pred(pred) )
          }
          clauses_rmed += instance.force_preds(
            Some((pred, TTerms::conj(tterms)))
          ) ? ;

          instance.check("after unfolding") ?
        },
        // Failed is caught before this match, and the rest is not possible for
        // the function generating `res`.
        _ => unreachable!(),
      }

      if instance.forced_terms_of(pred).is_some() {
        pred_count += 1
      } else {
        if_verb!{
          log_info!{ "  did not remove, still appears in lhs of" }
          for clause in instance.clauses_of_pred(pred).0 {
            log_info!{ "  {}", instance.clauses()[* clause].to_string_info( instance.preds() ) ? }
          }
          log_info!{ "  and rhs of" }
          for clause in instance.clauses_of_pred(pred).1 {
            log_info!{ "  {}", instance.clauses()[* clause].to_string_info( instance.preds() ) ? }
          }
        }
      }
      let mut dummy = String::new() ;
      println!("") ;
      println!( "; {}...", conf.emph("press return") ) ;
      let _ = ::std::io::stdin().read_line(& mut dummy) ;
    }

    if pred_count > 1 {
      instance.simplify_clauses() ?
    }

    Ok( (pred_count, clauses_rmed, 0).into() )
  }
}










/// Mono pred clause strengthening.
pub struct MonoPredClause {
  /// Predicates found to be equivalent to true, but not propagated yet.
  true_preds: PrdSet,
  /// Clauses to remove.
  clauses_to_rm: Vec<ClsIdx>,
  /// Remembers predicate that where already strengthened.
  known: PrdSet,
}
impl MonoPredClause {
  /// Constructor.
  pub fn new() -> Self {
    MonoPredClause {
      true_preds: PrdSet::with_capacity(7),
      clauses_to_rm: Vec::with_capacity(7),
      known: PrdSet::with_capacity(29),
      // preds: PrdHMap::with_capacity(7),
    }
  }
}
impl HasName for MonoPredClause {
  fn name(& self) -> & 'static str { "mono pred clause" }
}
impl<'kid, Slver> SolverRedStrat<'kid, Slver> for MonoPredClause
where Slver: Solver<'kid, Parser> {
  fn apply(
    & mut self, instance: & mut Instance, solver: & mut SolverWrapper<Slver>
  ) -> Res<RedInfo> {
    let mut nu_clause_count = 0 ;
    let mut known = PrdSet::with_capacity( instance.preds().len() ) ;
    // let mut strength = PrdHMap::with_capacity( instance.preds().len() ) ;

    'clause_iter: for clause in instance.clause_indices() {
      log_debug!{ "looking at clause #{}", clause }
      let (lhs_pred_apps_len, rhs_is_pred_app) = (
        instance[clause].lhs_pred_apps_len(),
        instance[clause].rhs().pred().is_some()
      ) ;

      if lhs_pred_apps_len == 0 && rhs_is_pred_app {
        let (pred, res) = if let TTerm::P {
          pred, ref args
        } = * instance.clauses()[clause].rhs() {
          (
            pred, solver.terms_of_rhs_app(
              instance,
              instance.clauses()[clause].lhs_terms(),
              instance.clauses()[clause].lhs_preds(), pred, args,
              instance.clauses()[clause].vars()
            ) ?
          )
        } else {
          bail!("inconsistent instance state")
        } ;

        if self.known.contains(& pred) { continue 'clause_iter }

        log_debug!{ "  rhs only ({})", instance[pred] }

        match res {
          ExtractRes::Failed => {
            log_debug!{ "  failed..." }
            continue
          },
          ExtractRes::Success(tterms) => {
            if_not_bench!{
              log_debug!{ "  success" }
              for tterm in & tterms {
                log_debug!{ "  - {}", tterm }
              }
              log_debug!{
                "  strengthening ({})...",
                instance.clauses_of_pred(pred).0.len()
              }
            }
            known.insert(pred) ;
            // strength.entry(pred).insert_or_with(
            //   || Vec::with_capacity(10)
            // ).push(tterms)
            nu_clause_count += instance.strengthen_in_lhs(pred, tterms) ?
          }
          ExtractRes::Trivial => {
            log_debug!{ "  clause is trivial..." }
            self.clauses_to_rm.push(clause)
          },
          ExtractRes::SuccessTrue => {
            log_debug!{ "  forcing {} to true", instance[pred] }
            self.true_preds.insert(pred) ;
            self.clauses_to_rm.push(clause)
          },
          // `terms_of_rhs_app` cannot return false.
          ExtractRes::SuccessFalse => unreachable!(),
        }

      } else if lhs_pred_apps_len == 1 && ! rhs_is_pred_app {
        log_debug!{ "  lhs only" }


      }
    }

    use std::iter::Extend ;
    self.known.extend( known ) ;

    let mut clauses = self.clauses_to_rm.len() ;
    let preds = self.true_preds.len() ;
    instance.forget_clauses( self.clauses_to_rm.drain(0..).collect() ) ? ;
    clauses += instance.force_true( self.true_preds.drain() ) ? ;

    Ok( (preds, clauses, nu_clause_count).into() )
  }
}






/// Removes clauses that are trivially true by smt.
pub struct SmtTrivial {}
impl SmtTrivial {
  /// Constructor.
  pub fn new() -> Self {
    SmtTrivial {
      // true_preds: PrdSet::with_capacity(7),
      // false_preds: PrdSet::with_capacity(7),
      // preds: PrdHMap::with_capacity(7),
    }
  }
}
impl HasName for SmtTrivial {
  fn name(& self) -> & 'static str { "smt trivial" }
}
impl<'kid, Slver> SolverRedStrat<'kid, Slver> for SmtTrivial
where Slver: Solver<'kid, Parser> {
  fn apply(
    & mut self, instance: & mut Instance, solver: & mut SolverWrapper<Slver>
  ) -> Res<RedInfo> {
    let mut clauses_to_rm = Vec::with_capacity(10) ;

    { // Push a scope so that `lhs` is dropped because it borrows `instance`.
      // Remove when non-lexical lifetimes are implemented.
      let mut lhs = Vec::with_capacity(10) ;
      let fls = term::fls() ;

      'clause_iter: for (
        clause_idx, clause
      ) in instance.clauses().index_iter() {
        lhs.clear() ;

        for term in clause.lhs_terms() {
          lhs.push(term)
        }

        let rhs = if let Some(term) = clause.rhs().term() {
          term
        } else {
          if lhs.is_empty() {
            continue 'clause_iter
          }
          & fls
        } ;

        if solver.trivial_impl(clause.vars(), lhs.drain(0..), rhs) ? {
          clauses_to_rm.push(clause_idx)
        }
      }
    }

    let clause_cnt = clauses_to_rm.len() ;
    instance.forget_clauses(clauses_to_rm) ? ;
    if clause_cnt > 0 {
      log_info!{ "  dropped {} trivial clause(s)", clause_cnt }
    }
    Ok( (0, clause_cnt, 0).into() )
  }
}







#[doc = r#"Unit type parsing the output of the SMT solver.

Does not parse anything.
"#]
pub struct Parser ;
impl ::rsmt2::ParseSmt2 for Parser {
  type Ident = () ;
  type Value = () ;
  type Expr = () ;
  type Proof = () ;
  type I = () ;

  fn parse_ident<'a>(
    & self, _: & 'a [u8]
  ) -> ::nom::IResult<& 'a [u8], ()> {
    panic!(
      "`parse_ident` of the reduction solver parser should never be called"
    )
  }

  fn parse_value<'a>(
    & self, _: & 'a [u8]
  ) -> ::nom::IResult<& 'a [u8], ()> {
    panic!(
      "`parse_value` of the reduction solver parser should never be called"
    )
  }

  fn parse_expr<'a>(
    & self, _: & 'a [u8], _: & ()
  ) -> ::nom::IResult<& 'a [u8], ()> {
    panic!(
      "`parse_expr` of the reduction solver parser should never be called"
    )
  }

  fn parse_proof<'a>(
    & self, _: & 'a [u8]
  ) -> ::nom::IResult<& 'a [u8], ()> {
    panic!(
      "`parse_proof` of the reduction solver parser should never be called"
    )
  }
}


