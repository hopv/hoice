#![doc = r#"Reduction strategies.

The strategies are attached `struct`s so that they can be put in a
vector using single dispatch. That way, they can be combined however we want.
"#]

use common::* ;
use instance::* ;


/// Runs pre-processing
pub fn work(
  instance: & mut Instance, profiler: & Profiler
) -> Res<()> {

  profile!{ |profiler| tick "pre-proc" }
  log_info!{ "starting pre-processing" }

  let res = if conf.preproc.smt_red {
    let mut kid = ::rsmt2::Kid::new( conf.solver.conf() ).chain_err(
      || ErrorKind::Z3SpawnError
    ) ? ;
    let solver = ::rsmt2::solver(& mut kid, ()).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    if let Some(log) = conf.solver.log_file("preproc") ? {
      run(
        instance, profiler, Some( SolverWrapper::new(solver.tee(log)) )
      )
    } else {
      run( instance, profiler, Some( SolverWrapper::new(solver) ) )
    }
  } else {
    run(
      instance, profiler,
      None as Option< SolverWrapper<::rsmt2::PlainSolver<()>> >
    )
  } ;
  profile!{ |profiler| mark "pre-proc" } ;
  log_info!{
    "\n\ndone with pre-processing:\n{}\n\n", instance.to_string_info(()) ?
  }
  match res {
    Err(ref e) if e.is_unsat() => {
      instance.set_unsat() ;
      Ok(())
    },
    res => res
  }

}

pub fn run<'kid, S: Solver<'kid, ()>>(
  instance: & mut Instance,
  profiler: & Profiler, solver: Option< SolverWrapper<S> >
) -> Res<()> {
  let mut reductor = Reductor::new(solver) ;
  let mut total: RedInfo = (0, 0, 0).into() ;

  // log_info!{ "running simplification" }
  // instance.check("before simplification") ? ;
  // profile!{ |profiler| tick "pre-proc", "propagate" }
  // let clauses = instance.simplify_clauses() ? ;
  // total.clauses_rmed += clauses ;
  // profile!{ |profiler| mark "pre-proc", "propagate" }
  // profile!{
  //   |profiler| format!(
  //     "{:>25} clause red", "propagate"
  //   ) => add clauses
  // }



  profile!{ |profiler| tick "pre-proc", "propagate" }
  let clauses = instance.simplify_clauses() ? ;
  total.clauses_rmed += clauses ;
  profile!{ |profiler| mark "pre-proc", "propagate" }
  profile!{
    |profiler| format!(
      "{:>25} clause red", "propagate"
    ) => add clauses
  }

  log_debug!{
    "|===| after propagation:\n{}\n\n", instance.to_string_info(()) ?
  }


  let mut changed = true ;
  'preproc: while changed {

    profile!{ |profiler| tick "pre-proc", "simplifying" }
    let red_info = reductor.run_simplification(instance, & profiler) ? ;
    total += red_info ;
    profile!{ |profiler| mark "pre-proc", "simplifying" }

    log_debug!{
      "|===| after simplification:\n{}\n\n", instance.to_string_info(()) ?
    }

    log_info!{ "running reduction" }
    profile!{ |profiler| tick "pre-proc", "reducing" }
    let red_info = reductor.run(instance, & profiler) ? ;
    changed = red_info.non_zero() ;
    total += red_info ;
    instance.check("after reduction") ? ;
    profile!{ |profiler| mark "pre-proc", "reducing" }
    log_info!{ "done reducing" }

    // log_info!{
    //   "\n\n\n|===|instance after reduction:\n{}\n\n", instance.to_string_info(()) ?
    // }

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
pub struct Reductor<'kid, S: Solver<'kid, ()>> {
  /// Strategies.
  strats: Vec< Box<RedStrat> >,
  /// Solver strats.
  solver_strats: Option< (
    SolverWrapper<S>, Vec< Box<SolverRedStrat<'kid, S>> >
  ) >,
}
impl<'kid, S: Solver<'kid, ()>> Reductor<'kid, S> {
  /// Constructor.
  pub fn new(solver: Option< SolverWrapper<S> >) -> Self {
    let strats: Vec< Box<RedStrat> > = vec![
      Box::new( Trivial {} ),
      // Box::new( ForcedImplies::new() ),
    ] ;
    let mut solver_strats: Vec< Box<SolverRedStrat<'kid, S>> > = vec![
      Box::new( SmtTrivial::new() ),
    ] ;
    if conf.preproc.one_rhs {
      solver_strats.push( Box::new( SimpleOneRhs::new() ) )
    }
    if conf.preproc.one_lhs {
      solver_strats.push( Box::new( SimpleOneLhs::new() ) )
    }
    // if conf.preproc.one_rhs {
    //   solver_strats.push( Box::new( OneRhs::new() ) )
    // }
    // if conf.preproc.mono_pred {
    //   solver_strats.push( Box::new( MonoPredClause::new() ) )
    // }
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
      // let mut changed = true ;
      // while changed {
      //   changed = false ;

        for strat in strats.iter_mut() {
          let mut changed = true ;
          while changed {
            log_info!("applying {}", conf.emph( strat.name() )) ;
            profile!{ |_profiler| tick "pre-proc", "reducing", strat.name() }
            let red_info = strat.apply(instance, solver) ? ;
            changed = red_info.non_zero() ;


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
          }

          // let mut dummy = String::new() ;
          // println!("") ;
          // println!( "; waiting..." ) ;
          // let _ = ::std::io::stdin().read_line(& mut dummy) ;
        }
      // }
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
impl<'a, Terms> ::rsmt2::to_smt::Expr2Smt<()> for NegImplWrap<'a, Terms>
where Terms: Iterator<Item = & 'a Term> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: & ()
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
    & self, w: & mut Writer, _: & ()
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
  // /// Variable set storing new quantified variables.
  // ///
  // /// Used when aggregating the terms in a quantified term, see
  // /// [`qterms_of_rhs_app`][fun].
  // ///
  // /// [fun]: struct.SolverWrapper.html#method.qterms_of_rhs_app
  // new_vars: VarSet,
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


  /// Returns the strongest quantified term such that `/\ lhs => (pred args)`.
  ///
  /// # TODO
  ///
  /// - move things allocated here to the struct above
  pub fn qterms_of_rhs_app(
    & mut self, instance: & Instance,
    lhs_terms: & HConSet<RTerm>, lhs_preds: & PredApps,
    pred: PrdIdx, args: & VarMap<Term>,
    var_info: & VarMap<VarInfo>
  ) -> Res<ExtractRes> {
    log_debug!{ "    qterms_of_rhs_app on {} {}", instance[pred], args }

    // Implication trivial?
    if self.trivial_impl(var_info, lhs_terms.iter(), & term::fls()) ? {
      log_debug!{ "      implication is trivial" }
      return Ok( ExtractRes::Trivial )
    }

    let (terms, map, mut app_vars) = if let Some(res) = terms_of_app(
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
    let mut lhs_terms: Vec<_> = lhs_terms.iter().collect() ;
    let mut lhs_terms_buf: Vec<_> = Vec::with_capacity( lhs_terms.len() ) ;
    let mut qvars = VarHMap::with_capacity(7) ;


    let mut vars = VarSet::with_capacity(7) ;
    for (pred, argss) in lhs_preds {
      for args in argss {
        let mut nu_args = VarMap::with_capacity( args.len() ) ;
        for arg in args {
          use std::iter::Extend ;
          vars.extend( arg.vars() ) ;
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
    for var in vars {
      let is_new = app_vars.insert(var) ;
      if is_new {
        let _prev = qvars.insert(var, var_info[var].typ) ;
        debug_assert_eq!( None, _prev )
      }
    }


    let mut fixed_point = false ;

    while fixed_point {
      fixed_point = true ;

      for term in lhs_terms.drain(0..) {
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
          lhs_terms_buf.push(term)
        } else {
          fixed_point = false ;
          for var in vars {
            let is_new = app_vars.insert(var) ;
            if is_new {
              let _prev = qvars.insert( var, var_info[var].typ ) ;
              debug_assert_eq!( _prev, None )
            }
          }
        }
      }

      ::std::mem::swap( & mut lhs_terms, & mut lhs_terms_buf )
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

    instance.force_trivial()
  }
}




/// Reduction strategy trait for strategies requiring a solver.
///
/// Function `apply` will be applied until fixed point (`false` is returned).
pub trait SolverRedStrat< 'kid, Slver: Solver<'kid, ()> >: HasName {
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
  pub fn new() -> Self {
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
where Slver: Solver<'kid, ()> {
  fn apply(
    & mut self, instance: & mut Instance, solver: & mut SolverWrapper<Slver>
  ) -> Res<RedInfo> {
    debug_assert!( self.true_preds.is_empty() ) ;
    debug_assert!( self.false_preds.is_empty() ) ;
    debug_assert!( self.preds.is_empty() ) ;
    let mut red_info: RedInfo = (0,0,0).into() ;

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
        red_info.clauses_rmed += 1 ;

        log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
        use self::ExtractRes::* ;
        match res {
          Trivial => {
            log_info!("  => false") ;
            red_info += instance.force_false(Some(pred)) ?
          },
          SuccessTrue => {
            log_info!("  => true") ;
            red_info += instance.force_true(Some(pred)) ? ;
          },
          Success(tterms) => {
            if_not_bench!{
              for tterm in & tterms {
                log_debug!("  => {}", tterm ) ;
                if let Some(pred) = tterm.pred() {
                  log_debug!("     {}", instance[pred])
                }
              }
            }
            red_info += instance.force_preds(
              Some((pred, None, TTerms::conj(tterms)))
            ) ? ;


            instance.check("after unfolding") ?
          },
          // Failed is caught before this match, and false is not possible for
          // the function generating `res`.
          Failed | SuccessFalse => unreachable!(),
        }

        if instance.forced_terms_of(pred).is_some() {
          red_info.preds += 1
        } else {
          if_verb!{
            log_debug!{ "  did not remove, still appears in lhs of" }
            for clause in instance.clauses_of_pred(pred).0 {
              log_debug!{ "  {}", instance.clauses()[* clause].to_string_info( instance.preds() ) ? }
            }
            log_debug!{ "  and rhs of" }
            for clause in instance.clauses_of_pred(pred).1 {
              log_debug!{ "  {}", instance.clauses()[* clause].to_string_info( instance.preds() ) ? }
            }
          }
        }
      }
    }

    Ok( red_info )
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
where Slver: Solver<'kid, ()> {
  fn apply(
    & mut self, instance: & mut Instance, solver: & mut SolverWrapper<Slver>
  ) -> Res<RedInfo> {
    debug_assert!( self.true_preds.is_empty() ) ;
    debug_assert!( self.false_preds.is_empty() ) ;
    debug_assert!( self.preds.is_empty() ) ;
    let mut red_info: RedInfo = (0,0,0).into() ;

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
      red_info.clauses_rmed += 1 ;

      log_info!{ "  instance:\n{}", instance.to_string_info( () ) ? }

      log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
      use self::ExtractRes::* ;
      match res {
        SuccessTrue => {
          log_info!("  => true") ;
          red_info += instance.force_true(Some(pred)) ?
        },
        SuccessFalse => {
          log_info!("  => false") ;
          red_info += instance.force_false(Some(pred)) ?
        },
        Success(tterms) => {
          if_not_bench!{
            for tterm in & tterms {
              log_debug!("  => {} (t)", tterm ) ;
              if let Some(pred) = tterm.pred() {
                log_debug!("     {}", instance[pred])
              }
            }
            log_debug!( "  {:?}", instance.clauses_of_pred(pred) )
          }
          red_info += instance.force_preds(
            Some((pred, None, TTerms::conj(tterms)))
          ) ? ;

          instance.check("after unfolding") ?
        },
        // Failed is caught before this match, and the rest is not possible for
        // the function generating `res`.
        _ => unreachable!(),
      }

      if instance.forced_terms_of(pred).is_some() {
        red_info.preds += 1
      } else {
        if_verb!{
          log_debug!{ "  did not remove, still appears in lhs of" }
          for clause in instance.clauses_of_pred(pred).0 {
            log_debug!{ "  {}", instance.clauses()[* clause].to_string_info( instance.preds() ) ? }
          }
          log_debug!{ "  and rhs of" }
          for clause in instance.clauses_of_pred(pred).1 {
            log_debug!{ "  {}", instance.clauses()[* clause].to_string_info( instance.preds() ) ? }
          }
        }
      }
      // let mut dummy = String::new() ;
      // println!("") ;
      // println!( "; {}...", conf.emph("press return") ) ;
      // let _ = ::std::io::stdin().read_line(& mut dummy) ;
    }

    Ok( red_info )
  }
}






/// Works on predicates that appear in only one rhs.
///
/// Only works on predicates that need qualifiers to be reduced, it's the
/// dual of `SimpleOneRhs` in a way.
pub struct OneRhs {
  /// Stores new variables discovered as we iterate over the lhs of clauses.
  new_vars: VarSet,
}
impl OneRhs {
  /// Constructor.
  pub fn new() -> Self {
    OneRhs {
      new_vars: VarSet::with_capacity(17)
    }
  }
}
impl HasName for OneRhs {
  fn name(& self) -> & 'static str { "simple one rhs" }
}
impl<'kid, Slver> SolverRedStrat<'kid, Slver> for OneRhs
where Slver: Solver<'kid, ()> {
  fn apply(
    & mut self, instance: & mut Instance, solver: & mut SolverWrapper<Slver>
  ) -> Res<RedInfo> {
    debug_assert!( self.new_vars.is_empty() ) ;
    let mut red_info: RedInfo = (0,0,0).into() ;

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

        if res.is_failed() {
          log_debug!{ "  skipping" }
          continue
        }
        
        // log_debug!{
        //   "from {}",
        //   instance.clauses()[clause].to_string_info( instance.preds() ) ?
        // }

        instance.forget_clause(clause) ? ;
        red_info.clauses_rmed += 1 ;

        log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
        use self::ExtractRes::* ;
        match res {
          Trivial => {
            log_info!("  => false") ;
            red_info += instance.force_false(Some(pred)) ?
          },
          SuccessTrue => {
            log_info!("  => true") ;
            red_info += instance.force_true(Some(pred)) ? ;
          },
          Success(tterms) => {
            if_not_bench!{
              for tterm in & tterms {
                log_debug!("  => {}", tterm ) ;
                if let Some(pred) = tterm.pred() {
                  log_debug!("     {}", instance[pred])
                }
              }
            }
            red_info += instance.force_preds(
              Some((pred, None, TTerms::conj(tterms)))
            ) ? ;


            instance.check("after unfolding") ?
          },
          // Failed is caught before this match, and false is not possible for
          // the function generating `res`.
          Failed | SuccessFalse => unreachable!(),
        }

        if instance.forced_terms_of(pred).is_some() {
          red_info.preds += 1
        } else {
          if_verb!{
            log_debug!{ "  did not remove, still appears in lhs of" }
            for clause in instance.clauses_of_pred(pred).0 {
              log_debug!{ "  {}", instance.clauses()[* clause].to_string_info( instance.preds() ) ? }
            }
            log_debug!{ "  and rhs of" }
            for clause in instance.clauses_of_pred(pred).1 {
              log_debug!{ "  {}", instance.clauses()[* clause].to_string_info( instance.preds() ) ? }
            }
          }
        }
      }
    }

    Ok( red_info )
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
where Slver: Solver<'kid, ()> {
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

    let clauses = self.clauses_to_rm.len() ;
    let preds = self.true_preds.len() ;
    instance.forget_clauses( self.clauses_to_rm.drain(0..).collect() ) ? ;
    let mut info: RedInfo = (preds, clauses, nu_clause_count).into() ;
    info += instance.force_true( self.true_preds.drain() ) ? ;

    Ok( info )
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
where Slver: Solver<'kid, ()> {
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

          if clause.lhs_is_empty() {
            if let Some(b) = term.bool() {
              if b {
                clauses_to_rm.push(clause_idx) ;
                continue 'clause_iter
              } else {
                log_debug!{
                  "unsat because of {}",
                  clause.to_string_info( instance.preds() ) ?
                }
                // Clause is true => false.
                bail!( ErrorKind::Unsat )
              }
            } else if solver.trivial_impl(
              clause.vars(), Some(term).into_iter(), & term::fls()
            ) ? {
              log_debug!{
                "unsat because of {}",
                clause.to_string_info( instance.preds() ) ?
              }
              // Clause true => false.
              bail!( ErrorKind::Unsat )
            }
          }
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
      log_debug!{ "  dropped {} trivial clause(s)", clause_cnt }
    }
    Ok( (0, clause_cnt, 0).into() )
  }
}
