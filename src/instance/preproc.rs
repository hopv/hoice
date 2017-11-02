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
    let res = {
      let solver = ::rsmt2::solver(& mut kid, ()).chain_err(
        || "while constructing preprocessing's solver"
      ) ? ;
      if let Some(log) = conf.solver.log_file("preproc") ? {
        run(
          instance, profiler, Some( SolverWrapper::new(solver.tee(log)) )
        )
      } else {
        run( instance, profiler, Some( SolverWrapper::new(solver) ) )
      }
    } ;
    kid.kill() ? ;
    res
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
      instance.set_unsat()
    },
    Err(e) => bail!(e),
    Ok(()) => ()
  }

  log_info!{ "building predicate dependency graph" }

  use instance::graph::* ;

  let graph = Graph::new(& instance) ;
  graph.check(& instance) ? ;
  graph.to_dot(& instance, "pred_dep") ? ;

  Ok(())
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


  preproc_dump!(
    instance =>
    "preproc_000_original_instance", "Instance before pre-processing."
  ) ? ;

  log_info!{ "starting basic simplifications" }

  profile!{ |profiler| tick "pre-proc", "propagate" }
  let simplify = instance.simplify_clauses() ? ;
  profile!{ |profiler| mark "pre-proc", "propagate" }
  profile!{
    |profiler| format!(
      "{:>25} clause red", "propagate"
    ) => add simplify.clauses_rmed
  }
  profile!{
    |profiler| format!(
      "{:>25} clause add", "propagate"
    ) => add simplify.clauses_added
  }
  total += simplify ;

  log_debug!{
    "|===| after propagation:\n{}\n\n", instance.to_string_info(()) ?
  }

  preproc_dump!(
    instance =>
    "preproc_001_simplified_instance", "Instance after basic simplifications."
  ) ? ;

  if ! conf.preproc.reduction {
    return Ok(())
  }

  let mut cnt = 2 ;

  let mut changed = true ;
  'preproc: while changed {

    log_info!{ "running simplification" }

    profile!{ |profiler| tick "pre-proc", "simplifying" }
    let red_info = reductor.run_simplification(instance, & profiler) ? ;
    total += red_info ;
    profile!{ |profiler| mark "pre-proc", "simplifying" }

    log_debug!{
      "|===| after simplification:\n{}\n\n", instance.to_string_info(()) ?
    }

    preproc_dump!(
      instance =>
        format!("preproc_{:0>3}_reduction", cnt),
        "Instance after smt-free reduction"
    ) ? ;
    cnt += 1 ;

    log_info!{ "running reduction" }
    profile!{ |profiler| tick "pre-proc", "reducing" }
    let red_info = reductor.run(instance, & profiler, & mut cnt) ? ;
    changed = red_info.non_zero() ;
    total += red_info ;
    instance.check("after reduction") ? ;
    profile!{ |profiler| mark "pre-proc", "reducing" }
    log_info!{ "done reducing" }

    preproc_dump!(
      instance =>
        format!("preproc_{:0>3}_smt_reduction", cnt),
        "Instance after smt-based reduction"
    ) ? ;
    cnt += 1 ;

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

  preproc_dump!(
    instance =>
      format!("preproc_{:0>3}_fixed_point", cnt),
      "Instance after reduction fixed-point"
  ) ? ;

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
    if conf.preproc.one_rhs && conf.preproc.one_rhs_full {
      solver_strats.push( Box::new( OneRhs::new() ) )
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
    & mut self, instance: & mut Instance, _profiler: & Profiler,
    cnt: & mut usize
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

    if let Some(_) = self.solver_strats {
      // let mut changed = true ;
      // while changed {
      //   changed = false ;

      let mut changed = true ;

      'run_strats: while changed {
        total += self.run_simplification(instance, _profiler) ? ;
        changed = false ;

        if let Some((ref mut solver, ref mut strats)) = self.solver_strats {
          for strat in strats.iter_mut() {
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

            preproc_dump!(
              instance =>
                format!(
                  "preproc_{:0>3}_{}", cnt, {
                    let mut s = String::new() ;
                    for token in strat.name().split_whitespace() {
                      s = if s.is_empty() { token.into() } else {
                        format!("{}_{}", s, token)
                      }
                    }
                    s
                  }
                ),
                "Instance after smt-based reduction"
            ) ? ;
            * cnt += 1 ;

            total += red_info ;
            instance.check( strat.name() ) ? ;

            // If something changed, re-run all strats.
            if changed { continue 'run_strats }
          }
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
pub fn terms_of_app<F: Fn(Term) -> Term>(
  instance: & Instance, pred: PrdIdx, args: & VarMap<Term>, f: F
) -> Res<
  Option<(HConSet<Term>, VarHMap<Term>, VarSet)>
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
      postponed.push( (index, arg) )
    }
  }

  for (var, arg) in postponed {
    if let Some( (term, _) ) = arg.subst_total(& map) {
      terms.insert(
        f( term::eq(term::var(var), term) )
      ) ;
    } else if let Some((v, inverted)) = arg.invert(var) {
      let _prev = map.insert(v, inverted) ;
      debug_assert_eq!( _prev, None ) ;
      let is_new = app_vars.insert(v) ;
      debug_assert!( is_new )
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
        self.solver.declare_const_u(& var.idx, & var.typ) ?
      }
    }
    self.solver.assert_u( & NegConj::new(terms) ) ? ;
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
        self.solver.declare_const_u(& var.idx, & var.typ) ?
      }
    }
    self.solver.assert_u( & NegImplWrap::new(lhs, rhs) ) ? ;
    let sat = self.solver.check_sat() ? ;
    self.solver.pop(1) ? ;
    Ok(! sat)
  }

  /// Returns the weakest predicate `p` such that `(p args) /\ lhs_terms /\
  /// {lhs_preds \ (p args)} => rhs`.
  ///
  /// The result is `(pred_app, pred_apps, terms)` which semantics is `pred_app
  /// \/ (not /\ tterms) \/ (not /\ pred_apps)`.
  pub fn terms_of_lhs_app(
    & mut self, instance: & Instance,
    lhs_terms: & HConSet<Term>, lhs_preds: & PredApps,
    rhs: Option<(PrdIdx, & VarMap<Term>)>,
    pred: PrdIdx, args: & VarMap<Term>,
  ) -> Res< ExtractRes<(Option<PredApp>, Vec<PredApp>, Vec<Term>)> > {
    log_debug!{ "    terms_of_lhs_app on {} {}", instance[pred], args }

    let (terms, map, app_vars) = if let Some(res) = terms_of_app(
      instance, pred, args, |term| term
    ) ? {
      res
    } else {
      return Ok(ExtractRes::Failed)
    } ;
    let mut terms: Vec<_> = terms.into_iter().collect() ;

    for term in lhs_terms {
      let vars = term.vars() ;
      if vars.is_subset(& app_vars) {
        let (term, _) = term.subst_total(& map).ok_or::<Error>(
          "failure during total substitution".into()
        ) ? ;
        terms.push(term)
      } else if vars.is_disjoint(& app_vars) {
        // Does not constrain the arguments as long as we don't later enter the
        // next branch.
        ()
      } else {
        return Ok(ExtractRes::Failed)
      }
    }

    let mut pred_apps = Vec::with_capacity( lhs_preds.len() ) ;

    for (prd, argss) in lhs_preds {
      if * prd == pred {
        match argss.len() {
          1 => continue,
          len => bail!(
            "illegal call to `terms_of_lhs_app`, \
            predicate {} is applied {} time(s), expected 1",
            instance[pred], len
          ),
        }
      }
      for args in argss {
        let mut nu_args = VarMap::with_capacity( args.len() ) ;
        for arg in args {
          if let Some( (nu_arg, _) ) = arg.subst_total(& map) {
            nu_args.push(nu_arg)
          } else {
            // For all we know, `prd` is false and there's no constraint on
            // the predicate we're resolving. Even if the variables are
            // completely disjoint.
            // Can't resolve without quantifiers.
            return Ok(ExtractRes::Failed)
          }
        }
        pred_apps.push( (* prd, nu_args) )
      }
    }

    let pred_app = if let Some((pred, args)) = rhs {
      let mut nu_args = VarMap::with_capacity( args.len() ) ;
      for arg in args {
        if let Some( (nu_arg, _) ) = arg.subst_total(& map) {
          nu_args.push(nu_arg)
        } else {
          // For all we know, `pred` is true and there's no constraint on
          // the predicate we're resolving. Even if the variables are
          // completely disjoint.
            // Can't resolve without quantifiers.
          return Ok(ExtractRes::Failed)
        }
      }
      Some((pred, nu_args))
    } else {
      None
    } ;

    Ok( ExtractRes::Success( (pred_app, pred_apps, terms) ) )
  }



  pub fn terms_of_rhs_app(
    & mut self, quantifiers: bool,
    instance: & Instance, var_info: & VarMap<VarInfo>,
    lhs_terms: & HConSet<Term>, lhs_preds: & PredApps,
    pred: PrdIdx, args: & VarMap<Term>,
  ) -> Res< ExtractRes<(Qualfed, Vec<TTerm>)> > {
    log_debug!{ "  terms of rhs app on {} {}", instance[pred], args }

    let (terms, mut map, mut app_vars) = if let Some(res) = terms_of_app(
      instance, pred, args, |term| term
    ) ? {
      res
    } else {
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

    let mut tterms: Vec<_> = terms.into_iter().map(
      |t| TTerm::T(t)
    ).collect() ;
    let mut qvars = VarHMap::with_capacity(
      if quantifiers { var_info.len() - app_vars.len() } else { 0 }
    ) ;

    // Index of the first quantified variable: fresh for `pred`'s variables.
    let mut fresh = instance[pred].sig.next_index() ;

    // Creates fresh (quantified) variables for the variables that are not
    // currently known.
    //
    // - `$quantifiers` if `false` and quantified variables are needed, early
    //   return with `ExtractRes::Failed` instead of creating fresh variables
    // - `$vars` the variables we're considering
    // - `$app_vars` currently known variables
    // - `$map` map from clause variables to predicate variables
    // - `$qvars` map from quantified variables to their `VarInfo`
    // - `$info` the clause's `VarInfo`s (used to retrieve types)
    // - `$fresh` the next fresh variable for the predicate
    macro_rules! add_vars {
      (
        if $quantifiers:ident : $vars:expr => $app_vars:ident
        |> $map:expr, $qvars:expr, $info:expr, $fresh:expr
      ) => (
        for var in $vars {
          let is_new = $app_vars.insert(var) ;
          if is_new {
            if ! quantifiers {
              return Ok(ExtractRes::Failed)
            }
            let _prev = $qvars.insert($fresh, $info[var].typ) ;
            debug_assert_eq!( None, _prev ) ;
            let _prev = $map.insert( var, term::var($fresh) ) ;
            debug_assert_eq!( None, _prev ) ;
            $fresh.inc()
          }
        }
      ) ;
    }

    log_debug! {
      "    working on lhs predicate applications ({})", lhs_preds.len()
    }

    // Predicate applications need to be in the resulting term. Depending on
    // the definition they end up having, the constraint might be trivial.
    for (pred, argss) in lhs_preds {
      for args in argss {
        let mut nu_args = VarMap::with_capacity( args.len() ) ;
        for arg in args {
          add_vars!{
            if quantifiers: arg.vars() =>
              app_vars |> map, qvars, var_info, fresh
          }
          if let Some( (nu_arg, _) ) = arg.subst_total(& map) {
            nu_args.push(nu_arg)
          } else {
            // Unreacheable as we just made sure all variables in the argument
            // are in the map.
            bail!("unreachable, rhs substitution was not total")
          }
        }
        tterms.push( TTerm::P { pred: * pred, args: nu_args } )
      }
    }

    log_debug! {
      "    working on lhs terms ({})", lhs_terms.len()
    }

    // This last step finds terms which variables are related to the ones from
    // the predicate applications.

    // The terms we're currently looking at.
    let mut lhs_terms_vec: Vec<_> = Vec::with_capacity( lhs_terms.len() ) ;
    for term in lhs_terms {
      match term.bool() {
        Some(true) => (),
        Some(false) => return Ok(ExtractRes::Trivial),
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
        for var in & app_vars {
          log_debug! { "      - {}", var_info[* var] }
        }
      }

      for term in lhs_terms_vec.drain(0..) {
        log_debug! { "      {}", term.to_string_info(var_info) ? }
        let vars = term.vars() ;

        if app_vars.len() == var_info.len()
        || vars.is_subset(& app_vars) {
          let term = if let Some((term, _)) = term.subst_total(& map) {
            term
          } else {
            bail!("[unreachable] failure during total substitution")
          } ;
          log_debug! { "      sub {}", term }
          tterms.push( TTerm::T(term) )

        } else if vars.is_disjoint(& app_vars) {
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
          let term = if let Some((term, _)) = term.subst_total(& map) {
            term
          } else {
            bail!("[unreachable] failure during total substitution")
          } ;
          tterms.push( TTerm::T(term) )
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

    debug_assert! { quantifiers || qvars.is_empty() }

    if tterms.is_empty() {
      Ok(ExtractRes::SuccessTrue)
    } else {
      Ok(
        ExtractRes::Success( (qvars, tterms.into_iter().collect()) )
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


/// Calls [`Instance::force_trivial`][force trivial] and
/// [`Instance::drop_trivial`][drop trivial].
///
/// [force trivial]: ../instance/struct.Instance.html#method.force_trivial (Instance's force_trivial method)
/// [drop trivial]: ../instance/struct.Instance.html#method.drop_trivial (Instance's drop_trivial method)
pub struct Trivial {}
impl HasName for Trivial {
  fn name(& self) -> & 'static str { "trivial" }
}
impl RedStrat for Trivial {

  fn apply(& mut self, instance: & mut Instance) -> Res<RedInfo> {
    let mut info = instance.drop_trivial() ? ;
    info += instance.force_trivial() ? ;
    Ok(info)
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
///
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

        let res = if let Some((_this_pred, args)) = instance[clause].rhs() {
          debug_assert_eq!( pred, _this_pred ) ;
          solver.terms_of_rhs_app(
            false, instance, instance[clause].vars(),
            instance[clause].lhs_terms(), instance[clause].lhs_preds(),
            pred, args
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
          Success((_quants, tterms)) => {
            debug_assert! { _quants.is_empty() } ;
            if_not_bench! {
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

        if instance.is_known(pred) {
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







/// Tries to reduce predicates that appear as an antecedent in exactly one
/// clause.
///
/// For a predicate `p`, if the clause in question is
///
/// ```bash
/// lhs(v_1, ..., v_n) and p(v_1, ..., v_n) => rhs(v_1, ..., v_n)
/// ```
///
/// then `p` is reduced to
///
/// ```bash
/// (not lhs(v_1, ..., v_n)) or rhs(v_1, ..., v_n)
/// ```
///
/// **iff** `p` is the only predicate application in the clause, `lhs` is sat
/// and `(not rhs)` is sat.
///
/// If `lhs` or `(not rhs)` is unsat, then the clause is dropped and `p` is
/// reduced to `true` since it does not appear as an antecedent anywhere
/// anymore.
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
      let clause_idx = {
        let (mut lhs_clauses, rhs_clauses) = (
          instance.clauses_of_pred(pred).0.iter(),
          instance.clauses_of_pred(pred).1
        ) ;
        if let Some(clause) = lhs_clauses.next() {
          if lhs_clauses.next().is_none()
          && ! rhs_clauses.contains(clause) {
            * clause
          } else {
            continue
          }
        } else {
          continue
        }
      } ;

      // Skip if the clause mentions this predicate more than once.
      if let Some( argss ) = instance[clause_idx].lhs_preds().get(& pred) {
        if argss.len() > 1 { continue }
      }

      log_debug!{
        "trying to unfold {}", instance[pred]
      }

      let res = {
        let clause = & instance[clause_idx] ;
        // log_debug!{
        //   "from {}", clause.to_string_info( instance.preds() ) ?
        // }
        let args = if let Some(argss) = clause.lhs_preds().get(& pred) {
          let mut iter = argss.iter() ;
          let res = iter.next().unwrap() ;
          // Guaranteed by the check before the `log_debug`.
          debug_assert!( iter.next().is_none() ) ;
          res
        } else {
          bail!("inconsistent instance state")
        } ;

        solver.terms_of_lhs_app(
          instance, clause.lhs_terms(), clause.lhs_preds(), clause.rhs(),
          pred, args
        ) ?
      } ;

      if res.is_failed() { continue }

      log_debug!{
        "from {}",
        instance.clauses()[clause_idx].to_string_info( instance.preds() ) ?
      }

      // instance.forget_clause(clause_idx) ? ;
      // red_info.clauses_rmed += 1 ;

      // log_info!{ "  instance:\n{}", instance.to_string_info( () ) ? }

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
        Success((pred_app, pred_apps, terms)) => {
          if_not_bench!{
            log_debug!{ "  => (or" }
            if let Some((pred, ref args)) = pred_app {
              let mut s = format!("({}", instance[pred]) ;
              for arg in args {
                s = format!("{} {}", s, arg)
              }
              log_debug!{ "    {})", s }
            }
            log_debug!{ "    (not" }
            log_debug!{ "      (and" }
            for & (pred, ref args) in & pred_apps {
              let mut s = format!("({}", instance[pred]) ;
              for arg in args {
                s = format!("{} {}", s, arg)
              }
              log_debug!{ "        {})", s }
            }
            for term in & terms {
              log_debug!{ "        {}", term }
            }
          }
          red_info += instance.force_pred_right(
            pred, pred_app, pred_apps, terms
          ) ? ;

          instance.check("after unfolding") ?
        },
        // Failed is caught before this match, and the rest is not possible for
        // the function generating `res`.
        _ => unreachable!(),
      }

      if instance.is_known(pred) {
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

    Ok( red_info )
  }
}






/// Works on predicates that appear in only one rhs.
///
/// Only works on predicates that need qualifiers to be reduced, complements
/// `SimpleOneRhs`.
///
/// If a predicate `p` appears as a rhs in only in one clause
///
/// ```bash
/// lhs(v_1, ..., v_n, v_n+1, ..., v_k) => p(v_1, ..., v_n)
/// ```
///
/// then it is forced to
///
/// ```bash
/// p(v_1, ..., v_n) = exists (v_n+1, ..., v_k) . lhs(v_1, ..., v_k)
/// ```
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
  fn name(& self) -> & 'static str { "one rhs" }
}
impl<'kid, Slver> SolverRedStrat<'kid, Slver> for OneRhs
where Slver: Solver<'kid, ()> {
  fn apply(
    & mut self, instance: & mut Instance, solver: & mut SolverWrapper<Slver>
  ) -> Res<RedInfo> {
    debug_assert!( self.new_vars.is_empty() ) ;
    let mut red_info: RedInfo = (0,0,0).into() ;

    'all_preds: for pred in instance.pred_indices() {
      if instance.clauses_of_pred(pred).1.len() == 1 {
        let clause =
          * instance.clauses_of_pred(pred).1.iter().next().unwrap() ;

        if instance.clauses_of_pred(pred).0.contains(& clause) {
        // || instance[clause].lhs_pred_apps_len() > 1 {
          continue 'all_preds
        }

        log_debug!{
          "trying to unfold {}", instance[pred]
        }

        let res = if let Some((_this_pred, args)) = instance[clause].rhs() {
          debug_assert_eq!( pred, _this_pred ) ;
          solver.terms_of_rhs_app(
            true, instance, instance[clause].vars(),
            instance[clause].lhs_terms(), instance[clause].lhs_preds(),
            pred, args
          ) ?
        } else {
          bail!("inconsistent instance state")
        } ;

        if res.is_failed() {
          log_debug!{ "  skipping" }
          continue
        }

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
          Success( (qvars, tterms) ) => {
            if_not_bench!{
              log_debug!("  {} quantified variables", qvars.len()) ;
              for (var, typ) in & qvars {
                log_debug!("  - v_{}: {}", var, typ)
              }
              for tterm in & tterms {
                log_debug!("  => {}", tterm ) ;
                if let Some(pred) = tterm.pred() {
                  log_debug!("     {}", instance[pred])
                }
              }
            }
            red_info += instance.force_preds(
              Some((pred, Some(qvars), TTerms::conj(tterms)))
            ) ? ;


            instance.check("after unfolding") ?
          },
          // Failed is caught before this match, and false is not possible for
          // the function generating `res`.
          Failed | SuccessFalse => unreachable!(),
        }

        if instance.is_known(pred) {
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

        // We did something, stop there in case more simple stuff can be done.
        break 'all_preds

      }
    }

    Ok( red_info )
  }
}






/// Removes clauses that are trivially true by smt.
///
/// A clause if removed if either
///
/// - `false and _ => _`: its lhs has atoms, and their conjunction is unsat, or
/// - `_ => true`: its rhs is an atom and its negation is unsatisfiable.
pub struct SmtTrivial {
  /// Clauses to remove, avoids re-allocation.
  clauses_to_rm: Vec<ClsIdx>,
}
impl SmtTrivial {
  /// Constructor.
  pub fn new() -> Self {
    SmtTrivial {
      clauses_to_rm: Vec::with_capacity(10),
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
    debug_assert!{ self.clauses_to_rm.is_empty() }

    { // Push a scope so that `lhs` is dropped because it borrows `instance`.
      // Remove when non-lexical lifetimes land.
      let mut lhs = Vec::with_capacity(10) ;
      let fls = term::fls() ;

      'clause_iter: for (
        clause_idx, clause
      ) in instance.clauses().index_iter() {
        lhs.clear() ;

        for term in clause.lhs_terms() {
          match term.bool() {
            Some(true) => (),
            Some(false) => {
              self.clauses_to_rm.push(clause_idx) ;
              continue 'clause_iter
            },
            _ => lhs.push(term),
          }
        }

        if clause.rhs().is_none() && clause.lhs_preds().is_empty() {
          // Either it is trivial, or falsifiable regardless of the predicates.
          if solver.trivial_impl(
            clause.vars(), lhs.drain(0..), & fls
          ) ? {
            self.clauses_to_rm.push(clause_idx) ;
            continue 'clause_iter
          } else {
            log_debug!{
              "unsat because of {}",
              clause.to_string_info( instance.preds() ) ?
            }
            bail!( ErrorKind::Unsat )
          }
        } else {
          if lhs.is_empty() {
            continue 'clause_iter
          }
        }

        if solver.trivial_impl(clause.vars(), lhs.drain(0..), & fls) ? {
          self.clauses_to_rm.push(clause_idx) ;
          continue 'clause_iter
        }
      }
    }

    let clause_cnt = self.clauses_to_rm.len() ;
    instance.forget_clauses(& mut self.clauses_to_rm) ? ;
    if clause_cnt > 0 {
      log_debug!{ "  dropped {} trivial clause(s)", clause_cnt }
    }
    Ok( (0, clause_cnt, 0).into() )
  }
}
