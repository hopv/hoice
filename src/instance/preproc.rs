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

  let res = if conf.preproc.simple_red {
    let mut kid = ::rsmt2::Kid::new( conf.solver.conf() ).chain_err(
      || ErrorKind::Z3SpawnError
    ) ? ;
    let solver = ::rsmt2::solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    if let Some(log) = conf.solver.log_file("preproc") ? {
      run( instance, profiler, Some( solver.tee(log) ) )
    } else {
      run( instance, profiler, Some(solver) )
    }
  } else {
    run(instance, profiler, None as Option<::rsmt2::PlainSolver<Parser>>)
  } ;
  profile!{ |profiler| tick "pre-proc" } ;
  log_info!{ "done with pre-processing" }
  res

}

pub fn run<'kid, S: Solver<'kid, Parser>>(
  instance: & mut Instance, profiler: & Profiler, solver: Option<S>
) -> Res<()> {
  let mut reductor = Reductor::new(solver) ;

  let mut changed = true ;
  'preproc: while changed {

    instance.check("before simplification") ? ;
    profile!{ |profiler| tick "pre-proc", "simplify" }
    instance.simplify_clauses() ? ;
    profile!{ |profiler| mark "pre-proc", "simplify" }
    instance.check("after simplification") ? ;

    log_info!{
      "instance after simplification:\n{}\n\n",
      instance.to_string_info(()) ?
    }

    log_info!{ "done simplifying, reducing" }
    profile!{ |profiler| tick "pre-proc", "reducing" }
    changed = reductor.run(instance, & profiler) ? ;
    instance.check("after reduction") ? ;
    profile!{ |profiler| mark "pre-proc", "reducing" }

    log_info!{ "done reducing" }

    log_info!{
      "instance after reduction:\n{}\n\n", instance.to_string_info(()) ?
    }

  }

  Ok(())
}





/// Reductor, stores the reduction strategies and a solver.
pub struct Reductor<S> {
  /// Strategies.
  strats: Vec< Box<RedStrat> >,
  /// Solver strats.
  solver_strats: Option< (S, SimpleOneRhs) >,
}
impl<'kid, S: Solver<'kid, Parser>> Reductor<S> {
  /// Constructor.
  pub fn new(solver: Option<S>) -> Self {
    let strats: Vec< Box<RedStrat> > = vec![
      Box::new( Trivial {} ),
      // Box::new( ForcedImplies::new() ),
    ] ;
    let solver_strats = solver.map(
      |solver| (solver, SimpleOneRhs::new())
    ) ;

    Reductor { strats, solver_strats }
  }

  /// Runs reduction.
  pub fn run(
    & mut self, instance: & mut Instance, _profiler: & Profiler
  ) -> Res<bool> {
    
    for strat in & mut self.strats {
      log_info!("applying {}", conf.emph( strat.name() )) ;
      let (pred_cnt, clse_cnt) = strat.apply(instance) ? ;
      instance.check("work") ? ;
      if pred_cnt + clse_cnt > 0 {
        profile!{
          |_profiler| format!("{} pred red", strat.name()) => add pred_cnt
        }
        profile!{
          |_profiler| "predicates eliminated" => add pred_cnt
        }
        profile!{
          |_profiler| format!("{} clause red", strat.name()) => add clse_cnt
        }
        profile!{
          |_profiler| "clauses eliminated" => add clse_cnt
        }
        return Ok(true)
      }
    }

    if let Some((ref mut solver, ref mut strat)) = self.solver_strats {
      // for strat in strats {
        log_info!("applying {}", conf.emph( strat.name() )) ;
        let (pred_cnt, clse_cnt) = strat.apply(instance, solver) ? ;
        instance.check("work") ? ;
        if pred_cnt + clse_cnt > 0 {
          profile!{
            |_profiler| format!("{} pred red", strat.name()) => add pred_cnt
          }
          profile!{
            |_profiler| "predicates eliminated" => add pred_cnt
          }
          profile!{
            |_profiler| format!("{} clause red", strat.name()) => add clse_cnt
          }
          profile!{
            |_profiler| "clauses eliminated" => add clse_cnt
          }
          return Ok(true)
        }
      // }
    }

    Ok(false)
  }
}




/// Wrapper around a negated implication for smt printing.
struct NegImplWrap<'a> {
  /// Lhs.
  lhs: & 'a [ Term ],
  /// Rhs.
  rhs: & 'a Term,
}
impl<'a> ::rsmt2::Expr2Smt<()> for NegImplWrap<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: & ()
  ) -> SmtRes<()> {
    let msg = "writing negated implication" ;
    smtry_io!(msg => write!(w, "(not ")) ;
    if self.lhs.is_empty() {
      smtry_io!( msg => self.rhs.write(w, |w, var| var.default_write(w)) )
    } else {
      smtry_io!( msg => write!(w, "(=> (and") ) ;
      for term in self.lhs {
        smtry_io!( msg => write!(w, " ") ) ;
        smtry_io!( msg => term.write(w, |w, var| var.default_write(w)) )
      }
      smtry_io!( msg => write!(w, ") ") ) ;
      smtry_io!( msg => self.rhs.write(w, |w, var| var.default_write(w)) ) ;
      smtry_io!( msg => write!(w, ")") )
    } ;
    smtry_io!( msg => write!(w, ")") ) ;
    Ok(())
  }
}
/// True if an implication of terms is a tautology.
fn trivial_impl<'kid, S: Solver<'kid, Parser>>(
  solver: & mut S, vars: & VarMap<VarInfo>, lhs: & [Term], rhs: & Term
) -> Res<bool> {
  solver.push(1) ? ;
  for var in vars {
    if var.active {
      solver.declare_const(& var.idx, & var.typ, & ()) ?
    }
  }
  solver.assert( & NegImplWrap { lhs, rhs }, & () ) ? ;
  let sat = solver.check_sat() ? ;
  solver.pop(1) ? ;
  Ok(! sat)
}



/// Returns the strongest term such that `/\ lhs => (pred args)`.
fn term_of_app<
  Lhs: IntoIterator<Item = TTerm>,
>(
  instance: & Instance, lhs: Lhs, pred: PrdIdx, args: VarMap<Term>,
) -> Res<
  Option<
    Either< Vec<TTerm>, bool >
  >
> {
  let mut map = VarHMap::with_capacity( instance[pred].sig.len() ) ;
  let mut app_vars = VarSet::with_capacity( instance[pred].sig.len() ) ;
  let mut tterms = Vec::with_capacity( 7 ) ;

  for (index, arg) in args.into_index_iter() {
    if let Some(var) = arg.var_idx() {
      let _ = app_vars.insert(var) ;
      if let Some(pre) = map.insert(var, term::var(index)) {
        tterms.push(
          TTerm::T( term::eq( term::var(index), pre ) )
        )
      }
    } else if let Some(b) = arg.bool() {
      let var = term::var(index) ;
      tterms.push(
        TTerm::T(
          if b { var } else { term::app(Op::Not, vec![var]) }
        )
      )
    } else if let Some(i) = arg.int() {
      tterms.push(
        TTerm::T( term::eq( term::var(index), term::int(i) ) )
      )
    } else {
      return Ok(None)
    }
  }

  for tterm in lhs {
    if let Some(b) = tterm.bool() {
      if b { continue } else {
        return Ok( Some( Either::Rgt(false) ) )
      }
    }
    let tterm_vars = tterm.vars() ;
    if tterm_vars.is_subset( & app_vars ) {
      let tterm = tterm.subst_total(& map) ? ;
      tterms.push(tterm)
    } else if tterm_vars.is_disjoint(& app_vars) {
      ()
    } else {
      return Ok( None )
    }
  }

  if tterms.is_empty() {
    Ok( Some( Either::Rgt(true) ) )
  } else {
    Ok( Some( Either::Lft(tterms) ) )
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
  fn apply(& mut self, & mut Instance) -> Res<(usize, usize)> ;
}


/// Forces to false predicates appearing only in the lhs of the clauses.
pub struct Trivial {}
impl HasName for Trivial {
  fn name(& self) -> & 'static str { "trivial" }
}
impl RedStrat for Trivial {

  fn apply(& mut self, instance: & mut Instance) -> Res<(usize, usize)> {

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

    Ok((pred_cnt, clse_cnt))
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
//   fn apply(& mut self, instance: & mut Instance) -> Res<(usize, usize)> {
//     let mut clauses_rmed = 0 ;

//     let mut clause_idx: ClsIdx = 0.into() ;
//     'iter_clauses: while clause_idx < instance.clauses.len() {

//       if instance[clause_idx].lhs.is_empty() {
//         let clause = instance.forget_clause(clause_idx) ? ;
//         clauses_rmed += 1 ;
//         match clause.rhs {
//           TTerm::P { pred, args } => match term_of_app(
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
//                 TTerm::P { pred, args } => match term_of_app(
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
  /// Applies the reduction strategy. Returns the number of predicates reduced
  /// and the number of clauses forgotten.
  fn apply(
    & mut self, & mut Instance, & mut Slver
  ) -> Res<(usize, usize)> ;
}





/// Unfolds predicates that appear as the rhs of a single clause, and for
/// which the part of the lhs mentioning the variables used by the predicate
/// are completely separated from the rest.
///
/// Actually, currently this version will replace the term iff the lhs
/// mentions nothing but the variables used in the predicate application (rhs).
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
    & mut self, instance: & mut Instance, solver: & mut Slver
  ) -> Res<(usize, usize)> {
    debug_assert!( self.true_preds.is_empty() ) ;
    debug_assert!( self.false_preds.is_empty() ) ;
    debug_assert!( self.preds.is_empty() ) ;
    let mut clauses_rmed = 0 ;
    let mut pred_count = 0 ;

    for pred in instance.pred_indices() {
      if instance.clauses_of_pred(pred).1.len() == 1 {
        let clause =
          * instance.clauses_of_pred(pred).1.iter().next().unwrap() ;
        let (pred, res) = if let TTerm::P {
          pred, ref args
        } = instance[clause].rhs {
          match term_of_app(
            instance, instance[clause].lhs.clone(), pred, args.clone()
          ) ? {
            None => continue,
            Some(res) => (pred, res),
          }
        } else {
          bail!("inconsistent instance state")
        } ;

        let Clause { lhs, vars, .. } = instance.forget_clause(clause) ? ;
        clauses_rmed += 1 ;

        // Don't unfold if lhs is not satisfiable.
        let lhs: Vec<Term> = lhs.into_iter().filter_map(
          |tterm| match tterm {
            TTerm::T(t) => Some(t),
            _ => None,
          }
        ).collect() ;
        if trivial_impl(
          solver, & vars, & lhs, & term::fls()
        ) ? {
          continue
        }

        log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
        pred_count += 1 ;
        match res {
          Either::Rgt(true) => {
            log_info!("  => true") ;
            clauses_rmed += instance.force_true(Some(pred)) ? ;
          },
          Either::Rgt(false) => {
            log_info!("  => false") ;
            clauses_rmed += instance.force_false(Some(pred)) ? ;
          },

          Either::Lft(tterms) => {
            if_not_bench!{
              for tterm in & tterms {
                log_info!("  => {}", tterm)
              }
            }
            clauses_rmed += instance.force_preds(Some((pred, tterms))) ? ;
          },
        }
      }
    }

    Ok((pred_count, clauses_rmed))
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


