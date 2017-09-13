#![doc = r#"Reduction strategies.

The strategies are attached `struct`s so that they can be put in a
vector using single dispatch. That way, they can be combined however we want.
"#]

use common::* ;
use instance::* ;



/// Runs pre-processing
pub fn work(
  instance: & mut Instance, profiler: & Profile
) -> Res<()> {

  profile!{ |profiler| tick "pre-proc" }

  let res = if conf.simple_red {
    let mut kid = ::rsmt2::Kid::mk( conf.solver_conf() ).chain_err(
      || ErrorKind::Z3SpawnError
    ) ? ;
    let solver = ::rsmt2::solver(& mut kid, Parser).chain_err(
      || "while constructing the teacher's solver"
    ) ? ;
    if let Some(log) = conf.smt_log_file("preproc") ? {
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
  instance: & mut Instance, profiler: & Profile, solver: Option<S>
) -> Res<()> {
  let mut reductor = Reductor::mk(solver) ;

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
  pub fn mk(solver: Option<S>) -> Self {
    let strats: Vec< Box<RedStrat> > = vec![
      Box::new( Trivial {} ),
      // Box::new( ForcedImplies::mk() ),
    ] ;
    let solver_strats = solver.map(
      |solver| (solver, SimpleOneRhs::mk())
    ) ;

    Reductor { strats, solver_strats }
  }

  /// Runs reduction.
  pub fn run(
    & mut self, instance: & mut Instance, _profiler: & Profile
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
    solver.declare_const(& var.idx, & var.typ, & ()) ?
  }
  solver.assert( & NegImplWrap { lhs, rhs }, & () ) ? ;
  let sat = solver.check_sat() ? ;
  solver.pop(1) ? ;
  Ok(! sat)
}


// /// Reduces an instance.
// ///
// /// Returns true if something was changed.
// pub fn work(instance: & mut Instance, _profiler: & Profile) -> Res<bool> {
//   let mut strategies = strategies() ;
//   let mut did_something = false ;
//   let mut changed = true ;
//   'all_strats_fp: while changed {
//     if instance.clauses.is_empty() { break 'all_strats_fp }
//     changed = false ;
//     for strat in & mut strategies {
//       if instance.clauses.is_empty() { break 'all_strats_fp }
//       log_info!("\napplying {}", conf.emph( strat.name() )) ;
//       let (mut pred_cnt, mut clse_cnt) = strat.apply(instance) ? ;
//       instance.check("work") ? ;
//       let mut this_changed = pred_cnt + clse_cnt > 0 ;
//       changed = changed || this_changed ;
//       'strat_fp: while this_changed {
//         let (nu_pred_cnt, nu_clse_cnt) = strat.apply(instance) ? ;
//         pred_cnt += nu_pred_cnt ;
//         clse_cnt += nu_clse_cnt ;
//         this_changed = nu_pred_cnt + nu_clse_cnt > 0
//       }
//       profile!{
//         |_profiler| format!("{} pred red", strat.name()) => add pred_cnt
//       }
//       profile!{
//         |_profiler| "predicates eliminated" => add pred_cnt
//       }
//       profile!{
//         |_profiler| format!("{} clause red", strat.name()) => add clse_cnt
//       }
//       profile!{
//         |_profiler| "clauses eliminated" => add clse_cnt
//       }
//     }
//     did_something = did_something || changed
//   }
//   log_info!("") ;
//   Ok(did_something)
// }



// Forces some predicates to false.
fn force_false<Preds: IntoIterator<Item = PrdIdx>>(
  instance: & mut Instance, preds: Preds
) -> Res<usize> {
  let mut clauses_dropped = 0 ;
  let (mut clause_lhs, mut clause_rhs) = (ClsSet::new(), ClsSet::new()) ;
  let fls = TTerm::T( instance.bool(false) ) ;
  for pred in preds.into_iter() {
    debug_assert!( clause_lhs.is_empty() ) ;
    debug_assert!( clause_rhs.is_empty() ) ;
    info!("  forcing {} to false", instance[pred]) ;
    instance.force_pred( pred, vec![ fls.clone() ] ) ? ;
    instance.drain_unlink_pred(pred, & mut clause_lhs, & mut clause_rhs) ;
    clauses_dropped += clause_lhs.len() ;
    instance.forget_clauses( clause_lhs.drain().collect() ) ? ;
    for clause in clause_rhs.drain() {
      instance.clauses[clause].rhs = fls.clone()
    }
  }
  instance.check("force_false") ? ;
  Ok(clauses_dropped)
}



// Forces some predicates to true.
fn force_true<Preds: IntoIterator<Item = PrdIdx>>(
  instance: & mut Instance, preds: Preds
) -> Res<usize> {
  let mut clauses_dropped = 0 ;
  let (mut clause_lhs, mut clause_rhs) = (ClsSet::new(), ClsSet::new()) ;
  let tru = TTerm::T( instance.bool(true) ) ;
  
  for pred in preds.into_iter() {
    debug_assert!( clause_lhs.is_empty() ) ;
    debug_assert!( clause_rhs.is_empty() ) ;

    info!("  forcing {} to true", instance[pred]) ;
    instance.force_pred( pred, vec![ tru.clone() ] ) ? ;
    instance.drain_unlink_pred(pred, & mut clause_lhs, & mut clause_rhs) ;

    for clause in clause_lhs.drain() {
      let mut cnt = 0 ;
      while cnt < instance[clause].lhs.len() {
        if let TTerm::P { pred: this_pred, .. } = instance[clause].lhs[cnt] {
          if this_pred == pred {
            instance.clauses[clause].lhs.swap_remove(cnt) ;
            continue
          }
        }
        cnt += 1
      }
    }
    clauses_dropped += clause_rhs.len() ;
    instance.forget_clauses( clause_rhs.drain().collect() ) ? ;
  }
  instance.check("force_true") ? ;
  Ok(clauses_dropped)
}





/// Applies a substitution to a top term.
fn tterm_subst(
  factory: & Factory, subst: & VarHMap<Term>, tterm: & TTerm
) -> Res<TTerm> {
  match * tterm {
    TTerm::P { pred, ref args } => {
      let mut new_args = VarMap::with_capacity( args.len() ) ;
      for term in args {
        if let Some((term, _)) = factory.subst_total(
          subst, term
        ) {
          new_args.push(term)
        } else {
          bail!("total substitution failed")
        }
      }
      Ok( TTerm::P { pred, args: new_args } )
    },
    TTerm::T(ref term) => if let Some((term, _)) = factory.subst_total(
      subst, term
    ) {
      Ok( TTerm::T(term) )
    } else {
      bail!("total substitution failed")
    },
  }
}


/// Forces some predicates to be something.
fn force_pred<Preds: IntoIterator<
  Item = (PrdIdx, Vec<TTerm>)
>>(
  instance: & mut Instance, preds: Preds
) -> Res<usize> {
  let (mut clause_lhs, mut clause_rhs) = (ClsSet::new(), ClsSet::new()) ;
  let mut terms_to_add = vec![] ;
  let mut clauses_to_rm = ClsSet::new() ;

  for (pred, tterms) in preds.into_iter() {
    debug_assert!( clause_lhs.is_empty() ) ;
    debug_assert!( clause_rhs.is_empty() ) ;
    debug_assert!( terms_to_add.is_empty() ) ;

    instance.drain_unlink_pred(pred, & mut clause_lhs, & mut clause_rhs) ;

    // LHS.
    'clause_iter_lhs: for clause in clause_lhs.drain() {
      use std::iter::Extend ;
      
      if clauses_to_rm.contains(& clause) { continue 'clause_iter_lhs }

      let mut cnt = 0 ;
      'lhs_iter: while cnt < instance.clauses[clause].lhs.len() {
        if let TTerm::P {
          pred: this_pred, ..
        } = instance.clauses[clause].lhs[cnt] {
          
          if this_pred == pred {
            let tterm = instance.clauses[clause].lhs.swap_remove(cnt) ;
            let args: VarHMap<_> = tterm.args().unwrap().index_iter().map(
              |(idx, term)| (idx, term.clone())
            ).collect() ;

            for tterm in & tterms {
              let tterm = tterm_subst(& instance.factory, & args, tterm) ? ;
              match tterm.bool() {
                Some(true) => (),
                Some(false) => {
                  clauses_to_rm.insert(clause) ;
                  continue 'clause_iter_lhs
                },
                None => {
                  if let Some(pred) = tterm.pred() {
                    instance.pred_to_clauses[pred].0.insert(clause) ;
                    instance.clause_to_preds[clause].0.insert(pred) ;
                  }
                  terms_to_add.push(tterm)
                },
              }
            }
            continue 'lhs_iter
          }
        }
        cnt += 1 ;
        continue
      }

      instance.clauses[clause].lhs.extend( terms_to_add.drain(0..) )

    }

    // RHS.
    'clause_iter_rhs: for clause in clause_rhs.drain() {
      
      if clauses_to_rm.contains(& clause) { continue 'clause_iter_rhs }

      debug_assert!( terms_to_add.is_empty() ) ;

      if let TTerm::P { pred: _this_pred, ref args } = instance[clause].rhs {
        debug_assert_eq!( _this_pred, pred ) ;

        let args: VarHMap<_> = args.index_iter().map(
          |(idx, trm)| (idx, trm.clone())
        ).collect() ;

        for tterm in & tterms {
          let tterm = tterm_subst(& instance.factory, & args, tterm) ? ;
          match tterm.bool() {
            Some(true) => {
              clauses_to_rm.insert(clause) ;
              continue 'clause_iter_rhs
            },
            Some(false) => {
              terms_to_add.clear() ;
              terms_to_add.push( TTerm::T( instance.bool(false) ) ) ;
              break 'clause_iter_rhs
            },
            None => terms_to_add.push(tterm),
          }
        }
      } else {
        bail!("inconsistent instance")
      } ;

      let mut tterms = terms_to_add.drain(0..) ;
      if let Some(tterm) = tterms.next() {
        if let Some(pred) = tterm.pred() {
          instance.pred_to_clauses[pred].1.insert(clause) ;
          instance.clause_to_preds[clause].1 = Some(pred) ;
        }
        instance.clauses[clause].rhs = tterm ;
        for tterm in tterms {
          let clause = Clause::mk(
            instance.clauses[clause].vars.clone(),
            instance.clauses[clause].lhs.clone(),
            tterm
          ) ;
          instance.push_clause(clause) ?
        }
      }

    }

    instance.force_pred(pred, tterms) ? ;
  }

  let clauses_rmed = clauses_to_rm.len() ;
  instance.forget_clauses( clauses_to_rm.into_iter().collect() ) ? ;

  Ok(clauses_rmed)
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
      if let Some(pre) = map.insert(var, instance.var(index)) {
        tterms.push(
          TTerm::T( instance.eq( instance.var(index), pre ) )
        )
      }
    } else if let Some(b) = arg.bool() {
      let var = instance.var(index) ;
      tterms.push(
        TTerm::T(
          if b { var } else { instance.op(Op::Not, vec![var]) }
        )
      )
    } else if let Some(i) = arg.int() {
      tterms.push(
        TTerm::T( instance.eq( instance.var(index), instance.int(i) ) )
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
      let tterm = tterm_subst(& instance.factory, & map, & tterm) ? ;
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
      if instance.pred_to_clauses[pred].1.is_empty() {
        fls_preds.push(pred)
      } else if instance.pred_to_clauses[pred].0.is_empty() {
        tru_preds.push(pred)
      }
    }

    let pred_cnt = fls_preds.len() + tru_preds.len() ;
    let mut clse_cnt = force_false( instance, fls_preds ) ? ;
    clse_cnt += force_true( instance, tru_preds ) ? ;

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
//   fn mk() -> Self {
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
//                     Clause::mk( args.clone(), vec![], tterm.clone() )
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
//                       let term = instance.op(
//                         Op::Not, vec![
//                           instance.op(
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

//     clauses_rmed += force_true(instance, self.true_preds.drain()) ? ;
//     clauses_rmed += force_false(instance, self.false_preds.drain()) ? ;
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
  fn mk() -> Self {
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
      if instance.pred_to_clauses[pred].1.len() == 1 {
        let clause =
          * instance.pred_to_clauses[pred].1.iter().next().unwrap() ;
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
          solver, & vars, & lhs, & instance.bool(false)
        ) ? {
          continue
        }

        log_info!{ "  unfolding {}", conf.emph(& instance[pred].name) }
        pred_count += 1 ;
        match res {
          Either::Rgt(true) => {
            log_info!("  => true") ;
            clauses_rmed += force_true(instance, Some(pred)) ? ;
          },
          Either::Rgt(false) => {
            log_info!("  => false") ;
            clauses_rmed += force_false(instance, Some(pred)) ? ;
          },

          Either::Lft(tterms) => {
            if_not_bench!{
              for tterm in & tterms {
                log_info!("  => {}", tterm)
              }
            }
            clauses_rmed += force_pred(instance, Some((pred, tterms))) ? ;
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


