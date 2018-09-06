//! Predicate-to-function reduction.

use common::*;
use fun::RFun;
use instance::{info::VarInfo, instance::PreInstance, preproc::RedStrat};

pub struct FunPreds;

impl FunPreds {
    /// Finalizes a definition for a predicate.
    ///
    /// Returns the final definition and some invariants.
    pub fn finalize_definition(
        instance: &mut PreInstance,
        name: &str,
        sig: &VarInfos,
        typ: &Typ,
        mut definitions: Vec<(TermSet, Term, bool)>,
        check: bool,
    ) -> Res<Option<(Term, Option<TermSet>)>> {
        instance.reset_solver()?;

        let invs = get_invariants(instance, name, sig, typ, &mut definitions)?;

        if_log! { @3
          if let Some(invs) = invs.as_ref() {
            log! { @3 "found {} invariant(s)", invs.len() }
            for inv in invs {
              log! { @3 "  {}", inv }
            }
          } else {
            log! { @3 "none found" }
          }
        }

        if check {
            log! { @3 "checking conditions are mutually exclusive" }
            let solver = instance.solver();

            for info in sig {
                solver.declare_const(&info.idx, info.typ.get())?
            }

            solver.declare_fun(name, sig, typ.get())?;

            let mut actlits = Vec::with_capacity(definitions.len());

            for (cube, _, _) in &definitions {
                use smt::TermConj;
                let conj = TermConj::new(cube.iter());
                let actlit = solver.get_actlit()?;
                solver.assert_act_with(&actlit, &conj, true)?;
                actlits.push(actlit)
            }

            scoped! {
              let mut actlits_iter = actlits.iter() ;

              while let Some(actlit) = actlits_iter.next() {
                for other in actlits_iter.clone() {
                  let not_exclusive = solver.check_sat_act(
                    vec![ actlit, other ]
                  ) ? ;
                  if not_exclusive {
                    return Ok(None)
                  }
                }
              }
            }

            for actlit in actlits {
                solver.de_actlit(actlit)?
            }

            log! { @3 "all branches are exclusive, checking they're exhaustive" }

            for (cube, _, _) in &definitions {
                use smt::TermConj;
                let conj = TermConj::new(cube.iter());
                solver.assert_with(&conj, false)?;
            }

            let not_exhaustive = solver.check_sat()?;

            if not_exhaustive {
                // warn!("fun_preds: branches are not exhaustive, moving on anyways") ;
                log! { @3 "branches are not exhaustive, aborting" }
                return Ok(None);
            } else {
                log! { @3 "branches are exhaustive, building definition" }
            }
        }

        let mut def = None;

        for (cube, value, _) in definitions.into_iter().rev() {
            let nu_def = if let Some(def) = def {
                term::ite(term::and(cube.into_iter().collect()), value, def)
            } else {
                value
            };
            def = Some(nu_def)
        }

        if let Some(def) = def {
            Ok(Some((def, invs)))
        } else {
            bail!("empty definitions during finalization in fun_preds")
        }
    }

    /// Reduces a predicate to a function.
    pub fn reduce_pred(
        instance: &mut PreInstance,
        pred: PrdIdx,
        use_all_args: bool,
    ) -> Res<Option<RedInfo>> {
        let mut info = RedInfo::new();
        // Clauses to remove.
        let mut to_rm = vec![];

        log!(@2 "working on {}", conf.emph(& instance[pred].name));

        debug_assert! { to_rm.is_empty() }

        let mut var_infos = VarInfos::new();

        let args_len = if use_all_args {
            instance[pred].sig.len()
        } else {
            instance[pred].sig.len() - 1
        };

        for typ in &instance[pred].sig[0..args_len] {
            let idx = var_infos.next_index();
            let var_info = VarInfo::new(idx.default_str(), typ.clone(), idx);
            var_infos.push(var_info)
        }
        let last: Option<VarIdx> = if use_all_args {
            None
        } else {
            Some((instance[pred].sig.len() - 1).into())
        };

        let pred_fun_name = make_fun_name(&instance[pred].name).chain_err(|| {
            format!(
                "while creating function for predicate {}",
                conf.emph(&instance[pred].name)
            )
        })?;
        let pred_fun_typ = if let Some(last) = last.as_ref() {
            instance[pred].sig[*last].clone()
        } else {
            typ::bool()
        };

        let mut rfun = RFun::new(pred_fun_name.clone(), var_infos, pred_fun_typ.clone());
        rfun.set_synthetic(pred);

        macro_rules! abort {
            ($($stuff:tt)*) => {{
                let _ = fun::retrieve_dec(&pred_fun_name);
                return Ok(None);
            }};
        }

        fun::register_dec(rfun)?;

        let mut definitions = vec![];

        for clause in instance.clauses_of(pred).1 {
            to_rm.push(*clause);

            if_log! { @3
              log!(@3 "working on clause #{}", clause) ;
              log!(@4 "lhs terms:") ;
              for term in instance[* clause].lhs_terms() {
                log!(@4 "  {}", term)
              }
              log!(@4 "lhs preds:") ;
              for (pred, argss) in instance[* clause].lhs_preds() {
                for args in argss {
                  log!(@4 "  ({} {})", instance[* pred], args)
                }
              }
            }
            let clause = *clause;
            let (_, rhs_args) = instance[clause].rhs().unwrap();
            log!(@4 "rhs args:\n  ({} {})", instance[pred], rhs_args);

            let (mut cube, mut subst) =
                if let Some((cube, subst)) = args_invert(rhs_args, args_len)? {
                    (cube, subst)
                } else {
                    log!(@3 "failed to invert rhs arguments");
                    abort!()
                };

            if_log! { @4
              log!(@4 "substitution:") ;
              for (var, term) in subst.iter() {
                log!(@4 "  v_{} -> {}", var, term)
              }
              log!(@4 "cube:") ;
              for term in cube.iter() {
                log!(@4 "  {}", term)
              }
            }

            let recursive = instance[clause].lhs_preds().contains_key(&pred);

            let mut lhs_argss: Vec<_> = instance[clause]
                .lhs_preds()
                .get(&pred)
                .map(|argss| argss.iter().collect())
                .unwrap_or_else(Vec::new);

            let mut nu_args = Vec::with_capacity(args_len);

            let mut value = None;

            while !lhs_argss.is_empty() {
                let prev_len = lhs_argss.len();
                let mut failed: Res<_> = Ok(false);

                lhs_argss.retain(|args| {
                    for arg in &args[0..args_len] {
                        if let Some((arg, _)) = arg.subst_total(&subst) {
                            nu_args.push(arg)
                        } else {
                            nu_args.clear();
                            return true;
                        }
                    }
                    let nu_args = ::std::mem::replace(
                        &mut nu_args,
                        Vec::with_capacity(instance[pred].sig.len() - 1),
                    );

                    let fun_app = term::fun(pred_fun_typ.clone(), pred_fun_name.clone(), nu_args);

                    let okay = if let Some(last) = last.as_ref() {
                        let last = *last;

                        map_invert(&args[last], fun_app, &mut subst, &mut cube)
                    } else {
                        value.get_or_insert_with(Vec::new).push(fun_app);
                        Ok(true)
                    };

                    match okay {
                        // Success, don't retain.
                        Ok(true) => false,
                        // Failure, retain.
                        Ok(false) => {
                            log!(@3
                  "could not invert last argument ({:?}) of ({} {})",
                  last, instance[pred], args
                );
                            if let Ok(failed) = failed.as_mut() {
                                *failed = true
                            }
                            true
                        }
                        // Error, do whatever.
                        err => {
                            failed = err.chain_err(|| {
                                format!("while inverting ({} {})", instance[pred], args)
                            });
                            true
                        }
                    }
                });

                if failed? {
                    log!(@3 "failed");
                    abort!()
                } else if lhs_argss.len() == prev_len {
                    // not making progress.
                    log!(@3 "not making progress on lhs preds");
                    abort!()
                }
            }

            if_log! { @4
              log!(@4 "subst after lhs preds:") ;
              for (var, term) in & subst {
                log!(@4 "  v_{} -> {}", var, term)
              }
            }

            for term in instance[clause].lhs_terms() {
                if let Some((term, _)) = term.subst_total(&subst) {
                    cube.insert(term);
                } else {
                    log!(@3 "total substitution on term {} failed", term);
                    abort!()
                }
            }

            if_log! { @4
              log!(@4 "cube:") ;
              for term in & cube {
                log!(@4 "  {}", term)
              }
            }

            let res = if let Some(last) = last.as_ref() {
                if let Some((res, _)) = rhs_args[*last].subst_total(&subst) {
                    res
                } else {
                    log!(@3 "failed to retrieve value, aborting");
                    abort!()
                }
            } else if let Some(conj) = value {
                term::and(conj)
            } else {
                term::tru()
            };

            log!(@4 "value: {}", res);

            definitions.push((cube, res, recursive))
        }

        definitions.sort_by(|(c_1, _, rec_1), (c_2, _, rec_2)| {
            use std::cmp::Ordering::*;
            if *rec_1 && !*rec_2 {
                Less
            } else if *rec_2 && !*rec_1 {
                Greater
            } else {
                c_1.len().cmp(&c_2.len())
            }
        });

        if use_all_args {
            let mut tru = TermSet::new();
            tru.insert(term::tru());
            definitions.push((tru, term::fls(), false))
        }

        log!(@3 "done working on {}", instance[pred]);
        if_log! { @4
          for (cube, res, recursive) in & definitions {
            log!(@4 "when {{") ;
            for term in cube {
              log!(@4 "  {}", term)
            }
            log!(@4 "}} -{}> {}", if * recursive { "rec-" } else { "" }, res)
          }
        }

        // let mut def = pred_fun_typ.default_term() ;

        // for (cube, res) in definitions.into_iter().rev() {
        //   let cond = term::and(
        //     cube.into_iter().collect()
        //   ) ;
        //   def = term::ite( cond, res, def )
        // }

        let mut dec = fun::retrieve_dec(&pred_fun_name)?;

        let (def, invs) = if let Some(def) = FunPreds::finalize_definition(
            instance,
            &pred_fun_name,
            &dec.sig,
            &pred_fun_typ,
            definitions,
            !use_all_args,
        )? {
            def
        } else {
            log!(@3 "failed to finalize definition, aborting");
            abort!()
        };

        if let Some(invs) = invs {
            for inv in invs {
                dec.invariants.insert(inv);
            }
        }

        instance.reset_solver()?;

        log!(@3 "definition:\n  {}", def);

        log!(@4 "registering...");
        dec.set_def(def);

        let fun = fun::mk(dec).chain_err(|| {
            format!(
                "while creating internal function for predicate {}",
                conf.bad(&instance[pred].name)
            )
        })?;

        instance.add_companion_fun(pred, fun.clone());

        // Restarting solver so that the function is declared.
        instance.reset_solver()?;

        info.clauses_rmed += to_rm.len();
        instance.forget_clauses(&mut to_rm)?;

        let mut args = Vec::with_capacity(args_len);
        for (var, typ) in instance[pred].sig.index_iter().take(args_len) {
            args.push(term::var(var, typ.clone()))
        }
        let fun_app = term::fun(fun.typ.clone(), fun.name.clone(), args);

        let def = if let Some(last) = last.as_ref() {
            term::eq(term::var(*last, fun.typ.clone()), fun_app)
        } else {
            fun_app
        };

        info.preds += 1;
        let mut tterm_set = TTermSet::new();
        tterm_set.insert_term(def);
        info += instance.force_dnf_left(pred, vec![(Quantfed::new(), tterm_set)])?;

        Ok(Some(info))
    }
}

impl RedStrat for FunPreds {
    fn name(&self) -> &'static str {
        "fun_preds"
    }

    fn new(_: &Instance) -> Self {
        FunPreds
    }

    fn apply(&mut self, instance: &mut PreInstance) -> Res<RedInfo> {
        let mut info = RedInfo::new();

        let mut new_stuff = true;

        while new_stuff {
            new_stuff = false;

            if instance.active_pred_count() <= 1 {
                return Ok(info);
            }

            let mut to_inline: Vec<_> = instance
                .preds()
                .iter()
                .filter_map(|info| {
                    let inline = {
                        let pred = info.idx;

                        // Predicate is still unknown.
                        ! instance.is_known(pred)

          // When `pred` appears in the rhs of a clause, the lhs only mentions
          // `pred`.
          && instance.clauses_of(pred).1.iter().all(
            |clause| instance[* clause].lhs_preds().iter().all(
              |(p, _)| * p == pred
            )
          )

          // `pred` appears more than once in a clause where it's not alone.
          // && instance.clauses_of(pred).0.iter().any(
          //   |clause| instance[* clause].lhs_preds().get(
          //     & pred
          //   ).unwrap().len() > 1
          //   && (
          //     instance[* clause].lhs_preds().len() > 1
          //     || instance[* clause].rhs().map(
          //       |(p, _)| pred != * p
          //     ).unwrap_or(false)
          //   )
          // )

          // `pred` has only one dtyp argument (ignoring the last argument)
          && info.sig.len() > 1
          && info.sig[ 0 .. info.sig.len() - 1 ].iter().fold(
            0, |acc, typ| if typ.is_dtyp() { acc + 1 } else { acc }
          ) <= 1
                    };

                    if inline {
                        Some(info.idx)
                    } else {
                        None
                    }
                }).collect();

            to_inline.sort_by(|p_1, p_2| {
                let adt_count_1 =
                    instance[*p_1]
                        .sig
                        .iter()
                        .fold(0, |acc, typ| if typ.is_dtyp() { acc + 1 } else { acc });
                let adt_count_2 =
                    instance[*p_2]
                        .sig
                        .iter()
                        .fold(0, |acc, typ| if typ.is_dtyp() { acc + 1 } else { acc });

                adt_count_1.cmp(&adt_count_2).reverse()
            });

            if to_inline.is_empty() {
                return Ok(info);
            }

            while let Some(pred) = to_inline.pop() {
                let res = FunPreds::reduce_pred(instance, pred, false)?;
                // pause("to resume fun_preds", & Profiler::new()) ;
                if let Some(red_info) = res {
                    new_stuff = true;
                    info += red_info;
                    break;
                } else {
                    // let res = FunPreds::reduce_pred(instance, pred, true) ? ;
                    // // pause("to resume fun_preds", & Profiler::new()) ;
                    // if let Some(red_info) = res {
                    //   new_stuff = true ;
                    //   info += red_info ;
                    //   break
                    // }
                    ()
                }
            }
        }

        Ok(info)
    }
}

/// Builds a cube and a substitution corresponding to inverting some arguments.
pub fn args_invert(args: &VarTerms, args_len: usize) -> Res<Option<(TermSet, VarHMap<Term>)>> {
    let (mut cube, mut subst) = (TermSet::new(), VarHMap::new());

    debug_assert! { args.len() >= 1 }

    let mut postponed = Vec::new();
    let mut current: Vec<_> = args
        .index_iter()
        .take(args_len)
        .map(|(var, term)| (term::var(var, term.typ()), term))
        .collect();

    let mut did_something;

    while !current.is_empty() {
        debug_assert! { postponed.is_empty() }

        did_something = false;

        for (var, term) in current.drain(0..) {
            log! { @4 "attempting to invert {} | {}", var, term }
            if_log! { @5
              log! { @5 "subst:" }
              for (var, term) in & subst {
                log! { @5 "  {}: {}", var.default_str(), term }
              }
              log! { @5 "cube:" }
              for term in & cube {
                log! { @5 "  {}", term }
              }
            }

            let worked = map_invert(term, var.clone(), &mut subst, &mut cube)?;

            if worked {
                log! { @4 "success :)" }
                did_something = true;
            } else {
                log! { @4 "failed :(" }
                postponed.push((var, term))
            }
        }

        // Making progress?
        if !did_something {
            return Ok(None);
        } else {
            ::std::mem::swap(&mut postponed, &mut current)
        }
    }

    Ok(Some((cube, subst)))
}

/// Inverts a term to complete a substitution and a cube.
///
/// Returns false if the invertion failed.
pub fn map_invert(
    to_invert: &Term,
    term: Term,
    subst: &mut VarHMap<Term>,
    cube: &mut TermSet,
) -> Res<bool> {
    debug_assert_eq! { to_invert.typ(), term.typ() }

    let mut nu_cube = vec![];
    let mut nu_subst = VarHMap::<Term>::new();

    let mut stack = vec![(term, to_invert.get())];

    while let Some((term, to_invert)) = stack.pop() {
        match to_invert {
            RTerm::DTypNew { typ, name, args } => {
                let selectors = typ.selectors_of(name)?;
                debug_assert_eq! { args.len(), selectors.len() }

                // `term` must be a specific variant: `name`
                nu_cube.push(term::dtyp_tst(name.clone(), term.clone()));

                for (arg, (slc, _)) in args.iter().zip(selectors.iter()) {
                    stack.push((term::dtyp_slc(arg.typ(), slc.clone(), term.clone()), arg))
                }
            }

            RTerm::Cst(val) => {
                nu_cube.push(term::eq(term, term::val(val.clone())));
                continue;
            }

            RTerm::Var(_, var) => {
                if let Some(t) = subst.get(var) {
                    nu_cube.push(term::eq(term, t.clone()));
                    continue;
                } else if let Some(t) = nu_subst.get(var) {
                    nu_cube.push(term::eq(term, t.clone()));
                    continue;
                }

                nu_subst.insert(*var, term);
            }

            // Constant array.
            RTerm::CArray { term: inner, typ } => {
                stack.push((
                    // Array is constant, select any value.
                    term::select(term, typ.default_term()),
                    inner.get(),
                ))
            }

            RTerm::App { typ, op, args } => {
                match op {
                    Op::CMul => if args[0].val().is_some() {
                        let nu_term = if typ.is_int() {
                            // Current term modulo `val` is zero.
                            nu_cube.push(term::eq(
                                term::modulo(term.clone(), args[0].clone()),
                                term::int(0),
                            ));
                            term::idiv(vec![term, args[0].clone()])
                        } else if typ.is_real() {
                            term::div(vec![term, args[0].clone()])
                        } else {
                            bail!("unexpected multiplication over type {}", typ)
                        };
                        stack.push((nu_term, args[1].get()));
                        continue;
                    } else {
                        bail!("illegal CMul term {}", to_invert)
                    },

                    Op::Add => {
                        let mut subtraction = vec![term];
                        let mut not_substed = None;

                        for arg in args {
                            if let Some((term, _)) = arg.subst_total(&(&*subst, &nu_subst)) {
                                subtraction.push(term)
                            } else if not_substed.is_some() {
                                return Ok(false);
                            } else {
                                not_substed = Some(arg.get())
                            }
                        }

                        let nu_term = term::sub(subtraction);

                        if let Some(nu_to_invert) = not_substed {
                            stack.push((nu_term, nu_to_invert))
                        } else {
                            nu_cube.push(term::eq(
                                nu_term,
                                if typ.is_int() {
                                    term::int_zero()
                                } else if typ.is_real() {
                                    term::real_zero()
                                } else {
                                    bail!("unexpected addition over type {}", typ)
                                },
                            ));
                        }
                        continue;
                    }

                    Op::Sub => {
                        let mut sub = None;
                        let mut add = vec![term];
                        let mut not_substed = None;

                        let mut first = true;
                        for arg in args {
                            if let Some((term, _)) = arg.subst_total(&(&*subst, &nu_subst)) {
                                if first {
                                    debug_assert! { sub.is_none() }
                                    sub = Some(term)
                                } else {
                                    add.push(term)
                                }
                            } else if not_substed.is_some() {
                                return Ok(false);
                            } else {
                                // Careful of the polarity here vvvvv
                                not_substed = Some((arg.get(), first))
                            }

                            first = false
                        }

                        let nu_term = term::add(add);
                        let nu_term = if let Some(sub) = sub {
                            term::sub(vec![nu_term, sub])
                        } else {
                            nu_term
                        };

                        if let Some((nu_to_invert, positive)) = not_substed {
                            stack.push((
                                if positive {
                                    nu_term
                                } else {
                                    term::u_minus(nu_term)
                                },
                                nu_to_invert,
                            ))
                        } else {
                            nu_cube.push(term::eq(
                                nu_term,
                                if typ.is_int() {
                                    term::int_zero()
                                } else if typ.is_real() {
                                    term::real_zero()
                                } else {
                                    bail!("unexpected addition over type {}", typ)
                                },
                            ));
                        }

                        continue;
                    }

                    _ => (),
                }

                let mut nu_args = Vec::with_capacity(args.len());
                for arg in args {
                    if let Some((arg, _)) = arg.subst_total(&(&*subst, &nu_subst)) {
                        nu_args.push(arg)
                    } else {
                        return Ok(false);
                    }
                }

                nu_cube.push(term::eq(term, term::app(*op, nu_args)))
            }

            RTerm::DTypSlc {
                typ,
                name,
                term: inner,
            } => if let Some((inner, _)) = inner.subst_total(&(&*subst, &nu_subst)) {
                nu_cube.push(term::eq(
                    term,
                    term::dtyp_slc(typ.clone(), name.clone(), inner),
                ))
            } else {
                return Ok(false);
            },

            RTerm::DTypTst {
                name, term: inner, ..
            } => if let Some((inner, _)) = inner.subst_total(&(&*subst, &nu_subst)) {
                nu_cube.push(term::eq(term, term::dtyp_tst(name.clone(), inner)))
            } else {
                return Ok(false);
            },

            RTerm::Fun { typ, name, args } => {
                let mut nu_args = Vec::with_capacity(args.len());
                for arg in args {
                    if let Some((arg, _)) = arg.subst_total(&(&*subst, &nu_subst)) {
                        nu_args.push(arg)
                    } else {
                        return Ok(false);
                    }
                }

                nu_cube.push(term::eq(
                    term,
                    term::fun(typ.clone(), name.clone(), nu_args),
                ))
            }
        }
    }

    for term in nu_cube {
        cube.insert(term);
    }
    for (var, term) in nu_subst {
        let prev = subst.insert(var, term);
        debug_assert! { prev.is_none() }
    }

    Ok(true)
}

/// Extracts invariants from a function pre-definition.
///
/// Assumes the solver has nothing declared / asserted.
fn get_invariants(
    instance: &mut PreInstance,
    name: &str,
    sig: &VarInfos,
    typ: &Typ,
    definitions: &mut Vec<(TermSet, Term, bool)>,
) -> Res<Option<TermSet>> {
    let mut candidates = TermMap::new();

    log! { @3 "looking for invariants..." }

    for (idx, (cube, _, _)) in definitions.iter_mut().enumerate() {
        cube.retain(|term| {
            let mut applications = None;

            term.iter(|sub| {
                if let Some((fun, _)) = sub.fun_inspect() {
                    if fun == name {
                        applications
                            .get_or_insert_with(TermSet::new)
                            .insert(sub.to_hcons());
                    }
                }
            });

            if let Some(applications) = applications {
                candidates
                    .entry(term.clone())
                    .or_insert_with(|| (Vec::new(), applications))
                    .0
                    .push(idx);
                false
            } else {
                true
            }
        })
    }

    if candidates.is_empty() {
        return Ok(None);
    }

    let mut invariants = TermSet::new();

    {
        let solver = instance.solver();

        for info in sig {
            solver.declare_const(&info.idx, info)?
        }

        solver.declare_fun(name, sig, typ.get())?;

        // use smt::{SmtTerm, TermConj};

        for (candidate, _) in candidates {
            invariants.insert(candidate);
        }

        // for (candidate, (cubes, apps)) in candidates {
        //     log! { @4 "checking candidate: {}", candidate }
        //     let mut invariant = true;

        //     solver.comment_args(format_args!("checking candidate {}", candidate))?;

        //     for (cube, value, _) in definitions.iter() {
        //         if_log! { @5
        //           log! { @5 "cube:" }
        //           for term in cube {
        //             log! { @5 "  {}", term }
        //           }
        //         }
        //         let actlit = solver.get_actlit()?;
        //         solver.comment("asserting cube")?;
        //         for term in cube {
        //             solver.assert_act(&actlit, &SmtTerm::new(term))?
        //         }
        //         solver.comment("forcing args")?;
        //         for app in apps.iter() {
        //             solver.comment_args(format_args!("{} = {}", app, value))?;
        //             let term = term::eq(app.clone(), value.clone());
        //             solver.assert_act(&actlit, &SmtTerm::new(&term))?
        //         }
        //         solver.comment("forcing branche's return value")?;
        //         solver.assert_act_with(&actlit, &TermConj::new(Some(&candidate)), false)?;

        //         let sat = solver.check_sat_act(Some(&actlit))?;

        //         if sat {
        //             invariant = false;
        //             break;
        //         }
        //     }

        //     if invariant {
        //         log! { @4 "invariant :)" }
        //         let is_new = invariants.insert(candidate);
        //         debug_assert! { is_new }
        //     } else {
        //         log! { @4 "not invariant :(" }
        //         for cube in cubes {
        //             definitions[cube].0.insert(candidate.clone());
        //         }
        //     }
        // }
    }

    instance.reset_solver()?;

    let res = if invariants.is_empty() {
        None
    } else {
        Some(invariants)
    };

    Ok(res)
}

fn make_fun_name(other_name: &str) -> Res<String> {
    let split: Vec<_> = other_name.split('|').collect();
    let str = match split.len() {
        1 => format!("{}_hoice_reserved_fun", other_name),
        3 if split[0] == "" && split[2] == "" && split[1] != "" => {
            format!("|{}_hoice_reserved_fun|", split[1])
        }
        _ => bail!("illegal symbol `{}`", other_name),
    };
    Ok(str)
}
