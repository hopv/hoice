//! Types related to qualifiers.
//!
//! A qualifier is essentially a signature and a term. The idea is that, given
//! some sample (input values) for a predicate, we want to to find all the
//! combinations of values that make sense for this qualifier.
//!
//! We also want to avoid storing the same qualifier more than once. For
//! instance:
//!
//! ```smt
//! (define-fun qual      ((v_1 Int) (v_2 Bool))
//!   (ite v_2 (> v_1 0) (= v_1 0))
//! )
//! (define-fun same_qual ((v_1 Bool) (v_2 Int))
//!   (ite v_1 (> v_2 0) (= v_2 0))
//! )
//! ```
//!
//! Hence the signature of a qualifier is sorted by the ordering over types.
//! For instance, say we want to have the following qualifier
//!
//! ```smt
//! (define-fun qual ((v_1 Int) (v_2 Bool) (v_3 Int))
//!   (ite v_2 (= v_3 (+ v_1 7)) (= v_1 0))
//! )
//! ```
//!
//! Then, assuming `Bool <= Int`, the signature is re-ordered either as `v_2`,
//! `v_3`, `v_1` or `v_2`, `v_1`, `v_3`. Either way, the signature of the
//! qualifier is `Bool Int Int`. Say `v_3` is first, then the qualifier becomes
//!
//! ```smt
//! (define-fun qual ((v_1 Bool) (v_2 Int) (v_3 Int))
//!   (ite v_1 (= v_2 (+ v_3 7)) (= v_3 0))
//! )
//! ```
//!
//! This guarantees that two qualifiers coming from the same term modulo
//! alpha-renaming will yield the same qualifier. Terms are currently not in
//! normal form though, so the same is not true for semantically-equivalent
//! terms.
//!
//! **Remark about equality.** One might think that two qualifiers with the
//! same term have to be the same qualifier. This is not true because of
//! polymorphism:
//!
//! ```smt
//! (define-fun qual ((v_1 Int) (v_2 Int))
//!   (= v_1 v_2)
//! )
//! (define-fun other_qual ((v_1 Bool) (v_2 Bool))
//!   (= v_1 v_2)
//! )
//! ```
//!
//! More precisely, this is currently not true because qualifiers cannot be
//! polymorphic.

// use hashconsing::* ;

use crate::common::*;

/// Extracts qualifier-related information from a predicate application.
fn qual_info_of(
    eq_quals: &mut VarHMap<Term>,
    quals: &mut NuQuals,
    pred: PrdIdx,
    args: &VarTerms,
) -> Res<(PrdIdx, VarHMap<Term>, TermSet)> {
    debug_assert!(eq_quals.is_empty());

    // Qualifiers generated while looking at predicate applications.
    let mut app_quals: TermSet = TermSet::with_capacity(17);

    // All the *clause var* to *pred var* maps for this predicate application.
    let mut map: VarHMap<Term> = VarHMap::with_capacity(args.len());

    for (pred_var, term) in args.index_iter() {
        let pred_var_typ = term.typ();

        // Parameter's a variable?
        if let Some(clause_var_index) = term.var_idx() {
            // Clause variable's already known as parameter?
            if let Some(other_pred_var) = map.get(&clause_var_index).cloned() {
                // Equality qualifier.
                app_quals.insert(term::eq(
                    term::var(pred_var, pred_var_typ),
                    other_pred_var.clone(),
                ));
            } else {
                // Add to map.
                let _prev = map.insert(clause_var_index, term::var(pred_var, pred_var_typ));
                debug_assert!(_prev.is_none())
            }
        } else {
            // Modulo constraint?
            if term.typ().is_int() {
                let mut maybe_cmul = Some(term);
                let mut maybe_add = None;

                // Term's an addition?
                if let Some(args) = term.add_inspect() {
                    if args.len() != 2 {
                        maybe_cmul = None
                    } else if args[0].val().is_some() {
                        maybe_add = Some(&args[0]);
                        maybe_cmul = Some(&args[1])
                    } else if args[1].val().is_some() {
                        maybe_add = Some(&args[1]);
                        maybe_cmul = Some(&args[0])
                    } else {
                        maybe_cmul = None
                    }
                }

                // Multiplication by a constant?
                if let Some(term) = maybe_cmul {
                    if let Some((val, _)) = term.cmul_inspect() {
                        let qual = term::eq(
                            term::modulo(term::var(pred_var, typ::int()), val.to_term().unwrap()),
                            maybe_add.cloned().unwrap_or_else(|| term::int(0)),
                        );
                        quals.insert(qual, pred)?;
                    }
                }
            }

            // Parameter's not a variable, store potential equality.
            let _prev = eq_quals.insert(pred_var, term.clone());
            debug_assert!(_prev.is_none());

            // Try to revert the term.
            if let Some((var, term)) = term.invert_var(pred_var, pred_var_typ) {
                if !map.contains_key(&var) {
                    map.insert(var, term);
                } else if let Some(other_pred_var) = map.get(&var) {
                    app_quals.insert(term::eq(other_pred_var.clone(), term));
                }
            }
        }
    }

    for (pred_var, term) in eq_quals.drain() {
        if let Some((term, _)) = term.subst_total(&map) {
            app_quals.insert(term::eq(term::var(pred_var, term.typ()), term));
        }
    }

    if !app_quals.is_empty() {
        let build_conj = app_quals.len() > 1;
        let mut conj = Vec::with_capacity(app_quals.len());

        for term in &app_quals {
            if build_conj {
                conj.push(term.clone())
            }
            quals.insert(term.clone(), pred)?;
        }

        if build_conj {
            let term = term::and(conj);
            quals.insert(term, pred)?;
        }
    }

    Ok((pred, map, app_quals))
}

/// Generates qualifiers from two terms.
fn qual_of_terms<F: FnMut(Term) -> Res<()>>(
    mut f: F,
    term: &Term,
    othr: &Term,
    clause_count: usize,
) -> Res<()> {
    match (term.app_inspect(), othr.app_inspect()) {
        (Some((op_1 @ Op::Ge, term_args)), Some((op_2 @ Op::Gt, othr_args)))
        | (Some((op_1 @ Op::Gt, term_args)), Some((op_2 @ Op::Ge, othr_args)))
        | (Some((op_1 @ Op::Gt, term_args)), Some((op_2 @ Op::Gt, othr_args)))
        | (Some((op_1 @ Op::Ge, term_args)), Some((op_2 @ Op::Ge, othr_args)))
        | (Some((op_1 @ Op::Eql, term_args)), Some((op_2 @ Op::Gt, othr_args)))
        | (Some((op_1 @ Op::Gt, term_args)), Some((op_2 @ Op::Eql, othr_args)))
        | (Some((op_1 @ Op::Ge, term_args)), Some((op_2 @ Op::Eql, othr_args)))
        | (Some((op_1 @ Op::Eql, term_args)), Some((op_2 @ Op::Ge, othr_args)))
        | (Some((op_1 @ Op::Eql, term_args)), Some((op_2 @ Op::Eql, othr_args))) => {
            if term_args[0].typ().is_arith() && term_args[0].typ() == othr_args[0].typ() {
                let nu_lhs = term::add(vec![term_args[0].clone(), othr_args[0].clone()]);

                let old_vars_1 = term::vars(&term_args[0]);
                let old_vars_2 = term::vars(&othr_args[0]);
                let nu_vars = term::vars(&nu_lhs);

                let use_qual = clause_count < 35
                    || (nu_vars.len() <= 2)
                    || (nu_vars.len() < old_vars_1.len() + old_vars_2.len());

                // if use_qual {
                //     log! { @4
                //       "from {}", term ;
                //       "     {}", othr
                //     }
                // } else {
                //     // log! { @1
                //     //   " " ;
                //     //   "skipping" ;
                //     //   "from {}", term ;
                //     //   "     {}", othr ;
                //     //   "  -> {}", nu_lhs
                //     // }
                // }

                if use_qual {
                    let op = match (op_1, op_2) {
                        (_, Op::Gt) | (Op::Gt, _) => Op::Gt,

                        (_, Op::Ge) | (Op::Ge, _) => Op::Ge,

                        (Op::Eql, Op::Eql) => Op::Eql,

                        _ => unreachable!(),
                    };

                    let nu_term = term::app(
                        op,
                        vec![
                            nu_lhs,
                            term::add(vec![term_args[1].clone(), othr_args[1].clone()]),
                        ],
                    );
                    f(nu_term.clone())?;

                    // log! { @4 "  -> {}", nu_term }

                    if op_1 == Op::Eql {
                        let nu_lhs = term::sub(vec![othr_args[0].clone(), term_args[0].clone()]);
                        let nu_rhs = term::sub(vec![othr_args[1].clone(), term_args[1].clone()]);
                        let nu_term = term::app(op, vec![nu_lhs, nu_rhs]);
                        f(nu_term)?;
                    } else if op_2 == Op::Eql {
                        let nu_lhs = term::sub(vec![term_args[0].clone(), othr_args[0].clone()]);
                        let nu_rhs = term::sub(vec![term_args[1].clone(), othr_args[1].clone()]);
                        let nu_term = term::app(op, vec![nu_lhs, nu_rhs]);
                        f(nu_term)?;
                    }
                }
            }
        }

        _ => (),
    }
    Ok(())
}

/// Qualifier version of a term.
fn qual_of_term(term: &Term, map: &VarHMap<Term>) -> Option<Term> {
    if let Some((qual, true)) = term.subst_total(&map) {
        if let Some(qual) = qual.rm_neg() {
            Some(qual)
        } else {
            Some(qual)
        }
    } else {
        None
    }
}

/// Extracts some qualifiers from a clause.
///
/// # TO DO
///
/// - write an explanation of what actually happens
/// - and some tests, probably
fn qualifiers_of_clause(instance: &Instance, clause: &Clause, quals: &mut NuQuals) -> Res<()> {
    // if clause.from_unrolling { return Ok(()) }

    let build_conj = instance.clauses().len() < 2000 && conf.ice.mine_conjs;

    // Variable to term maps, based on the way the predicates are used.
    let mut maps = vec![];

    scoped! {
      // Represents equalities between *pred vars* and terms over *clause
      // variables*. These will be added to `app_quals` if the total
      // substitution of the term by `map` succeeds.
      let mut eq_quals = VarHMap::with_capacity(7) ;

      clause.all_pred_apps_do(
        |pred, args| {
          maps.push(
            qual_info_of(& mut eq_quals, quals, pred, args) ?
          ) ;
          Ok(())
        }
      ) ?
    }

    apply_mappings(quals, clause, build_conj, maps, instance.clauses().len())?;

    Ok(())
}

/// Applies a mapping for some predicate on a clause.
fn apply_mappings(
    quals: &mut NuQuals,
    clause: &Clause,
    build_conj: bool,
    maps: Vec<(PrdIdx, VarHMap<Term>, TermSet)>,
    clause_count: usize,
) -> Res<()> {
    let term_count = clause.lhs_terms().len();

    // Stores the subterms of `lhs_terms`.
    let mut subterms = Vec::with_capacity(7);
    // Stores all (sub-)terms.
    let mut all_terms = if term_count <= 100 {
        Some(TermSet::with_capacity(clause.lhs_terms().len()))
    } else {
        None
    };

    macro_rules! all_terms {
    ( $fun:ident( $($args:tt)* ) ) => (
      if let Some(all_terms) = all_terms.as_mut() {
        all_terms.$fun($($args)*) ;
      }
    ) ;
  }

    // Stores all top terms.
    let mut conj = TermSet::with_capacity(clause.lhs_terms().len());

    // Look for atoms and try to apply the mappings.
    for (pred, map, app_quals) in maps {
        all_terms!(clear());
        conj.clear();

        for term in clause.lhs_terms() {
            if let Some((term, true)) = term.subst_total(&map) {
                all_terms!(insert(term.clone()));
                conj.insert(term.clone());
                let term = if let Some(term) = term.rm_neg() {
                    term
                } else {
                    term
                };
                quals.insert(term, pred)?;
                ()
            }

            debug_assert!(subterms.is_empty());
            subterms.push(term);

            while let Some(subterm) = subterms.pop() {
                if let Some((qual, true)) = subterm.subst_total(&map) {
                    all_terms!(insert(qual));
                }

                match subterm.app_inspect() {
                    Some((Op::Or, terms))
                    | Some((Op::And, terms))
                    | Some((Op::Not, terms))
                    | Some((Op::Impl, terms)) => {
                        for term in terms {
                            subterms.push(term);
                            if let Some(term) = qual_of_term(term, &map) {
                                quals.insert(term, pred)?;
                            }
                        }
                    }

                    // Some( (Op::Eql, terms) ) |
                    // Some( (Op::Distinct, terms) ) => if terms.iter().all(
                    //   |term| term.typ().is_bool()
                    // ) {
                    //   for term in terms {
                    //     subterms.push(term) ;
                    //     if let Some(term) = qual_of_term(term, & map) {
                    //       quals.insert(term, pred) ? ;
                    //     }
                    //   }
                    // } else if let Some( (qual, true) ) = subterm.subst_total(& map) {
                    //   all_terms!().insert(qual) ;
                    // },
                    _ => {
                        if let Some((qual, true)) = subterm.subst_total(&map) {
                            all_terms!(insert(qual));
                        }
                    }
                }
            }
        }

        if build_conj {
            quals.insert(term::and(app_quals.iter().cloned().collect()), pred)?;
            if conj.len() > 1 {
                quals.insert(term::and(conj.iter().cloned().collect()), pred)?;
                quals.insert(term::and(conj.drain().chain(app_quals).collect()), pred)?;
            }
        }

        if let Some(all_terms) = all_terms.as_ref() {
            let mut all_terms = all_terms.iter();

            if all_terms.len() <= 100 {
                while let Some(term) = all_terms.next() {
                    for other in all_terms.clone() {
                        qual_of_terms(
                            |qual| {
                                quals.insert(qual, pred)?;
                                Ok(())
                            },
                            term,
                            other,
                            clause_count,
                        )?
                    }
                }
            }
        }
    }

    Ok(())
}

/// Mines the clauses in an instance for qualifiers.
fn mine_instance(instance: &Instance, quals: &mut NuQuals) -> Res<()> {
    // Add boolean qualifiers for all predicate's bool vars.
    for pred in instance.preds() {
        for (var, typ) in pred.sig.index_iter() {
            let mut bool_vars = Vec::new();
            if typ.is_bool() {
                let var = term::var(var, typ::bool());
                quals.insert(var.clone(), pred.idx)?;
                bool_vars.push(var)
            }
            if bool_vars.len() > 1 {
                quals.insert(term::and(bool_vars.clone()), pred.idx)?;
                quals.insert(term::or(bool_vars), pred.idx)?;
            }
        }
    }

    // Mine all clauses.
    for clause in instance.clauses() {
        qualifiers_of_clause(instance, clause, quals)?
    }

    Ok(())
}

pub struct NuQuals {
    instance: Arc<Instance>,
    quals: PrdMap<VarHMap<TermSet>>,
    rng: Rng,
}
impl NuQuals {
    /// Mines a signature.
    pub fn mine_sig<F>(sig: &Sig, mut qual_do: F) -> Res<()>
    where
        F: FnMut(Term) -> Res<()>,
    {
        let mut prev: TypMap<VarSet> = TypMap::new();

        let sig = sig.index_iter();

        for (var, typ) in sig {
            if let Some(vars) = prev.get(typ) {
                for v in vars {
                    qual_do(term::eq(
                        term::var(*v, typ.clone()),
                        term::var(var, typ.clone()),
                    ))?
                }
            }

            scoped! {
              prev.entry( typ.clone() ).or_insert_with(VarSet::new).insert(var) ;
            }

            // println!("looking at {}: {}", var.default_str(), typ);

            match **typ {
                typ::RTyp::Int => {
                    qual_do(term::ge(term::var(var, typ.clone()), term::int(0)))?;
                    qual_do(term::le(term::var(var, typ.clone()), term::int(0)))?;
                    qual_do(term::eq(term::var(var, typ.clone()), term::int(0)))?;
                    // quals.insert(
                    //   term::ge( term::var(var, typ.clone()),
                    //   term::int(1) ),
                    //   pred_info.idx
                    // ) ? ;
                    // quals.insert(
                    //   term::le( term::var(var, typ.clone()),
                    //   term::int(1) ),
                    //   pred_info.idx
                    // ) ? ;
                    // quals.insert(
                    //   term::eq( term::var(var, typ.clone()),
                    //   term::int(1) ),
                    //   pred_info.idx
                    // ) ? ;
                }

                typ::RTyp::Real => {
                    qual_do(term::ge(
                        term::var(var, typ.clone()),
                        term::real(Rat::from_integer(0.into())),
                    ))?;
                    qual_do(term::le(
                        term::var(var, typ.clone()),
                        term::real(Rat::from_integer(0.into())),
                    ))?;
                    qual_do(term::eq(
                        term::var(var, typ.clone()),
                        term::real(Rat::from_integer(0.into())),
                    ))?;
                    // quals.insert(
                    //   term::ge(
                    //     term::var(var, typ.clone()),
                    //     term::real(Rat::from_integer(1.into()))
                    //   ),
                    //   pred_info.idx
                    // ) ? ;
                    // quals.insert(
                    //   term::le(
                    //     term::var(var, typ.clone()),
                    //     term::real(Rat::from_integer(1.into()))
                    //   ),
                    //   pred_info.idx
                    // ) ? ;
                    // quals.insert(
                    //   term::eq(
                    //     term::var(var, typ.clone()),
                    //     term::real(Rat::from_integer(1.into()))
                    //   ),
                    //   pred_info.idx
                    // ) ? ;
                }

                typ::RTyp::Bool => {
                    let var = term::bool_var(var);
                    qual_do(var)?
                }

                typ::RTyp::Array { .. } => {
                    qual_do(term::eq(term::var(var, typ.clone()), typ.default_term()))?
                }

                typ::RTyp::DTyp { ref dtyp, .. } => {
                    for name in dtyp.news.keys() {
                        qual_do(term::dtyp_tst(name.clone(), term::var(var, typ.clone())))?
                    }
                    let functions = fun::Functions::new(typ.clone());
                    for fun in functions.from_typ {
                        if fun.typ.is_bool() {
                            qual_do(term::fun(
                                fun.name.clone(),
                                vec![term::var(var, typ.clone())],
                            ))?
                        }
                    }
                }

                typ::RTyp::Unk => bail!("unexpected unknown type"),
            }
        }

        Ok(())
    }

    /// Constructor.
    pub fn new(instance: &Arc<Instance>, mine: bool) -> Res<Self> {
        use rand::SeedableRng;

        let mut quals = PrdMap::with_capacity(instance.preds().len());
        for _ in 0..instance.preds().len() {
            quals.push(VarHMap::new())
        }
        let mut quals = NuQuals {
            quals,
            instance: instance.clone(),
            rng: Rng::from_seed([42; 16]),
        };

        if mine {
            'all_preds: for pred_info in instance.preds() {
                if instance[pred_info.idx].is_defined() {
                    continue 'all_preds;
                }

                // Add companion functions if any.
                // fun::iter(
                //   |fun| {
                //     if fun.synthetic == Some(pred_info.idx) {
                //       let mut args = Vec::with_capacity( pred_info.sig.len() - 1 ) ;
                //       for (var, typ) in pred_info.sig.index_iter().take(
                //         pred_info.sig.len() - 1
                //       ) {
                //         args.push( term::var(var, typ.clone()) )
                //       }
                //       let fun_app = term::fun(
                //         fun.typ.clone(), fun.name.clone(), args
                //       ) ;
                //       let last: VarIdx = (
                //         pred_info.sig.len() - 1
                //       ).into() ;
                //       quals.insert(
                //         term::eq(
                //           term::var( last, fun.typ.clone() ),
                //           fun_app
                //         ),
                //         pred_info.idx
                //       ) ? ;
                //     }
                //     Ok(())
                //   }
                // ) ? ;

                NuQuals::mine_sig(instance[pred_info.idx].sig(), |qual| {
                    quals.insert(qual, pred_info.idx)?;
                    Ok(())
                })?
            }

            mine_instance(instance, &mut quals).chain_err(|| "during qualifier mining")?
        }

        Ok(quals)
    }

    pub fn insert(&mut self, term: Term, pred: PrdIdx) -> Res<bool> {
        let var_count = term::vars(&term).len();
        let set = self.quals[pred]
            .entry(var_count.into())
            .or_insert_with(|| TermSet::with_capacity(103));

        let is_new = set.insert(term);
        Ok(is_new)
    }

    /// Real number of qualifiers considered.
    pub fn real_qual_count(&self) -> usize {
        let mut count = 0;
        for sets in &self.quals {
            for (_, terms) in sets {
                count += terms.len()
            }
        }
        count
    }

    ///
    pub fn wipe(&mut self) -> () {}

    pub fn log(&self) {
        println!("; quals {{");
        for (pred, terms) in self.quals.index_iter() {
            if terms.iter().any(|(_, terms)| !terms.is_empty()) {
                println!(";   {}", conf.emph(&self.instance[pred].name));
                println!(";   {}", self.instance[pred].sig);
                for (_, terms) in terms {
                    for term in terms {
                        println!(";   | {}", term)
                    }
                }
            }
        }
        println!("; }}")
    }

    pub fn quals_of_contains(&self, pred: PrdIdx, term: &Term) -> bool {
        self.quals[pred]
            .iter()
            .any(|(_, terms)| terms.contains(term))
    }

    pub fn quals_of(&self, pred: PrdIdx) -> &VarHMap<TermSet> {
        &self.quals[pred]
    }

    /// Returns the qualifier that maximized the input criterion in a non-zero
    /// fashion, if any. Early-returns if the criterion is `>=` to the gain pivot
    /// defined in the configuration at some point.
    pub fn maximize<Crit>(
        &mut self,
        pred: PrdIdx,
        bias: Option<VarVals>,
        mut crit: Crit,
    ) -> Res<Option<(Term, f64)>>
    where
        Crit: FnMut(&Term) -> Res<Option<f64>>,
    {
        let var_bias = if let Some(sample) = bias {
            let mut set = VarSet::new();
            for (var, val) in sample.index_iter() {
                if val.is_known() {
                    set.insert(var);
                }
            }
            if set.is_empty() {
                bail!("empty bias sample in gain maximization")
            }
            Some(set)
        } else {
            None
        };

        let mut best = None;
        let rng = &mut self.rng;

        let mut quals: Vec<_> = self.quals[pred]
            .iter()
            .filter_map(|(count, terms)| {
                if let Some(var_bias) = var_bias.as_ref() {
                    if var_bias.len() == **count {
                        Some(terms)
                    } else {
                        None
                    }
                } else {
                    Some(terms)
                }
            })
            .collect();

        if conf.ice.rand_quals {
            quals.sort_unstable_by(|_, _| {
                use rand::Rng;
                if 0.5 < rng.gen() {
                    ::std::cmp::Ordering::Greater
                } else {
                    ::std::cmp::Ordering::Less
                }
            })
        }

        for terms in quals {
            // for terms in terms {
            for term in terms {
                if let Some(var_bias) = var_bias.as_ref() {
                    if var_bias != &term::vars(term) {
                        continue;
                    }
                }

                if let Some(value) = crit(term)? {
                    best = if value > 0.9999 {
                        return Ok(Some((term.clone(), value)));
                    } else if let Some((best, best_value)) = best {
                        let diff = value - best_value;
                        if diff > ::std::f64::EPSILON {
                            Some((term, value))
                        } else {
                            Some((best, best_value))
                        }
                    } else {
                        Some((term, value))
                    }
                }
            }
        }

        Ok(best.map(|(t, v)| (t.clone(), v)))
    }
}
