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

use common::* ;
use instance::Clause ;



/// Extracts qualifier-related information from a predicate application.
fn qual_info_of(
  eq_quals: & mut VarHMap<Term>, quals: & mut NuQuals,
  pred: PrdIdx, args: & VarTerms,
) -> Res< (PrdIdx, VarHMap<Term>, TermSet) > {
  debug_assert!( eq_quals.is_empty() ) ;

  // Qualifiers generated while looking at predicate applications.
  let mut app_quals: TermSet = TermSet::with_capacity(17) ;

  // All the *clause var* to *pred var* maps for this predicate application.
  let mut map: VarHMap<Term> = VarHMap::with_capacity( args.len() ) ;

  for (pred_var, term) in args.index_iter() {
    let pred_var_typ = term.typ() ;

    // Parameter's a variable?
    if let Some(clause_var_index) = term.var_idx() {

      // Clause variable's already known as parameter?
      if let Some(other_pred_var) = map.get(
        & clause_var_index
      ).cloned() {
        // Equality qualifier.
        app_quals.insert(
          term::eq(
            term::var(pred_var, pred_var_typ), other_pred_var.clone()
          )
        ) ;
      } else {
        // Add to map.
        let _prev = map.insert(
          clause_var_index, term::var(pred_var, pred_var_typ)
        ) ;
        debug_assert!( _prev.is_none() )
      }

    } else {

      // Parameter's not a variable, store potential equality.
      let _prev = eq_quals.insert( pred_var, term.clone() ) ;
      debug_assert!( _prev.is_none() ) ;

      // Try to revert the term.
      if let Some((var, term)) = term.invert_var(
        pred_var, pred_var_typ
      ) {
        if ! map.contains_key(& var) {
          map.insert(var, term) ;
        } else if let Some(other_pred_var) = map.get(& var) {
          app_quals.insert(
            term::eq( other_pred_var.clone(), term )
          ) ;
        }
      }

    }

  }

  for (pred_var, term) in eq_quals.drain() {
    if let Some((term, _)) = term.subst_total(& map) {
      app_quals.insert(
        term::eq(
          term::var( pred_var, term.typ() ), term
        )
      ) ;
    }
  }

  if ! app_quals.is_empty() {
    let build_conj = app_quals.len() > 1 ;
    let mut conj = Vec::with_capacity( app_quals.len() ) ;

    for term in & app_quals {
      if build_conj {
        conj.push( term.clone() )
      }
      quals.insert(term.clone(), pred) ? ;
    }

    if build_conj {
      let term = term::and(conj) ;
      quals.insert(term, pred) ? ;
    }
  }

  Ok( (pred, map, app_quals) )
}





/// Generates qualifiers from two terms.
fn qual_of_terms<F: FnMut(Term) -> Res<()>>(
  mut f: F, term: & Term, othr: & Term
) -> Res<()> {
  macro_rules! mk_terms {
    (
      $( $op:ident, $( $fun:ident($($terms:expr),*) ),* );*
      $(;)*
    ) => ({
      $(
        f(
          term::app(
            $op, vec![
              $( term::$fun( vec![ $($terms.clone()),* ] ) ),*
            ]
          )
        ) ?
      );*
    }) ;
  }

  match (
    term.app_inspect(), othr.app_inspect()
  ) {

    ( Some((op @ Op::Gt, terms)), Some((_, othrs)) ) |
    ( Some((_, othrs)), Some((op @ Op::Gt, terms)) ) |

    ( Some((op @ Op::Ge, terms)), Some((_, othrs)) ) |
    ( Some((_, othrs)), Some((op @ Op::Ge, terms)) ) |

    ( Some((op @ Op::Eql, terms)), Some((Op::Eql, othrs)) ) =>
    if ! terms[0].typ().is_bool() && terms[0].typ() == othrs[0].typ() {
      mk_terms!(
        op, add(terms[0], othrs[0]), add(terms[1], othrs[1]) ;
        op, sub(terms[0], othrs[1]), sub(terms[1], othrs[0]) ;
      )
    },

    _ => (),
  }

  Ok(())
}









/// Qualifier version of a term.
fn qual_of_term(term: & Term, map: & VarHMap<Term>) -> Option<Term> {
  if let Some( (qual, true) ) = term.subst_total(& map) {
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
fn qualifiers_of_clause(
  instance: & Instance, clause: & Clause, quals: & mut NuQuals
) -> Res<()> {
  // if clause.from_unrolling { return Ok(()) }

  let build_conj = instance.clauses().len() < 2000 && conf.ice.mine_conjs ;

  // Variable to term maps, based on the way the predicates are used.
  let mut maps = vec![] ;

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

  apply_mappings(quals, clause, build_conj, maps) ? ;

  Ok(())

}





/// Applies a mapping for some predicate on a clause.
fn apply_mappings(
  quals: & mut NuQuals, clause: & Clause, build_conj: bool,
  maps: Vec<(PrdIdx, VarHMap<Term>, TermSet)>,
) -> Res<()> {
  // Stores the subterms of `lhs_terms`.
  let mut subterms = Vec::with_capacity(7) ;
  // Stores all (sub-)terms.
  let mut all_terms = TermSet::with_capacity(
    clause.lhs_terms().len()
  ) ;
  // Stores all top terms.
  let mut conj = TermSet::with_capacity(
    clause.lhs_terms().len()
  ) ;

  // Look for atoms and try to apply the mappings.
  for (pred, map, app_quals) in maps {
    all_terms.clear() ;
    conj.clear() ;

    for term in clause.lhs_terms() {

      if let Some( (term, true) ) = term.subst_total(& map) {
        all_terms.insert( term.clone() ) ;
        conj.insert( term.clone() ) ;
        let term = if let Some(term) = term.rm_neg() {
          term
        } else { term } ;
        quals.insert(term, pred) ? ;
        ()
      }

      debug_assert!( subterms.is_empty() ) ;
      subterms.push(term) ;

      while let Some(subterm) = subterms.pop() {
        if let Some( (qual, true) ) = subterm.subst_total(& map) {
          all_terms.insert(qual) ;
        }

        match subterm.app_inspect() {
          Some( (Op::Or, terms) ) |
          Some( (Op::And, terms) ) |
          Some( (Op::Not, terms) ) |
          Some( (Op::Impl, terms) ) => for term in terms {
            subterms.push(term) ;
            if let Some(term) = qual_of_term(term, & map) {
              quals.insert(term, pred) ? ;
            }
          },

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
          //   all_terms.insert(qual) ;
          // },

          _ => if let Some( (qual, true) ) = subterm.subst_total(& map) {
            all_terms.insert(qual) ;
          }
        }
      }

    }

    if build_conj {
      quals.insert(
        term::and(
          app_quals.iter().cloned().collect()
        ), pred
      ) ? ;
      if conj.len() > 1 {
        quals.insert(
          term::and( conj.iter().cloned().collect() ), pred
        ) ? ;
        quals.insert(
          term::and( conj.drain().chain(app_quals).collect() ), pred
        ) ? ;
      }
    }

    let mut all_terms = all_terms.iter() ;

    while let Some(term) = all_terms.next() {
      for other in all_terms.clone() {
        qual_of_terms(
          |qual| { quals.insert(qual, pred) ? ; Ok(()) }, term, other
        ) ?
      }
    }

  }

  Ok(())
}






/// Mines the clauses in an instance for qualifiers.
fn mine_instance(instance: & Instance, quals: & mut NuQuals) -> Res<()> {
  // Add boolean qualifiers for all predicate's bool vars.
  for pred in instance.preds() {
    for (var, typ) in pred.sig.index_iter() {
      let mut bool_vars = Vec::new() ;
      if typ.is_bool() {
        let var = term::var( var, typ::bool() ) ;
        quals.insert( var.clone(), pred.idx ) ? ;
        bool_vars.push(var)
      }
      if bool_vars.len() > 1 {
        quals.insert(
          term::and( bool_vars.clone() ), pred.idx
        ) ? ;
        quals.insert(
          term::or(bool_vars), pred.idx
        ) ? ;
      }
    }
  }

  // Mine all clauses.
  for clause in instance.clauses() {
    qualifiers_of_clause(instance, clause, quals) ?
  }

  Ok(())
}









pub struct NuQuals {
  instance: Arc<Instance>,
  quals: PrdMap< VarHMap< TermSet > >,
  rng: Rng,
}
impl NuQuals {
  pub fn new(instance: & Arc<Instance>, mine: bool) -> Res<Self> {
    use rand::SeedableRng ;

    let mut quals = PrdMap::with_capacity( instance.preds().len() ) ;
    for _ in 0 .. instance.preds().len() {
      quals.push( VarHMap::new() )
    }
    let mut quals = NuQuals {
      quals,
      instance: instance.clone(),
      rng: Rng::from_seed( [ 42 ; 16 ] ),
    } ;

    if mine {

      'all_preds: for pred_info in instance.preds() {

        if instance.is_known(pred_info.idx) { continue 'all_preds }

        let mut sig = pred_info.sig.index_iter() ;

        for (var, typ) in sig {

          match ** typ {
            typ::RTyp::Int => {
              quals.insert(
                term::ge( term::var(var, typ.clone()),
                term::int(0) ),
                pred_info.idx
              ) ? ;
              quals.insert(
                term::le( term::var(var, typ.clone()),
                term::int(0) ),
                pred_info.idx
              ) ? ;
              quals.insert(
                term::eq( term::var(var, typ.clone()),
                term::int(0) ),
                pred_info.idx
              ) ? ;
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
            },
            typ::RTyp::Real => {
              quals.insert(
                term::ge(
                  term::var(var, typ.clone()),
                  term::real(Rat::from_integer(0.into()))
                ),
                pred_info.idx
              ) ? ;
              quals.insert(
                term::le(
                  term::var(var, typ.clone()),
                                  term::real(Rat::from_integer(0.into()))
                ),
                pred_info.idx
              ) ? ;
              quals.insert(
                term::eq(
                  term::var(var, typ.clone()),
                  term::real(Rat::from_integer(0.into()))
                ),
                pred_info.idx
              ) ? ;
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
            },
            typ::RTyp::Bool => {
              let var = term::bool_var(var) ;
              quals.insert( var.clone(), pred_info.idx ) ? ;
              quals.insert(var, pred_info.idx) ? ;
            },

            typ::RTyp::Array { .. } => {
              quals.insert(
                term::eq(
                  term::var(var, typ.clone()),
                  typ.default_term()
                ),
                pred_info.idx
              ) ? ;
            },
          }
        }
      }

      mine_instance(instance, & mut quals).chain_err(
        || "during qualifier mining"
      ) ?
    }

    Ok(quals)
  }

  pub fn insert(
    & mut self, term: Term, pred: PrdIdx
  ) -> Res<bool> {
    let var_count = term::vars(& term).len() ;
    let set = self.quals[pred].entry(
      var_count.into()
    ).or_insert_with(
      || TermSet::with_capacity(103)
    ) ;

    let is_new = set.insert(term) ;
    Ok(is_new)
  }


  /// Real number of qualifiers considered.
  pub fn real_qual_count(& self) -> usize {
    let mut count = 0 ;
    for sets in & self.quals {
      for (_, terms) in sets {
        count += terms.len()
      }
    }
    count
  }

  ///
  pub fn wipe(& mut self) -> () {}

  pub fn log(& self) {
    println!("; quals {{") ;
    for (pred, terms) in self.quals.index_iter() {
      if terms.iter().any(
        |(_, terms)| ! terms.is_empty()
      ) {
        println!(";   {}", conf.emph(& self.instance[pred].name)) ;
        println!(";   {}", self.instance[pred].sig) ;
        for (_, terms) in terms {
          for term in terms {
            println!(";   | {}", term)
          }
        }
      }
    }
    println!("; }}")
  }

  pub fn quals_of_contains(& self, pred: PrdIdx, term: & Term) -> bool {
    self.quals[pred].iter().any(
      |(_, terms)| terms.contains(term)
    )
  }


  pub fn quals_of(& self, pred: PrdIdx) -> & VarHMap< TermSet > {
    & self.quals[pred]
  }



  /// Returns the qualifier that maximized the input criterion in a non-zero
  /// fashion, if any. Early-returns if the criterion is `>=` to the gain pivot
  /// defined in the configuration at some point.
  pub fn maximize<Crit>(
    & mut self, pred: PrdIdx, mut crit: Crit
  ) -> Res< Option<(Term, f64)> >
  where Crit: FnMut( & Term ) -> Res< Option<f64> > {
    use rand::Rng ;

    let mut best = None ;
    let rng = & mut self.rng ;

    let mut quals: Vec<_> = self.quals[pred].iter().map(
      |(_, terms)| terms
    ).collect() ;

    if conf.ice.rand_quals {
      quals.sort_unstable_by(
        |_, _| if 0.5 < rng.gen() {
          ::std::cmp::Ordering::Greater
        } else {
          ::std::cmp::Ordering::Less
        }
      )
    }

    for terms in quals {

      // for terms in terms {
      for term in terms {
        if let Some(value) = crit(term) ? {
          best = if value > 0.9999 {
            return Ok( Some((term.clone(), value)) )
          } else if let Some((best, best_value)) = best {
            let diff = value - best_value ;
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

    Ok( best.map(|(t,v)| (t.clone(), v)) )
  }
}
