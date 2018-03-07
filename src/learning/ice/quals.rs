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

use hashconsing::* ;


use common::* ;


/// Hashconsed version of `RQArgs`.
pub type QArgs = HConsed< VarMap<Val> > ;

/// Signature of a qualifier.
pub type QSig = VarMap<Typ> ;

/// Hash consed signature.
pub type HQSig = HConsed< QSig > ;

/// Type of the predicate signatures factory.
type Factory = HashConsign<VarMap<Typ>> ;




/// Information about a qualifier.
///
/// `preds` contains the predicates the qualifier `q` was created for. That is,
/// the predicate passed when `q` was first inserted, and all the predicates
/// that triggered the same insertion afterwards.
///
/// `is_new` is set to
///
/// - `true` when the qualifier is added and when a new predicate is inserted
///   in `preds`. That is, whenever a call to [`insert`][quals insert]
///   generates this qualifier with a predicate that was not in `preds` yet;
/// - `false` whenever it is passed to the criterion function in
///   [`maximize`][quals max].
///
/// [quals max]: struct.Qualifiers.html#method.maximize
/// (Qualifiers' maximize function)
/// [quals insert]: struct.Qualifiers.html#method.insert
/// (Qualifiers' insert function)
pub struct QInfo {
  /// Indicates whether the qualifier has been evaluated at least once.
  pub is_new: bool,
  /// Predicates the qualifier was created for.
  pub preds: PrdSet,
}
impl QInfo {
  /// Constructor.
  pub fn new(pred: PrdIdx) -> Self {
    let mut preds = PrdSet::with_capacity(3) ;
    preds.insert(pred) ;
    QInfo {
      is_new: true,
      preds,
    }
  }
}



/// Type of a signature transformation.
pub type Transform = VarMap<(VarIdx, Typ)> ;

/// Some transformations, either complete or partial.
///
/// - *complete* means that all possible transformations have been generated,
/// - *partial* means that only specific transformations are considered: the
///   ones given when inserting a term.
///
/// The goal is to avoid the combinatorial blow-up that can happen when
/// generating all transformations.
pub enum Transforms {
  /// Complete, contains all the transformations.
  Complete( Vec<Transform> ),
  /// Partial, on-demand transformations.
  Partial( Vec<Transform> ),
}
impl ::std::ops::Deref for Transforms {
  type Target = Vec<Transform> ;
  fn deref(& self) -> & Self::Target {
    match * self {
      Transforms::Complete(ref vec) => vec,
      Transforms::Partial(ref vec) => vec,
    }
  }
}
impl Transforms {
  /// Inserts a transformation in `Partial`, does nothing on `Complete`.
  pub fn insert(& mut self, transform: Transform) {
    match * self {
      Transforms::Partial(ref mut ts) => if ts.iter().all(
        |t| t != & transform
      ) {
        ts.push(transform)
      },
      Transforms::Complete(_) => (),
    }
  }
}


/// For a specific qualifier signature, maps a predicate signature to all the
/// predicate var to qualifier var mappings that work type-wise.
///
/// The [constructor][new] is where the magic happens.
///
/// [new]: struct.SigTransforms.html#method.new
/// (SigTransforms' constructor)
pub struct SigTransforms {
  /// Actual map.
  ///
  /// Currently never iterated on, so non-determinism is okay.
  pub map: HashMap< VarMap<Typ>, Transforms >,
}

impl ::std::ops::Deref for SigTransforms {
  type Target = HashMap< VarMap<Typ>, Transforms > ;
  fn deref(& self) -> & Self::Target {
    & self.map
  }
}
impl ::std::ops::DerefMut for SigTransforms {
  fn deref_mut(& mut self) -> & mut Self::Target {
    & mut self.map
  }
}

impl SigTransforms {
  /// Checks consistency.
  #[inline]
  #[cfg( not(debug_assertions) )]
  pub fn check(& self) -> Res<()> { Ok(()) }
  #[cfg(debug_assertions)]
  pub fn check(& self) -> Res<()> {
    let mut prev = None ;
    for (sig, transs) in & self.map {
      for trans in transs.iter() {
        if prev.is_none() { prev = Some( trans.len() ) }
        if prev != Some( trans.len() ) {
          bail!(
            "sig transform is inconsistent: \
            non-unique transformation arity"
          )
        }
        for & (idx, _) in trans {
          if * idx >= sig.len() {
            bail!(
              "sig transform is inconsistent: \
              co-domain inconsistent with signature"
            )
          }
        }
      }
    }
    if prev == Some(0) {
      bail!(
        "illegal sig transform: \
        empty transformations"
      )
    }
    Ok(())
  }


  /// Constructor.
  pub fn new(
    preds: & PrdMap<::instance::info::PrdInfo>,
    qual_sig: & QSig,
  ) -> Self {

    let mut map = HashMap::with_capacity( preds.len() ) ;
    // The stack is explained below.
    let mut stack = Vec::with_capacity(17) ;

    let partial = ! conf.ice.complete ; // && qual_sig.len() > 1 ;

    'all_preds: for info in preds {
      // Skip if already known.
      if map.contains_key(& info.sig) { continue }

      macro_rules! partial_and_continue {
        () => ({
          let prev = map.insert(
            info.sig.clone(),
            Transforms::Partial(Vec::with_capacity(7))
          ) ;
          debug_assert! { prev.is_none() }
          continue 'all_preds
        })
      }

      if partial {
        partial_and_continue!()
      }

      let mut res: u64 = 1 ;
      for typ in qual_sig {
        let mut mul = 0 ;
        for t in & info.sig {
          if t == typ { mul += 1 }
        }
        if let Some(r) = res.checked_mul(mul) {
          res = r
        } else {
          partial_and_continue!()
        }
      }

      if res > 100 {
        partial_and_continue!()
      }

      let mut res = Vec::with_capacity(103) ;
      let mut p_sig = info.sig.index_iter() ;
      let mut q_sig = qual_sig.index_iter() ;

      // This is a bit technical.
      stack.push( (
        // We're going to iterate and backtrack on `q_sig` to construct all
        // possible arrangements of variables from `info` that work type-wise.
        q_sig,
        // The map we're currently constructing. Will be cloned when going down
        // (so that we can backtrack later).
        VarMap::with_capacity( qual_sig.len() ),
        // This will store the variables used in the codomain of the map being
        // constructed (previous element of the tuple) so that we can avoid
        // them.
        VarSet::with_capacity( qual_sig.len() ),
        // This is an iterator on the predicate variables that can be
        // considered at the current decision level. Each time we backtrack to
        // this level, we consume it more and more.
        p_sig,
      ) ) ;

      'build_maps: while let Some(
        (mut q_sig, mut map, mut used, mut p_sig)
      ) = stack.pop() {

        // Remember this to memorize current state later.
        let old_q_sig = q_sig.clone() ;

        // What's the next type we want?
        if let Some((_var, q_typ)) = q_sig.next() {
          // println!("  q_{}: {}", var.default_str(), q_typ) ;

          // Find a variable in `p_sig` that has this type and is unknown.
          while let Some((idx, p_typ)) = p_sig.next() {
            // println!("    q_{}: {}", idx.default_str(), p_typ) ;
            // If not the right type...
            if p_typ != q_typ
            // ...or already in use...
            || used.contains(& idx) {
              // ...then skip.
              continue
            }
            // println!("      going down") ;

            // Otherwise, memorize current state: only difference is that we
            // discarded everything in `p_sig` until and including `idx`. This
            // is what we will backtrack to later.
            stack.push(
              ( old_q_sig.clone(), map.clone(), used.clone(), p_sig )
            ) ;
            // ...update map...
            map.push((idx, * p_typ)) ;
            // ...update used predicate variables...
            let is_new = used.insert(idx) ;
            debug_assert! { is_new }
            // ...keep going: work on next type in `q_sig`.
            stack.push(
              ( q_sig, map, used, info.sig.index_iter() )
              // Create a new     ^^^^^^^^^^^^^^^^^^^^^
              // iterator on predicate variables for the new decision level.
            ) ;
            continue 'build_maps
          }

          // println!("    nothing works, go up") ;
          // If we're here it's because there nothing in `p_sig` that works
          // anymore. We discard the current decision level and backtrack.
          continue 'build_maps

        } else {
          // println!("  complete, go up") ;
          // No next type, current mapping is complete. Push and keep going.
          if res.iter().any(
            |m| m == & map
          ) {
            panic!("stuttering")
          }
          res.push(map)
        }
      }

      if ! res.is_empty() {
        res.shrink_to_fit() ;
        let prev = map.insert(
          info.sig.clone(), Transforms::Complete(res)
        ) ;
        debug_assert! { prev.is_none() }
      }

    }

    map.shrink_to_fit() ;
    SigTransforms { map }
  }
}



/// Stores qualifiers that have the same signature.
pub struct QualClass {
  /// Signature transformations.
  pub transforms: SigTransforms,
  /// Qualifiers: map from terms to their info.
  pub quals: HConMap<Term, QInfo>,
}

impl QualClass {
  /// Checks consistency.
  #[inline]
  #[cfg( not(debug_assertions) )]
  pub fn check(& self) -> Res<()> { Ok(()) }
  #[cfg(debug_assertions)]
  pub fn check(& self) -> Res<()> {
    if self.transforms.is_empty() {
      bail!("illegal qual class: no transformations")
    }
    self.transforms.check() ? ;
    for transs in self.transforms.values() {
      for trans in transs.iter() {
        'check_quals: for qual in self.quals.keys() {
          for var in term::vars(qual) {
            if * var >= trans.len() {
              bail!(
                "illegal qual class: \
                qual {} goes above the max variable `v_{}`",
                qual, trans.len() - 1
              )
            }
          }

        }
      }
    }
    Ok(())
  }


  /// Constructor.
  ///
  /// Returns `None` if `transforms.is_empty()`.
  pub fn new(transforms: SigTransforms, qual_capa: usize) -> Option<Self> {
    if transforms.is_empty() {
      None
    } else {
      Some(
        QualClass {
          transforms,
          quals: HConMap::with_capacity(qual_capa)
        }
      )
    }
  }

  /// Inserts a new term in the class.
  ///
  /// Tricky arguments:
  ///
  /// - `pred_sig`: (predicate) signature this new term was extracted from,
  /// - `hint_map`: map from term's variables to predicate's.
  ///
  /// These two arguments are only useful when the transforms for `pred_sig`
  /// are stored in a partial manner ([`SigTransforms::Partial`][partial]). In
  /// this case, `hint_map` is added to the list of partial maps for
  /// `pred_sig`.
  ///
  /// [partial]: enum.Transforms.html#variant.Partial
  /// (SigTransforms' Partial variant)
  pub fn insert(
    & mut self, term: Term, pred: PrdIdx,
    pred_sig: & VarMap<Typ>, hint_map: VarMap<(VarIdx, Typ)>
  ) -> bool {
    use std::collections::hash_map::Entry ;
    if let Some(transforms) = self.transforms.get_mut(pred_sig) {
      transforms.insert(hint_map)
    } else {
      panic!("unknown predicate signature {}", pred_sig)
    }
    if ! self.quals.contains_key( & term::not( term.clone() ) ) {
      match self.quals.entry(term) {
        Entry::Occupied(entry) => {
          let entry = entry.into_mut() ;
          let is_new = entry.preds.insert(pred) ;
          if is_new {
            // Qualifier is new **for this predicate**.
            entry.is_new = true
          }
          // But qualifier is not new in general.
          false
        },
        Entry::Vacant(entry) => {
          entry.insert( QInfo::new(pred) ) ;
          true
        },
      }
    } else {
      false
    }
  }
}



/// Specializes the notion of qualifier defined in this module to a
/// version tailored for one predicate.
///
/// The same qualifier will in general be tailored in different ways for the
/// same predicate.
///
/// This type is in fact a temporary structure created internally by
/// `Qualifiers` for its [`maximize`][quals max] function.
///
/// [quals max]: /learning/ice/quals/struct.Qualifiers.html#method.maximize
/// (Qualifiers' maximize function)
pub struct Qual<'a> {
  /// The qualifier.
  pub qual: & 'a Term,
  // cache: & 'a mut EvalCache,
  /// Maps qualifier variables to predicate variables.
  pub map: & 'a VarMap<(VarIdx, Typ)>,
}
impl<'a> Qual<'a> {
  /// Checks consistency.
  #[inline]
  #[cfg( not(debug_assertions) )]
  pub fn check(& self) -> Res<()> { Ok(()) }
  #[cfg(debug_assertions)]
  pub fn check(& self) -> Res<()> {
    for var in term::vars(self.qual) {
      if * var >= self.map.len() {
        bail!(
          "illegal qualifier: {} goes above max variable `v_{}`",
          self.qual, self.map.len()
        )
      }
    }
    Ok(())
  }

  /// Evaluates this qualifier.
  pub fn bool_eval<E>(& self, vals: & E) -> Res<Option<bool>>
  where E: Evaluator {
    self.qual.bool_eval( & (self.map, vals) )
  }

  /// Extracts the term corresponding to this specialized qualifier.
  pub fn to_term(& self) -> Term {
    if let Some((term, changed)) = self.qual.subst_total(self.map) {
      debug_assert! { changed }
      term
    } else {
      panic!("bug in new qualifier system, could not retrieve term")
    }
  }
}
impl<'a> ::std::fmt::Display for Qual<'a> {
  fn fmt(& self, fmt: & mut ::std::fmt::Formatter) -> ::std::fmt::Result {
    self.qual.fmt(fmt)
  }
}
impl<'a> CanBEvaled for Qual<'a> {
  fn evaluate<E>(& self, args: & E) -> Res< Option<bool> >
  where E: Evaluator {
    self.bool_eval(args)
  }
}



/// Stores qualifiers and a lot of stuff for (cached) evaluation.
pub struct Qualifiers {
  /// Predicate signature factory.
  factory: Factory,
  /// Map from **qualifier** signatures to qualifier classes.
  pub classes: HConMap< HQSig, QualClass >,
  /// Arc to the instance.
  pub instance: Arc<Instance>,
  /// Maps predicate variables to alpha-renamed qualifier variables. Factored
  /// to avoid allocation.
  alpha_map: VarHMap<(VarIdx, Typ)>,
}

impl Qualifiers {
  /// Checks consistency.
  #[inline]
  #[cfg( not(debug_assertions) )]
  pub fn check(& self) -> Res<()> { Ok(()) }
  #[cfg(debug_assertions)]
  pub fn check(& self) -> Res<()> {
    for (sig, class) in self.classes.iter() {
      class.check() ? ;
      for transs in class.transforms.values() {
        for trans in transs.iter() {
          if trans.len() != sig.len() {
            bail!(
              "inconsistent quals: \
              found a transformation of arity {} but \
              qual signature arity is {}", trans.len(), sig.len()
            )
          }
        }
      }
    }
    Ok(())
  }

  /// Constructor.
  pub fn new(
    instance: Arc<Instance>,
    mine: bool,
  ) -> Res<Self> {
    let class_capa = 13 ;
    let mut quals = Qualifiers {
      factory: Factory::with_capacity(17),
      classes: HConMap::with_capacity(class_capa),
      instance: instance.clone(),
      alpha_map: VarHMap::with_capacity(7),
    } ;

    // 'all_preds: for pred_info in instance.preds() {
    //   let (mut int, mut real) = (false, false) ;
    //   for (var, typ) in pred_info.sig.index_iter() {
    //     if int && real { break 'all_preds }

    //     match * typ {
    //       Typ::Int => if ! int {
    //         int = true ;
    //         quals.insert(
    //           & term::ge( term::var(var), term::int(0) ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::ge( term::var(var), term::int(1) ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::le( term::var(var), term::int(0) ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::le( term::var(var), term::int(1) ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::eq( term::var(var), term::int(0) ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::eq( term::var(var), term::int(1) ),
    //           pred_info.idx
    //         ) ? ;
    //       },
    //       Typ::Real => if ! real {
    //         real = true ;
    //         quals.insert(
    //           & term::ge(
    //             term::var(var), term::real(Rat::from_integer(0.into()))
    //           ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::ge(
    //             term::var(var), term::real(Rat::from_integer(1.into()))
    //           ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::le(
    //             term::var(var), term::real(Rat::from_integer(0.into()))
    //           ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::le(
    //             term::var(var), term::real(Rat::from_integer(1.into()))
    //           ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::eq(
    //             term::var(var), term::real(Rat::from_integer(0.into()))
    //           ),
    //           pred_info.idx
    //         ) ? ;
    //         quals.insert(
    //           & term::eq(
    //             term::var(var), term::real(Rat::from_integer(1.into()))
    //           ),
    //           pred_info.idx
    //         ) ? ;
    //       },
    //       Typ::Bool => (),
    //     }
    //   }
    // }

    if mine {
      instance.qualifiers(& mut quals).chain_err(
        || "during qualifier mining"
      ) ?
    }

    quals.check().chain_err( || "after creation" ) ? ;

    Ok(quals)
  }

  /// Forgets all qualifiers.
  pub fn wipe(& mut self) {
    self.classes.clear()
  }


  /// Number of qualifiers.
  pub fn qual_count(& self) -> usize {
    let mut count = 0 ;
    for class in self.classes.values() {
      count += class.quals.len()
    }
    count
  }

  /// Real number of qualifiers considered.
  pub fn real_qual_count(& self) -> usize {
    let mut count = 0 ;
    let mut mul ;
    for class in self.classes.values() {
      mul = 0 ;
      for transforms in class.transforms.values() {
        mul += transforms.len() ;
      }
      count += mul * class.quals.len()
    }
    count
  }



  /// Returns the qualifier that maximized the input criterion in a non-zero
  /// fashion, if any. Early-returns if the criterion is `>=` to the gain pivot
  /// defined in the configuration at some point.
  pub fn maximize<Crit>(
    & mut self, pred: PrdIdx, mut crit: Crit, new_only: bool
  ) -> Res< Option<(Term, f64)> >
  where Crit: FnMut( & mut Qual ) -> Res< Option<f64> > {
    let sig = & self.instance.preds()[pred].sig ;
    let mut prev = None ;
    for class in self.classes.values_mut() {
      if let Some(maps) = class.transforms.get(sig) {
        let quals = & mut class.quals ;
        'all_quals: for (qual, info) in quals.iter_mut() {
          
          if (
            conf.ice.qual_bias && ! info.preds.contains(& pred)
          ) || (
            new_only && ! info.is_new
          ) {
            continue 'all_quals
          }
          info.is_new = false ;

          'all_maps: for map in maps.iter() {
            let qual = & mut Qual { qual, map } ;
            qual.check() ? ;
            // println!("- {}", qual.to_term()) ;
            let res = if let Some(res) = crit(qual) ? {
              res
            } else {
              // println!("  none") ;
              continue 'all_maps
            } ;

            // println!("  {}", res) ;

            if res == 0.0 {
              continue 'all_maps
            } else if res == 1.0 {
              return Ok(
                Some(
                  (qual.to_term(), res)
                )
              )
            }
            prev = if let Some((p_term, p_res)) = prev {
              if p_res < res {
                Some( (qual.to_term(), res) )
              } else {
                Some( (p_term, p_res) )
              }
            } else {
              Some( (qual.to_term(), res) )
            }
          }

        }
      }
    }
    Ok(prev)
  }




  /// Inserts a new qualifier from a term.
  ///
  /// When a qualifier is inserted, it is considered new until it is evaluated
  /// for the first time.
  pub fn insert(
    & mut self, term: & Term, pred: PrdIdx
  ) -> Res<bool> {
    let pred_sig = & self.instance[pred].sig ;
    // This function basically renames the variables that appear in `term` so
    // that their numbering follows the order on their types. That is, in the
    // renamed term, `forall v_i, v_j. ( i < j => typ(v_i) <= typ(v_j) )`.
    //
    // This guarantees that two qualifiers that can have the same signature
    // will have the same signature.

    let mut vars = Vec::with_capacity( pred_sig.len() ) ;
    for var in term::vars( term ) {
      vars.push(var)
    }

    if vars.is_empty() {
      // No variables, don't care about this term.
      return Ok(false)
    }

    vars.sort_unstable_by(
      |v_i, v_j| pred_sig[* v_i].cmp( & pred_sig[* v_j] )
    ) ;

    // This will be used for variable substitution.
    self.alpha_map.clear() ;

    // Signature of the alpha-renamed term.
    let mut sig = VarMap::with_capacity( vars.len() ) ;
    // Map from variables of the alpha-renamed term to variables of `pred_sig`.
    let mut transform = VarMap::with_capacity( vars.len() ) ;

    for var in vars {
      let typ = pred_sig[var] ;
      // Next qualifier variable index...
      let q_var = sig.next_index() ;
      // ...maps to `var`,
      transform.push((var, typ)) ;
      // ...has its type,
      sig.push( pred_sig[var] ) ;
      // ...substitution will change `var` to `q_var`.
      let prev = self.alpha_map.insert(var, (q_var, typ)) ;
      debug_assert_eq! { prev, None }
    }

    debug_assert_eq! { sig.len(), self.alpha_map.len() }
    debug_assert_eq! { sig.len(), transform.len() }

    let term = if let Some((term, _)) = term.subst_total(& self.alpha_map) {
      term
    } else {
      bail!("qualifier total substitution failed")
    } ;

    // Remove term's negation if any.
    let term = if let Some(term) = term.rm_neg() {
      term
    } else {
      term
    } ;

    // Hashcons signature.
    let sig = self.factory.mk(sig) ;

    // Insert in the classes.
    use std::collections::hash_map::Entry ;
    match self.classes.entry(sig) {
      Entry::Occupied(entry) => Ok(
        entry.into_mut().insert(
          term, pred, pred_sig, transform
        )
      ),
      Entry::Vacant(entry) => {
        let transforms = SigTransforms::new(
          self.instance.preds(), entry.key()
        ) ;

        if let Some(class) = QualClass::new(transforms, 107) {
          Ok(
            entry.insert(class).insert(
              term, pred, pred_sig, transform
            )
          )
        } else {
          Ok(false)
        }
      },
    }
  }

  /// Logs itself regardless of the verbosity level.
  pub fn log(& self) {
    let pref = "; " ;
    println!("{}quals {{", pref) ;
    for (sig, class) in & self.classes {
      let mut s = String::new() ;
      for (var, typ) in sig.index_iter() {
        s.push_str(& format!(" ({} {})", var.default_str(), typ))
      }
      println!("{}  sig{} {{", pref, s) ;
      s.clear() ;
      println!("{}    transforms {{", pref) ;
      for (sig, transs) in class.transforms.iter() {
        for (var, typ) in sig.index_iter() {
          s.push_str( & format!(" ({} {})", var.default_str(), typ) ) ;
        }
        println!("{}      for {}", pref, s) ;
        s.clear() ;
        for trans in transs.iter() {
          for (var, & (v, t)) in trans.index_iter() {
            s.push_str(
              & format!(
                " {}: {} -> {},", v.default_str(), t, var.default_str()
              )
            )
          }
          println!("{}      |{}", pref, s) ;
          s.clear()
        }
      }
      println!("{}    }}", pref) ;
      for (quals, cache) in class.quals.iter() {
        println!("{}    {} ({})", pref, quals, cache.is_new) ;
        print!(  "{}    ->", pref) ;
        for pred in & cache.preds {
          print!(" {},", self.instance[* pred])
        }
        println!("")
      }
      println!("{}  }}", pref)
    }
    println!("{}}}", pref)
  }

}

