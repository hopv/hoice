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
//! Hence the signature of a qualifier is sorted by the order of apparition of
//! each variable in the qualifier. For instance, say we want to have the
//! following qualifier
//!
//! ```smt
//! (define-fun qual ((v_1 Int) (v_2 Bool) (v_3 Int))
//!   (ite v_2 (= v_3 (+ v_1 7)) (= v_1 0))
//! )
//! ```
//!
//! Then, the signature is re-ordered as `v_2`, `v_3`, `v_1`. The qualifier
//! becomes
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
use instance::info::VarInfo ;



// /// Arguments for qualifiers. Different from predicate arguments.
// #[derive(PartialEq, Eq, Hash)]
// pub struct RQArgs {
//   /// Actual arguments.
//   pub args: VarMap<Val>,
// }
// impl Deref for RQArgs {
//   type Target = VarMap<Val> ;
//   fn deref(& self) -> & VarMap<Val> {
//     & self.args
//   }
// }
/// Hashconsed version of `RQArgs`.
pub type QArgs = HConsed< VarMap<Val> > ;

// /// Type of the `QArgs` factory.
// type Factory = HashConsign<VarMap<Val>> ;


/// Signature of a qualifier.
pub type QSig = VarMap<Typ> ;



/// Contains the sets of `QArgs` on which a qualifier is true/false/unknown.
pub struct EvalCache {
  /// `QArgs` for which the qualifier is true.
  pub tru_set: HConSet<QArgs>,
  /// `QArgs` for which the qualifier is false.
  pub fls_set: HConSet<QArgs>,
  /// `QArgs` fro which the value of the qualifier is unknown.
  pub unk_set: HConSet<QArgs>,
}
impl EvalCache {
  /// Constructor.
  pub fn new(capa: usize) -> Self {
    EvalCache {
      tru_set: HConSet::with_capacity(capa),
      fls_set: HConSet::with_capacity(capa),
      unk_set: HConSet::with_capacity(capa),
    }
  }

  /// Retrieves a value from the cache or updates it.
  pub fn get(& mut self, qual: & Term, args: & QArgs) -> Res< Option<bool> > {
    if self.tru_set.contains(args) {
      Ok( Some(true) )
    } else if self.fls_set.contains(args) {
      Ok( Some(false) )
    } else if self.unk_set.contains(args) {
      Ok( None )
    } else {
      let res = qual.bool_eval( args.get() ) ? ;
      let is_new = match res {
        Some(true) => & mut self.tru_set,
        Some(false) => & mut self.fls_set,
        None => & mut self.unk_set,
      }.insert( args.clone() ) ;
      debug_assert! { is_new }
      Ok(res)
    }
  }
}



/// Type of a signature transformation.
pub type SigTransform = VarMap<VarIdx> ;


/// For a specific qualifier signature, maps a predicate signature to all the
/// predicate var to qualifier var mappings that work type-wise.
pub struct SigTransforms {
  /// Actual map.
  map: HashMap< VarMap<Typ>, Vec<SigTransform> >,
}

impl ::std::ops::Deref for SigTransforms {
  type Target = HashMap< VarMap<Typ>, Vec<VarMap<VarIdx>> > ;
  fn deref(& self) -> & Self::Target {
    & self.map
  }
}

impl SigTransforms {
  /// Constructor.
  pub fn new(
    preds: & PrdMap<::instance::info::PrdInfo>,
    qual_sig: & QSig,
  ) -> Self {
    let mut map = HashMap::with_capacity( preds.len() ) ;
    // The stack is explained below.
    let mut stack = Vec::with_capacity(17) ;
    for info in preds {
      if map.contains_key(& info.sig) { continue }

      let mut res = Vec::with_capacity(103) ;
      let mut p_sig = info.sig.index_iter() ;
      let mut q_sig = qual_sig.iter() ;

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
        if let Some(q_typ) = q_sig.next() {

          // Find a variable in `p_sig` that has this type and is unknown.
          while let Some((idx, p_typ)) = p_sig.next() {
            // If not the right type...
            if p_typ != q_typ
            // ...or already in use...
            || used.contains(& idx) {
              // ...then skip.
              continue
            }

            // Otherwise, memorize current state: only difference is that we
            // discarded everything in `p_sig` until and including `idx`. This
            // is what we will backtrack to later.
            stack.push(
              ( old_q_sig.clone(), map.clone(), used.clone(), p_sig )
            ) ;
            // ...update map...
            map.push(idx) ;
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

          // If we're here it's because there nothing in `p_sig` that works
          // anymore. We discard the current decision level and backtrack.
          continue 'build_maps

        } else {
          // No next type, current mapping is complete. Push and keep going.
          res.push(map)
        }
      }

      if ! res.is_empty() {
        res.shrink_to_fit() ;
        let prev = map.insert( info.sig.clone(), res ) ;
        debug_assert! { prev.is_none() }
      }

    }

    map.shrink_to_fit() ;
    SigTransforms { map }
  }
}


// /// For a specific qualifier signature, maps samples (predicate input values)
// /// to `QArgs`.
// pub struct SampleMap {
//   /// Actual map.
//   map: HConMap< HSample, Option< HConSet<QArgs> > >,
//   /// Signature transformations.
//   transforms: SigTransforms,
// }
// impl SampleMap {
//   /// Constructor.
//   pub fn new(
//     preds: & PrdMap<::instance::info::PrdInfo>, qual_sig: & QSig
//   ) -> Self {
//     let transforms = SigTransforms::new(preds, qual_sig) ;
//     SampleMap {
//       map: HConMap::with_capacity(1001), transforms
//     }
//   }

//   /// Returns the `QArgs` corresponding to a sample, no cache.
//   fn extract(
//     transforms: & SigTransforms, factory: & mut Factory,
//     sample: & HSample, sample_sig: & VarMap<Typ>
//   ) -> Option< HConSet<QArgs> > {
//     if let Some(trans) = transforms.get(sample_sig) {
//       debug_assert! { ! trans.is_empty() }
//       let mut res: HConSet<QArgs> = HConSet::with_capacity( trans.len() ) ;
//       for map in trans {
//         let mut qargs = VarMap::with_capacity( map.len() ) ;
//         for p_idx in map {
//           qargs.push( sample[* p_idx].clone() )
//         }
//         let qargs = factory.mk(qargs) ;
//         res.insert(qargs) ;
//       }
//       Some(res)
//     } else {
//       None
//     }
//   }

//   /// Gets the `QArgs` corresponding to a sample.
//   ///
//   /// The `factory` is required to create `QArgs`.
//   ///
//   /// The `sample_sig` is required to know which `QArgs` to create. It's the
//   /// signature of the predicate the sample comes from.
//   pub fn get<'a>(
//     & mut self, factory: & mut Factory,
//     sample: & HSample, sample_sig: & VarMap<Typ>
//   ) -> Option< & HConSet<QArgs> > {
//     use std::collections::hash_map::Entry ;
//     match self.map.entry( sample.clone() ) {
//       Entry::Occupied(entry) => entry.into_mut().as_ref(),
//       Entry::Vacant(entry) => entry.insert(
//         Self::extract(& self.transforms, factory, sample, sample_sig)
//       ).as_ref(),
//     }
//   }
// }


/// Stores qualifiers that have the same signature.
pub struct QualClass {
  /// Signature transformations.
  transforms: SigTransforms,
  /// Qualifiers: map from terms to `EvalCache`.
  quals: HConMap<Term, EvalCache>,
}

impl QualClass {
  /// Constructor.
  pub fn new(transforms: SigTransforms, qual_capa: usize) -> Self {
    QualClass {
      transforms,
      quals: HConMap::with_capacity(qual_capa)}
  }

  /// Inserts a new term in the class.
  pub fn insert(& mut self, term: Term) -> bool {
    use std::collections::hash_map::Entry ;
    match self.quals.entry(term) {
      Entry::Occupied(_) => false,
      Entry::Vacant(entry) => {
        entry.insert( EvalCache::new(107) ) ;
        true
      },
    }
  }
}



/// Specializes the notion of qualifier defined in this module to a
/// version tailored for one predicate.
///
/// The same qualifier will in general be tailored in different ways for the
/// same predicate.
///
/// This type is in fact a temporary structure created internally by `Quals`
/// for its [`maximize`][quals max] function.
///
/// [quals max]: struct.Quals.html#methods.maximize (Quals' maximize function)
pub struct Qual<'a> {
  qual: & 'a Term,
  // cache: & 'a mut EvalCache,
  map: & 'a VarMap<VarIdx>,
}
impl<'a> Qual<'a> {
  /// Evaluates this qualifier.
  pub fn bool_eval<E>(& mut self, vals: & E) -> Res<Option<bool>>
  where E: term::Evaluator {
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



/// Stores qualifiers and a lot of stuff for (cached) evaluation.
///
/// # TODO
///
/// - `classes` is probably not deterministic right now; fix
pub struct Quals {
  // /// `QArgs` factory.
  // factory: Factory,
  /// Map from **qualifier** signatures to qualifier classes.
  classes: HashMap< VarMap<Typ>, QualClass >,
  /// Arc to the instance.
  instance: Arc<Instance>,
  /// Qualifier blacklist.
  blacklist: HConSet<Term>,
}

impl Quals {
  /// Constructor.
  ///
  /// - `factory_capa`: size of the `QArgs` factory
  /// - `class_capa`: space allocated for qualifier classes `QualClass`
  pub fn new(
    // factory_capa: usize,
    class_capa: usize, instance: Arc<Instance>
  ) -> Self {
    Quals {
      // factory: Factory::with_capacity(factory_capa),
      classes: HashMap::with_capacity(class_capa),
      instance,
      blacklist: HConSet::with_capacity(107),
    }
  }



  /// Returns the qualifier that maximized the input criterion in a non-zero
  /// fashion, if any. Early-returns if the criterion is `1.0` at some point.
  ///
  /// The criterion `Crit` can return some info, and the info of the best
  /// qualifier will be returned.
  pub fn maximize<Info, Crit>(
    & self, pred: PrdIdx, mut crit: Crit
  ) -> Option<(Term, f64, Info)>
  where Crit: for<'a> FnMut( & Qual<'a> ) -> (f64, Info) {
    let sig = & self.instance.preds()[pred].sig ;
    let mut prev = None ;
    for class in self.classes.values() {
      if let Some(maps) = class.transforms.get(sig) {
        let quals = & class.quals ;
        for map in maps {
          for qual in quals.keys() {
            let qual = Qual { qual, map } ;
            let (res, info) = crit(& qual) ;
            if res == 1.0 {
              return Some(
                (qual.to_term(), res, info)
              )
            }
            prev = if let Some((p_term, p_res, p_info)) = prev {
              if p_res < res {
                Some( (qual.to_term(), res, info) )
              } else {
                Some( (p_term, p_res, p_info) )
              }
            } else {
              Some( (qual.to_term(), res, info) )
            }
          }
        }
      }
    }
    prev
  }



  /// Blacklists a qualifier.
  pub fn blacklist(& mut self, qual: & Term) {
    let is_new = self.blacklist.insert( qual.clone() ) ;
    debug_assert! { is_new }
  }
  /// Clears the qualifier blacklist.
  pub fn clear_blacklist(& mut self) {
    self.blacklist.clear()
  }

  /// Inserts a new qualifier.
  pub fn insert(
    & mut self, term: & Term, clause_sig: & VarMap<VarInfo>
  ) -> bool {
    let mut sig = VarMap::with_capacity( clause_sig.len() ) ;
    let mut map = VarHMap::with_capacity( clause_sig.len() ) ;
    let mut stack: Vec<
      ( Op, Vec<Term>, _ )
    > = Vec::with_capacity(7) ;
    let mut curr = term ;

    let term = 'top_loop: loop {

      // Go down.
      let mut to_propagate_upward = match * * curr {

        RTerm::Var(old_idx) => {
          use std::collections::hash_map::Entry ;
          let idx = match map.entry(old_idx) {
            Entry::Occupied(entry) => * entry.get(),
            Entry::Vacant(entry) => {
              let idx = sig.next_index() ;
              entry.insert(idx) ;
              sig.push( clause_sig[old_idx].typ ) ;
              idx
            },
          } ;
          term::var(idx)
        },

        RTerm::Int(_) => curr.clone(),
        RTerm::Bool(_) => curr.clone(),

        RTerm::App { op, ref args } => {
          let mut args_iter = args.iter() ;
          if let Some(next) = args_iter.next() {
            curr = next ;
          } else {
            panic!("empty operator application")
          }
          stack.push( (op, Vec::with_capacity( args.len() ), args_iter) ) ;
          continue 'top_loop
        },

      } ;

      'go_up: loop {
        if let Some( (op, mut lft, mut rgt) ) = stack.pop() {
          lft.push(to_propagate_upward) ;
          if let Some(next) = rgt.next() {
            stack.push( (op, lft, rgt) ) ;
            curr = next ;
            continue 'top_loop
          } else {
            to_propagate_upward = term::app(op, lft)
          }
        } else {
          break 'top_loop to_propagate_upward
        }

      }
    } ;

    sig.shrink_to_fit() ;

    use std::collections::hash_map::Entry ;
    match self.classes.entry(sig) {
      Entry::Occupied(entry) => entry.into_mut().insert(term),
      Entry::Vacant(entry) => {
        let transforms = SigTransforms::new(
          self.instance.preds(), entry.key()
        ) ;
        entry.insert(
          QualClass::new(transforms, 107)
        ).insert(term) ;
        true
      },
    }
  }

}
