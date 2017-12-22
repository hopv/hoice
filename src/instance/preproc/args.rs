//! Helpers to discover useless arguments of predicates.

use common::* ;


/// A reduction maps predicates to the variables that can be safely ignored.
pub type Reduction = PrdHMap<VarSet> ;


/// Dependencies between predicate variables and predicate variables to keep.
pub struct Cxt {
  /// Dependencies between predicate variables.
  dep: Vec< PrdHMap<VarSet> >,
  /// Maps predicate variables to the index of their dependency class.
  ped: PrdMap< VarHMap<usize> >,
  /// Predicate variables that **cannot** be ignored.
  keep: PrdHMap<VarSet>,
  /// Map from **clause** variables to predicate variables.
  ///
  /// Cleared by [`commit`](#method.commit).
  cvar_to_pvar: VarHMap< PrdHMap<VarSet> >,
  /// Clause variables appearing in the clause's terms.
  ///
  /// Cleared by [`commit`](#method.commit).
  term_vars: VarSet,
}
impl Cxt {
  /// Constructor.
  pub fn new(instance: & Instance) -> Self {
    let pred_count = instance.active_pred_count() ;
    let dep = Vec::new() ;
    let mut ped = PrdMap::with_capacity( pred_count ) ;
    for info in instance.preds() {
      ped.push( VarHMap::with_capacity( info.sig.len() ) )
    }
    let keep = PrdHMap::with_capacity(pred_count) ;
    let cvar_to_pvar = VarHMap::new() ;
    let term_vars = VarSet::new() ;
    Cxt { dep, ped, keep, cvar_to_pvar, term_vars }
  }

  /// Log-debugs cvar_to_pvar.
  pub fn log_debug_internal(
    & self, instance: & Instance,
    clause: & ::instance::instance::Clause, pref: & str
  ) {
    if_debug! {
      macro_rules! logd {
        ($s:expr) => ( logd! { $s, } ) ;
        ($s:expr, $($tt:tt)*) => (
          log_debug! { $s, pref, $($tt)* }
        ) ;
      }
      logd! { "{}cvar_to_pvar {{" }
      for (cvar, map) in & self.cvar_to_pvar {
        logd! { "{}  {} {{", clause.vars[* cvar] }
        for (pred, vars) in map {
          let mut s = String::new() ;
          for var in vars {
            s.push_str( & format!(" {}", var.default_str()) )
          }
          logd! { "{}    {}:{}", instance[* pred], s }
        }
        logd! { "{}  }}" }
      }
      logd! { "{}}}" }
    }
  }

  /// Log-debugs the context.
  pub fn log_debug(& self, instance: & Instance, pref: & str) {
    if_debug! {
      macro_rules! logd {
        ($s:expr) => ( logd! { $s, } ) ;
        ($s:expr, $($tt:tt)*) => (
          log_debug! { $s, pref, $($tt)* }
        ) ;
      }
      logd! { "{}dep {{" }
      for class in & self.dep {
        logd! { "{}  {{" }
        for (pred, vars) in class {
          let mut s = String::new() ;
          for var in vars {
            s.push_str( & format!(" {}", var.default_str()) )
          }
          logd! { "{}    {}:{}", instance[* pred], s }
        }
        logd! { "{}  }}" }
      }
      logd! { "{}}}" }
      logd! { "{}to_keep {{" }
      for (pred, vars) in & self.keep {
        let mut s = String::new() ;
        for var in vars {
          s.push_str( & format!(" {}", var.default_str()) )
        }
        logd! { "{} {}:{}", instance[* pred], s }
      }
      logd! { "{}}}" }
    }
  }

  /// Checks the context is legal (only active in debug).
  #[cfg(debug_assertions)]
  pub fn check(& self, instance: & Instance) -> Res<()> {
    macro_rules! fail {
      ($blah:expr) => (
        bail!("inconsistent predicate argument context state ({})...", $blah)
      ) ;
    }

    for class in & self.dep {
      for (pred, vars) in class {
        for var in vars {
          if * var >= instance[* pred].sig.len() {
            bail!(
              "inconsistent `dep` in argument reduction\n\
              predicate {} has no var {}",
              instance[* pred], var.default_str()
            )
          }
        }
      }
    }
    for (pred, vars) in & self.keep {
      for var in vars {
        if * var >= instance[* pred].sig.len() {
          bail!(
            "inconsistent `keep` in argument reduction\n\
            predicate {} has no var {}", instance[* pred], var.default_str()
          )
        }
      }
    }

    let mut index = 0 ;
    while index < self.dep.len() {
      for (pred, vars) in & self.dep[index] {
        for var in vars {
          if self.ped[* pred].get(& var) != Some(& index) {
            fail!("dep -> ped")
          }
          let mut inner_index = index + 1 ;
          while inner_index < self.dep.len() {
            if self.dep[inner_index].get(pred).map(
              |vars| vars.contains(var)
            ).unwrap_or(false) {
              fail!("dep")
            }
            inner_index += 1
          }
        }
      }
      index += 1
    }

    for (pred, var_map) in self.ped.index_iter() {
      for (var, index) in var_map {
        if ! self.dep[* index].get(& pred).map(
          |vars| vars.contains(var)
        ).unwrap_or(false) {
          fail!("ped -> dep")
        }
      }
    }
    Ok(())
  }
  #[cfg( not(debug_assertions) )]
  #[inline(always)]
  pub fn check(& self, _instance: & Instance) -> Res<()> { Ok(()) }

  /// Adds clause term variables.
  pub fn term_vars(& mut self, vars: VarSet) {
    use std::iter::Extend ;
    self.term_vars.extend( vars )
  }

  /// Adds a link between some clause variables and a predicate variable.
  ///
  /// Returns the new length of the set of `pred`'s variables that are related
  /// to `cvar`. (This is usefull to check if more than one of `pred`'s
  /// variables are related to `cvar`.)
  pub fn cvar_to_pvar(
    & mut self, cvar: VarIdx, pred: PrdIdx, var: VarIdx
  ) -> usize {
    let pred_var_set = self.cvar_to_pvar.entry(cvar).or_insert_with(
      || PrdHMap::new()
    ).entry(pred).or_insert_with(
      || VarSet::new()
    ) ;
    pred_var_set.insert(var) ;
    pred_var_set.len()
  }

  /// Registers a predicate variable to keep.
  pub fn keep(& mut self, pred: PrdIdx, var: VarIdx) {
    self.keep.entry(pred).or_insert_with(
      || VarSet::new()
    ).insert(var) ;
  }

  /// Registers a predicate application.
  pub fn pred_app(& mut self, pred: PrdIdx, args: & VarMap<Term>) {
    for (pvar, term) in args.index_iter() {
      // println!("{} -> {}", pvar, term) ;
      match ** term {
        RTerm::Var(var) => {
          if self.term_vars.contains(& var) {
            // println!("keeping {} {}", pred, var) ;
            self.keep(pred, pvar)
          }
          let pred_vars_count = self.cvar_to_pvar(var, pred, pvar) ;
          if pred_vars_count > 1 {
            self.keep(pred, pvar)
          }
        },
        _ => {
          // println!("keeping {} {}", pred, pvar) ;
          self.keep(pred, pvar) ;
          for var in term::vars(term) {
            self.cvar_to_pvar(var, pred, pvar) ;
          }
        },
      }
    }
  }

  /// Registers a predicate application, RHS version.
  pub fn rhs_pred_app(& mut self, pred: PrdIdx, args: & VarMap<Term>) {
    for (pvar, term) in args.index_iter() {
      for cvar in term::vars(term) {
        self.cvar_to_pvar(cvar, pred, pvar) ;
      }
    }
  }

  /// Commits the information on a clause.
  pub fn commit(& mut self) {
    for cvar in self.term_vars.drain() {
      if let Some(map) = self.cvar_to_pvar.get(& cvar) {
        for (pred, vars) in map {
          // println!("keeping {} {}", pred, var) ;
          self.keep.entry(* pred).or_insert_with(
            || VarSet::with_capacity( vars.len() )
          ).extend(vars) ;
        }
      }
    }

    for (_, pvars) in self.cvar_to_pvar.drain() {
      if pvars.len() < 2 {
        for (_, vars) in & pvars {
          if vars.len() < 2 { continue }
        }
      }

      // Retrieve all `dep` indices and merge them.
      let mut indices = None ;
      for (pred, vars) in & pvars {
        for var in vars {
          if let Some(index) = self.ped[* pred].get(var) {
            indices.get_or_insert_with( || HashSet::new() ).insert(* index) ;
          }
        }
      }

      if let Some(indices) = indices {
        debug_assert! { ! indices.is_empty() }
        let mut indices: Vec<_> = indices.into_iter().collect() ;
        indices.sort_unstable() ;
        let merging_to = indices[0] ;

        while let Some(index) = indices.pop() {
          // We're merging into the first element, skip it.
          if indices.is_empty() { break }

          for (pred, vars) in self.dep.swap_remove(index) {
            for var in & vars {
              let prev = self.ped[pred].insert(* var, merging_to) ;
              debug_assert_eq! { prev, Some(index) }
            }
            self.dep[merging_to].entry(pred).or_insert_with(
              || VarSet::with_capacity( vars.len() )
            ).extend(vars) ;
          }

          if index < self.dep.len() {
            for (pred, vars) in & self.dep[index] {
              for var in vars {
                let prev = self.ped[* pred].insert(* var, index) ;
                debug_assert_eq! { prev, Some(self.dep.len()) }
              }
            }
          }
        }

        for (pred, vars) in pvars {
          for var in vars {
            if let Some(index) = self.ped[pred].get(& var).cloned() {
              debug_assert_eq! { index, merging_to }
            } else {
              let is_new = self.dep[merging_to].entry(pred).or_insert_with(
                || VarSet::new()
              ).insert(var) ;
              debug_assert! { is_new }
              let prev = self.ped[pred].insert(var, merging_to) ;
              debug_assert! { prev.is_none() }
            }
          }
        }

      } else {
        let index = self.dep.len() ;
        for (pred, vars) in & pvars {
          for var in vars {
            let prev = self.ped[* pred].insert(* var, index) ;
            debug_assert! { prev.is_none() }
          }
        }
        self.dep.push(pvars)
      }
    }
  }

  /// Destroys the context and returns the predicate variables to keep.
  pub fn extract(mut self, instance: & Instance) -> PrdHMap<VarSet> {
    log_debug! { "  extract..." }
    let mut keep = HashSet::new() ;
    let mut res = PrdHMap::with_capacity( self.keep.len() ) ;
    for (pred, vars) in self.keep {
      for var in vars {
        if let Some(index) = self.ped[pred].remove(& var) {
          keep.insert(index) ;
        } else {
          res.entry(pred).or_insert_with(
            || VarSet::new()
          ).insert(var) ;
        }
      }
    }
    for index in keep {
      for (pred, vars) in self.dep[index].drain() {
        if_debug! {
          let mut s = String::new() ;
          for var in & vars {
            s.push_str( & format!(" {}", var.default_str()) )
          }
          log_debug! { "    keeping {}:{}", instance[pred], s }
        }
        res.entry(pred).or_insert_with(
          || VarSet::new()
        ).extend(vars)
      }
    }
    for pred in instance.pred_indices() {
      if instance.is_known(pred) || res.contains_key(& pred) { continue }
      let prev = res.insert(pred, VarSet::new()) ;
      debug_assert!( prev.is_none() )
    }

    if_debug! {
      log_debug! { "  extraction result {{" }
      for (pred, vars) in & res {
        let mut s = String::new() ;
        for var in vars {
          s.push_str(" ") ;
          s.push_str( & var.default_str() )
        }
        log_debug! { "    {}:{}", instance[* pred], s }
      }
      log_debug! { "  }}" }
    }

    res
  }
}


/// Returns the predicate variables to keep.
///
/// If a predicate is not in the resulting map, it means this predicate is
/// already forced and thus should not be touched.
pub fn to_keep(
  instance: & Instance
) -> Res< PrdHMap<VarSet> > {
  // Dependencies between predicate variables.
  let mut cxt = Cxt::new(instance) ;

  // Iterate over all clauses
  //
  // - find links between predicate arguments and terms (keep)
  // - find links between predicate arguments (dep)
  'all_clauses: for clause in instance.clauses() {
    cxt.check(instance) ? ;

    log_debug! {
      "    working on clause {}", clause.to_string_info(
        instance.preds()
      ).unwrap()
    }

    // All the variables appearing in the lhs's terms are off limits.
    for term in clause.lhs_terms() {
      cxt.term_vars( term::vars(term) )
    }
    cxt.check(instance) ? ;

    // Scan all predicate applications.
    for (pred, argss) in clause.lhs_preds() {
      for args in argss {
        cxt.pred_app(* pred, args)
      }
    }
    cxt.check(instance) ? ;

    if let Some((pred, args)) = clause.rhs() {
      cxt.rhs_pred_app(pred, args)
    }
    cxt.check(instance) ? ;

    cxt.log_debug_internal(instance, clause, "    ") ;

    cxt.commit() ;

    cxt.log_debug(instance, "    ")
  }

  // println!("dependencies:") ;
  // for set in & cxt.dep {
  //   print!("-") ;
  //   for & (pred, var) in set {
  //     print!(" {}[{}],", instance[pred], var)
  //   }
  //   println!("")
  // }
  // println!("keep:") ;
  // for (pred, vars) in & cxt.keep {
  //   print!("- {} ", instance[* pred]) ;
  //   for var in vars {
  //     print!("{},", var)
  //   }
  //   println!("")
  // }
  // println!("") ;

  Ok( cxt.extract(instance) )

}
