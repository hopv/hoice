//! Helpers to discover useless arguments of predicates.

use common::* ;


/// A reduction maps predicates to the variables that can be safely ignored.
pub type Reduction = PrdHMap<VarSet> ;



/// Returns some reductions 
pub fn reductions(
  instance: & Instance
) -> Res< PrdHMap<VarSet> > {
  use std::iter::Extend ;
  let mut forbidden = PrdMap::with_capacity( instance.preds().len() ) ;
  for pred in instance.pred_indices() {
    forbidden.push( VarSet::with_capacity( instance[pred].sig.len() ) )
  }

  // In a given clause, for a given predicate, contains all the variables of the input terms of all applications of that predicate, formal parameter-wise.
  let mut var_to_vars = VarMap::with_capacity( * instance.max_pred_arity ) ;
  for _ in 0..( * instance.max_pred_arity - 1 ) {
    var_to_vars.push( VarSet::with_capacity(7) )
  }

  'all_clauses: for (cidx, clause) in instance.clauses().index_iter() {
    if_debug! {

      log_debug! { "  forbidden (1) {{" }
      for (pred, vars) in forbidden.index_iter() {
        log_debug! { "    {}", instance[pred] }
        for var in vars {
          log_debug! { "    -> {}", var.default_str() }
        }
      }
      log_debug! { "  }}" }

      log_debug! { "  looking at clause #{}", cidx }
      log_debug! { "{}", clause.to_string_info( instance.preds() ).unwrap() }

    }
    // Variables appearing in the lhs's terms, and the predicate applications
    // we have seen so far.
    let mut term_vars = VarSet::with_capacity( clause.vars().len() ) ;
    for term in clause.lhs_terms() {
      term_vars.extend( term::vars(term) )
    }

    for set in & mut var_to_vars {
      set.clear()
    }

    let mut pred_apps = clause.lhs_preds().iter() ;

    // Populate `var_to_vars` for this predicate.
    'all_apps: while let Some( (pred, argss) ) = pred_apps.next() {
      let pred = * pred ;
      log_debug! { "    looking at {}", instance[pred] }
      for set in & mut var_to_vars {
        set.clear()
      }

      'all_args: for args in argss {

        'args: for (var, term) in args.index_iter() {
          let these_vars = term::vars(term) ;
          let okay = match ** term {
            RTerm::Var(_) => true,
            _ => false,
          } ;
          var_to_vars[var].extend( & these_vars ) ;

          if forbidden[pred].contains(& var) { continue 'args }

          let okay = okay && these_vars.intersection(
            & term_vars
          ).next().is_none() ;

          if ! okay {
            // At least a variable appears in the lhs's terms, forbidden.
            let is_new = forbidden[pred].insert(var) ;
            debug_assert!(is_new) ;
            continue 'args
          }
        }

      }

      if_debug! {
        log_debug! { "    - var_to_vars {{" }
        for (v, vars) in var_to_vars.index_iter() {
          log_debug! { "      {}", v.default_str() }
          for var in vars {
            log_debug! { "      -> {}", var.default_str() }
          }
        }
        log_debug! { "    }}" }
      }
      log_debug! { "    forbidden (2) {{" }
      for (pred, vars) in forbidden.index_iter() {
        log_debug! { "      {}", instance[pred] }
        for var in vars {
          log_debug! { "      -> {}", var.default_str() }
        }
      }
      log_debug! { "    }}" }

      // Check this predicate's arguments' vars between themselves.
      let mut all_forbidden = true ;
      {
        let mut vvars = var_to_vars.index_iter() ;
        while let Some( (var, vars) ) = vvars.next() {
          let skip = forbidden[pred].contains(& var) ;
          if ! skip
          && vars.intersection( & term_vars ).next().is_some() {
            let is_new = forbidden[pred].insert(var) ;
            debug_assert!( is_new )
          }
          term_vars.extend( vars ) ;
          if ! skip { all_forbidden = false }
        }
      }
      if all_forbidden {
        log_debug! { "    all forbidden" }
        continue 'all_apps
      }
      log_debug! { "    forbidden (3) {{" }
      for (pred, vars) in forbidden.index_iter() {
        log_debug! { "      {}", instance[pred] }
        for var in vars {
          log_debug! { "      -> {}", var.default_str() }
        }
      }
      log_debug! { "    }}" }

      // Check with other predicate applications.
      'other_apps: for (other_pred, other_argss) in pred_apps.clone() {
        let other_pred = * other_pred ;
        if other_pred == pred { continue 'other_apps }
        log_debug! { "    checking with {}", instance[other_pred] }

        'other_all_args: for other_args in other_argss {

          'other_args: for (v, term) in other_args.index_iter() {
            let other_vars = term::vars( term ) ;
            for (var, vars) in var_to_vars.index_iter() {
              if other_vars.intersection( vars ).next().is_some() {
                forbidden[other_pred].insert(v) ;
                forbidden[pred].insert(var) ;
                // Since `v` is forbidden for `other_pred`, might as well add
                // `other_vars` to `term_vars`.
                term_vars.extend( & other_vars )
              }
            }
          }

        }

      }
      log_debug! { "    forbidden (4) {{" }
      for (pred, vars) in forbidden.index_iter() {
        log_debug! { "      {}", instance[pred] }
        for var in vars {
          log_debug! { "      -> {}", var.default_str() }
        }
      }
      log_debug! { "    }}" }

      // Check with RHS.
      if let Some((other_pred, other_args)) = clause.rhs() {
        if pred == other_pred {
          for (var, vars) in var_to_vars.index_iter() {
            if forbidden[pred].contains(& var) { continue }
            for (v, term) in other_args.index_iter() {
              if v == var { continue }
              let t_vars = term::vars(term) ;
              if term_vars.intersection( vars ).next().is_some() {
                forbidden[pred].insert( var ) ;
                forbidden[pred].insert( v ) ;
                term_vars.extend( & t_vars )
              }
            }
          }
        } else {
          for (v, term) in other_args.index_iter() {
            let other_vars = term::vars( term ) ;
            for (var, vars) in var_to_vars.index_iter() {
              if other_vars.intersection( vars ).next().is_some() {
                log_debug! { "    forbidding {}", var.default_str() }
                for var in vars {
                  log_debug! { "    -> {}", var.default_str() }
                }
                log_debug! {
                  "    and {} for {}", v.default_str(), instance[other_pred]
                }
                forbidden[other_pred].insert(v) ;
                forbidden[pred].insert(var) ;
                // Since `v` is forbidden for `other_pred`, might as well add
                // `other_vars` to `term_vars`.
                term_vars.extend( & other_vars )
              }
            }

          }
        }
      }

    }

  }

  let mut res = PrdHMap::with_capacity( instance.preds().len() ) ;

  for (pred, vars) in forbidden.index_iter() {
    for var in VarRange::zero_to( instance[pred].sig.len() ) {
      if ! vars.contains(& var) {
        let is_new = res.entry(pred).or_insert_with(
          || VarSet::new()
        ).insert(var) ;
        debug_assert!( is_new )
      }
    }
  }

  Ok(res)
}