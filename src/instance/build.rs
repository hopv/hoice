//! Instance builder.
//!
//! # TODO
//!
//! - investigate further the `unused variable` warnings in the parsers

use nom::multispace ;

use common::* ;
use instance::* ;

/// Instance builder.
pub struct InstBuild {
  /// The instance under construction.
  instance: Instance,
}
impl InstBuild {
  /// Creates an instance builder.
  pub fn mk() -> Self {
    InstBuild { instance: Instance::mk(3_000, 42, 42) }
  }

  /// Internal instance.
  pub fn instance(& mut self) -> & mut Instance {
    & mut self.instance
  }

  /// Detects predicates that can only be tautologies given the clauses.
  ///
  /// Returns the number of tautologies detected.
  pub fn simplify_tautologies(& mut self) -> Res<usize> {
    // Look for trivial predicates: those appearing in clauses of the form
    // `true => P(v_1, v_2, ...)` where all `v_i`s are different.
    let mut res = 0 ;
    let mut cls_idx = ClsIdx::zero() ;
    'trivial_preds: while cls_idx < self.instance.clauses().next_index() {
      let maybe_pred = if self.instance.clauses()[cls_idx].lhs().is_empty() {
        if let TTerm::P {
          pred, ref args
        } = * self.instance.clauses()[cls_idx].rhs() {
          // rhs is a predicate application...
          let mut vars = VarSet::with_capacity(args.len()) ;
          let mut okay = true ;
          for term in args {
            let arg_okay = if let Some(idx) = term.var_idx() {
              let is_new = vars.insert(idx) ;
              is_new
            } else {
              // Not a variable.
              false
            } ;
            okay = okay && arg_okay
          }
          if okay {
            Some(pred)
          } else {
            None
          }
        } else { None }
      } else { None } ;
      if let Some(pred) = maybe_pred {
        res += 1 ;
        let term = self.instance.bool(true) ;
        log_info!{
          "trivial predicate {}: forcing to {}", self.instance[pred], term
        }
        self.instance.force_pred(pred, term) ? ;
        let _clause = self.instance.forget_clause(cls_idx) ;
        log_info!{
          "dropped associated clause {}",
          _clause.string_do( & self.instance.preds, |s| s.to_string() ) ?
        }
      } else {
        cls_idx.inc()
      }
    }
    Ok(res)
  }


  /// Goes through the clauses and replaces forced predicates with their term.
  ///
  /// Returns the number of propagations: predicates replaced + clauses
  /// dropped.
  ///
  /// Only works with predicates that are `true` for now.
  pub fn propagate_forced(& mut self) -> Res<usize> {
    let mut res = 0 ;
    let mut cls_idx = ClsIdx::zero() ;

    'clause_iter: while cls_idx < self.instance.clauses().next_index() {

      // If `rhs` is true, remove clause.
      if let TTerm::P { pred, .. }  = self.instance.clauses[cls_idx].rhs {
        match self.instance.preds_term[pred].as_ref().map(
          |t| t.is_true()
        ) {
          Some(true) => {
            res += 1 ;
            let _clause = self.instance.forget_clause(cls_idx) ;
            log_info!{
              "dropping clause {}, rhs is true",
              _clause.string_do( & self.instance.preds, |s| s.to_string() ) ?
            }
            continue 'clause_iter
          },
          Some(false) => bail!(
            "progation for terms that are not `true` is not implemented"
          ),
          _ => (),
        }
      }

      let clause = & mut self.instance.clauses[cls_idx] ;
      let mut cnt = 0 ;
      'lhs_iter: while cnt < clause.lhs.len() {
        if let TTerm::P { pred, .. } = clause.lhs[cnt] {
          match self.instance.preds_term[pred].as_ref().map(
            |t| t.is_true()
          ) {
            Some(true) => {
              let _ = clause.lhs.swap_remove(cnt) ;
              res += 1 ;
              continue 'lhs_iter
            },
            Some(false) => bail!(
              "progation for terms that are not `true` is not implemented"
            ),
            None => (),
          }
        }
        cnt += 1
      }

      cls_idx.inc()
    }

    Ok(res)
  }

  /// Predicate accessor.
  pub fn preds(& self) -> & PrdMap<PrdInfo> {
    self.instance.preds()
  }
  /// Clause accessor.
  pub fn clauses(& self) -> & ClsMap<Clause> {
    self.instance.clauses()
  }



  // /// Reduces the instance.
  // pub fn reduce(& mut self) -> Res<()> {
  //   Ok(())
  // }

  /// Destructs the builder and yields the instance.
  ///
  /// The weird `line` argument works as follows: if it is
  ///
  /// - `None`, then the data generated will have no line info (useful when
  ///   reading from `stdin`) ;
  /// - `Some(off)`, then the data will have a line info which is the line 
  ///   where the error token appears in `input` plus `off` (useful when
  ///   reading a file incrementally to add an offset to error messages). 
  pub fn to_instance(
    mut self // , input: & [u8], line: Option<usize>
  ) -> Res<Instance> {
    'simplify: loop {
      let _tautologies = self.simplify_tautologies() ? ;
      log_info!{ "{} predicates found to be tautologies", _tautologies }
      let propagations = self.propagate_forced() ? ;
      if propagations == 0 {
        log_info!{ "done simplifying\n" }
        break 'simplify
      } else {
        log_info!{ "{} propagations\n", propagations }
      }
    }

    // if self.errors.is_empty() {
      self.instance.shrink_to_fit() ;
      Ok(self.instance)
    // } else {
    //   Err( self.to_error(input, line) )
    // }
  }
}


named!{
  #[doc = "Comment parser."],
  pub cmt, re_bytes_find!(r#"^;.*[\n\r]*"#)
}

named!{
  #[doc = "Parses comments and spaces."],
  pub spc_cmt<()>, map!(
    many0!( alt_complete!(cmt | multispace) ), |_| ()
  )
}

named!{
  #[doc = "Integer parser."],
  pub int<Int>, map!(
    re_bytes_find!("^([1-9][0-9]*|0)"),
    |bytes| Int::parse_bytes(bytes, 10).expect(
      "[bug] problem in integer parsing"
    )
  )
}