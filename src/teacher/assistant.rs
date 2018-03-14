//! Handles example propagation.

use rsmt2::to_smt::Expr2Smt ;

use common::* ;
use common::data::{ Data, Sample } ;


/// Propagates examples, tries to break implication constraints.
pub struct Assistant {
  /// Core, to communicate with the teacher.
  // core: & 'a MsgCore,
  /// Solver.
  solver: Solver<()>,
  /// Instance.
  instance: Arc<Instance>,
  /// Positive constraints.
  pos: PrdHMap< ClsSet >,
  /// Negative constraints.
  neg: PrdHMap< ClsSet >,
  /// Profiler.
  _profiler: Profiler,
}

impl Assistant {

  /// Constructor.
  pub fn new(
    instance: Arc<Instance>, // core: & 'a MsgCore
  ) -> Res<Self> {
    let solver = conf.solver.spawn("assistant", ()) ? ;
    let _profiler = Profiler::new() ;

    let mut pos = PrdHMap::with_capacity( instance.preds().len() ) ;
    let mut neg = PrdHMap::with_capacity( instance.preds().len() ) ;

    let mut pos_clauses = ClsSet::new() ;
    let mut neg_clauses = ClsSet::new() ;

    macro_rules! add_clauses {
      ($pred:expr) => ({
        if ! pos_clauses.is_empty() {
          let mut clause_set = ClsSet::new() ;
          ::std::mem::swap( & mut pos_clauses, & mut clause_set ) ;
          let prev = pos.insert($pred, clause_set) ;
          debug_assert! { prev.is_none() }
        }
        if ! neg_clauses.is_empty() {
          let mut clause_set = ClsSet::new() ;
          ::std::mem::swap( & mut neg_clauses, & mut clause_set ) ;
          let prev = neg.insert($pred, clause_set) ;
          debug_assert! { prev.is_none() }
        }
      }) ;
    }

    for pred in instance.pred_indices() {
      debug_assert! { pos_clauses.is_empty() }
      debug_assert! { neg_clauses.is_empty() }

      for clause in instance.clauses_of(pred).1 {
        let clause = * clause ;
        if instance[clause].lhs_preds().is_empty() {
          let is_new = pos_clauses.insert(clause) ;
          debug_assert! { is_new }
        }
      }

      for clause in instance.clauses_of(pred).0 {
        let clause = * clause ;
        if instance[clause].rhs().is_none()
        && instance[clause].lhs_pred_apps_len() == 1 {
          let is_new = neg_clauses.insert(clause) ;
          debug_assert! { is_new }
        }
      }

      add_clauses!(pred)
    }

    Ok(
      Assistant {
        // core,
        solver, instance, pos, neg, _profiler
      }
    )
  }

  /// Destroys the assistant.
  pub fn finalize(mut self) -> Res<Profiler> {
    self.solver.kill().chain_err(
      || "While killing solver"
    ) ? ;
    Ok(self._profiler)
  }

  /// Breaks implications.
  pub fn break_implications(
    & mut self, data: & mut Data
  ) -> Res<()> {
    if data.constraints.is_empty() { return Ok(()) }

    let (mut pos, mut neg) = ( Vec::new(), Vec::new() ) ;
    // msg! { debug self.core => "breaking implications..." }
    profile! { self "constraints received" => add data.constraints.len() }

    'all_constraints: for cstr in CstrRange::zero_to(
      data.constraints.len()
    ) {

      // Can happen because of simplifications when propagating.
      if cstr > data.constraints.len() {
        break
      }
      if data.constraints[cstr].is_tautology() {
        continue
      }

      // debug! {
      //   "  {}", data.constraints[cstr].string_do(
      //     self.instance.preds(), |s| s.to_string()
      //   ).unwrap()
      // }

      let mut trivial = false ;
      let mut rhs_false = false ;
      let mut lhs_unknown = 0 ;
      macro_rules! move_on {
        (if trivial) => ( if trivial { move_on!() } ) ;
        () => ({
          if trivial
          || lhs_unknown == 0
          || rhs_false && lhs_unknown == 1 {
            profile! { self "constraints   broken" => add 1 }
          }
          // Discard the constraint, regardless of what will happen.
          profile! { self tick "data" }
          data.tautologize(cstr) ? ;
          for Sample { pred, args } in pos.drain(0..) {
            data.add_pos(pred, args) ;
          }
          for Sample { pred, args } in neg.drain(0..) {
            data.add_neg(pred, args) ;
          }
          data.propagate() ? ;
          profile! { self mark "data" }
          continue 'all_constraints
        }) ;
      }

      if let Some(
        & Sample { pred, ref args }
      ) = data.constraints[cstr].rhs() {
        match self.try_force(data, pred, args) ? {
          None => (),
          Some( Either::Left(pos_sample) ) => {
            pos.push(pos_sample) ;
            // Constraint is trivial, move on.
            trivial = true
          },
          Some( Either::Right(neg_sample) ) => {
            rhs_false = true ;
            neg.push(neg_sample)
          },
        }
      }

      // move_on!(if trivial) ;

      if let Some(lhs) = data.constraints[cstr].lhs() {
        'lhs: for (pred, samples) in lhs {
          let mut lhs_trivial = true ;
          for sample in samples {
            match self.try_force(data, * pred, sample) ? {
              None => {
                lhs_unknown += 1 ;
                lhs_trivial = false
              },
              Some( Either::Left(pos_sample) ) => pos.push(pos_sample),
              Some( Either::Right(neg_sample) ) => {
                neg.push(neg_sample) ;
                trivial = true ;
                // Constraint is trivial, move on.
                // break 'lhs
              },
            }
          }
          trivial = trivial || lhs_trivial
        }
      } else {
        bail!("Illegal constraint")
      }

      move_on!()

    }

    let (_pos_count, _neg_count) = data.pos_neg_count() ;
    if ! data.pos.is_empty() {
      profile! { self "positive examples generated" => add _pos_count }
    }
    if ! data.neg.is_empty() {
      profile! { self "negative examples generated" => add _neg_count }
    }

    Ok(())
  }

  /// Checks if a sample can be forced to anything.
  ///
  /// If it can't, return None. If it can, returns `Either`
  ///
  /// - `Left` of a sample which, when forced positive, will force the input
  ///   sample to be classified positive.
  /// - `Right` of a sample which, when forced negative, will force the input
  ///   sample to be classified negative.
  pub fn try_force(
    & mut self, _data: & Data, pred: PrdIdx, vals: & Args
  ) -> Res< Option< Either<Sample, Sample> > > {
    self.solver.comment_args(
      format_args!("working on sample ({} {})", self.instance[pred], vals)
    ) ? ;

    if let Some(clauses) = self.pos.get(& pred) {

      self.solver.comment("working on positive clauses") ? ;

      for clause in clauses {
        let clause = & self.instance[* clause] ;
        if let Some((p, args)) = clause.rhs() {
          debug_assert_eq! { pred, p }
          debug_assert! { clause.lhs_preds().is_empty() }

          self.solver.push(1) ? ;
          clause.declare(& mut self.solver) ? ;
          self.solver.assert(
            & ConjWrap::new( clause.lhs_terms() )
          ) ? ;
          self.solver.assert( & ArgValEq::new(args, vals) ) ? ;
          let sat = profile! {
            self wrap {
              self.solver.check_sat() ?
            } "smt"
          } ;
          self.solver.pop(1) ? ;

          if sat {
            // msg! { debug self => "  forcing positive" }
            return Ok(
              Some(
                Either::Left(
                  Sample { pred, args: vals.clone() }
                )
              )
            )
          }
        } else {
          bail!("inconsistent instance state")
        }
      }

    }

    if let Some(clauses) = self.neg.get(& pred) {

      self.solver.comment("working on negative clauses") ? ;

      for clause in clauses {
        let clause = & self.instance[* clause] ;
        if let Some(argss) = clause.lhs_preds().get(& pred) {
          let args = {
            let mut argss = argss.iter() ;
            if let Some(args) = argss.next() {
              debug_assert! { argss.next().is_none() }
              args
            } else {
              bail!("inconsistent instance state")
            }
          } ;

          self.solver.push(1) ? ;
          clause.declare(& mut self.solver) ? ;
          self.solver.assert(
            & ConjWrap::new( clause.lhs_terms() )
          ) ? ;
          self.solver.assert( & ArgValEq::new(args, vals) ) ? ;
          let sat = profile! {
            self wrap {
              self.solver.check_sat() ?
            } "smt"
          } ;
          self.solver.pop(1) ? ;

          if sat {
            // msg! { debug self => "  forcing negative" }
            return Ok(
              Some(
                Either::Right(
                  Sample { pred, args: vals.clone() }
                )
              )
            )
          }
        } else {
          bail!("inconsistent instance state")
        }
      }

    }

    // msg! { debug self => "  giving up" }

    Ok(None)
  }

}

/// Wrapper around a conjunction for smt printing.
struct ConjWrap<'a> {
  /// Conjunction.
  terms: & 'a HConSet<Term>,
}
impl<'a> ConjWrap<'a> {
  /// Constructor.
  pub fn new(terms: & 'a HConSet<Term>) -> Self {
    ConjWrap { terms }
  }
}
impl<'a> ::rsmt2::to_smt::Expr2Smt<()> for ConjWrap<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    if self.terms.is_empty() {
      write!(w, "true") ?
    } else {
      write!(w, "(and") ? ;
      for term in self.terms {
        write!(w, " ") ? ;
        term.write(w, |w, var| var.default_write(w)) ? ;
      }
      write!(w, ")") ?
    }
    Ok(())
  }
}


/// Wrapper around some arguments and some values.
///
/// Used to assert `(= arg[i] val[i])`.
pub struct ArgValEq<'a> {
  /// Arguments.
  args: & 'a HTArgs,
  /// Values.
  vals: & 'a Args,
}
impl<'a> ArgValEq<'a> {
  /// Constructor.
  pub fn new(args: & 'a HTArgs, vals: & 'a Args) -> Self {
    debug_assert_eq! { args.len(), vals.len() }
    ArgValEq { args, vals }
  }
}
impl<'a> Expr2Smt<()> for ArgValEq<'a> {
  fn expr_to_smt2<Writer>(
    & self, w: & mut Writer, _: ()
  ) -> ::rsmt2::SmtRes<()>
  where Writer: Write {
    write!(w, "(and") ? ;
    let mut unknown = 0 ;

    for (arg, val) in self.args.iter().zip( self.vals.iter() ) {
      match * val {
        Val::B(b) => {
          write!(w, " ") ? ;
          if ! b {
            write!(w, "(not ") ?
          }
          arg.write(
            w, |w, v| w.write_all( v.default_str().as_bytes() )
          ) ? ;
          if ! b {
            write!(w, ")") ?
          }
        },
        Val::I(ref i) => {
          write!(w, " (= ") ? ;
          arg.write(
            w, |w, v| w.write_all( v.default_str().as_bytes() )
          ) ? ;
          write!(w, " ") ? ;
          int_to_smt!(w, i) ? ;
          write!(w, ")") ?
        },
        Val::R(ref r) => {
          write!(w, " (= ") ? ;
          arg.write(
            w, |w, v| w.write_all( v.default_str().as_bytes() )
          ) ? ;
          write!(w, " ") ? ;
          rat_to_smt!(w, r) ? ;
          write!(w, ")") ?
        },
        Val::N => unknown += 1,
      }
    }

    if unknown == self.args.len() {
      write!(w, " true") ?
    }
    write!(w, ")") ? ;
    Ok(())
  }

}