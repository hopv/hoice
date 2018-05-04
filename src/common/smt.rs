//! SMT-related zero-cost wrappers.

use std::str::FromStr ;
use std::io::BufRead ;

use rsmt2::print::* ;
use rsmt2::parse::{ IdentParser, ValueParser, SmtParser } ;

use common::* ;
use common::data::Constraint ;


/// SMT-prints a term using the default var writer.
pub struct SmtTerm<'a> {
  /// The term.
  pub term: & 'a Term,
}
impl<'a> SmtTerm<'a> {
  /// Constructor.
  pub fn new(term: & 'a Term) -> Self {
    SmtTerm { term }
  }
}
impl<'a> Expr2Smt<()> for SmtTerm<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    self.term.write(
      w, |w, var| var.default_write(w)
    ) ? ;
    Ok(())
  }
}


/// SMT-prints a collection of terms as a conjunction with default var writer.
pub struct SmtConj<Trms> {
  /// Conjunction.
  terms: Trms,
}
impl<'a, Trms> SmtConj<Trms>
where Trms: Iterator<Item = & 'a Term> + ExactSizeIterator + Clone {
  /// Constructor.
  pub fn new<IntoIter>(terms: IntoIter) -> Self
  where IntoIter: IntoIterator<IntoIter = Trms, Item = & 'a Term> {
    SmtConj { terms: terms.into_iter() }
  }

  /// Checks if this conjunction is unsatisfiable.
  pub fn is_unsat<Parser: Copy>(
    & self, solver: & mut Solver<Parser>, vars: & VarInfos
  ) -> Res<bool> {
    if self.terms.len() == 0 { return Ok(false) }
    solver.push(1) ? ;
    for var in vars {
      if var.active {
        solver.declare_const(& var.idx, & var.typ) ?
      }
    }
    solver.assert( self ) ? ;
    let sat = solver.check_sat() ? ;
    solver.pop(1) ? ;
    Ok(! sat)
  }
}
impl<'a, Trms> Expr2Smt<()> for SmtConj<Trms>
where Trms: Iterator<Item = & 'a Term> + ExactSizeIterator + Clone {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    if self.terms.len() == 0 {
      write!(w, "true") ?
    } else {
      write!(w, "(and") ? ;
      for term in self.terms.clone().into_iter() {
        write!(w, " ") ? ;
        term.write(
          w, |w, var| var.default_write(w)
        ) ? ;
      }
      write!(w, ")") ?
    }
    Ok(())
  }
}



/// SMT-prints an implication `/\ (set \ term) => term`.
pub struct SmtImpl<'a> {
  /// Set of terms.
  pub set: & 'a HConSet<Term>,
  /// Term to remove from `set`.
  pub trm: & 'a Term,
}
impl<'a> SmtImpl<'a> {
  /// Constructor.
  ///
  /// Returns `None` if `set.is_empty()`.
  pub fn new(set: & 'a HConSet<Term>, trm: & 'a Term) -> Option<Self> {
    if ! set.is_empty() {
      Some( SmtImpl { set, trm } )
    } else {
      None
    }
  }
}
impl<'a> Expr2Smt<()> for SmtImpl<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    debug_assert! { ! self.set.is_empty() }
    write!(w, "(and (not ") ? ;
    self.trm.write(w, |w, var| var.default_write(w)) ? ;
    write!(w, ") ") ? ;
    if self.set.len() <= 1 {
      write!(w, "true") ?
    } else {
      write!(w, "(and ") ? ;
      for term in self.set {
        if term != self.trm {
          write!(w, " ") ? ;
          term.write(w, |w, var| var.default_write(w)) ?
        }
      }
      write!(w, ")") ?
    }
    write!(w, ")") ? ;
    Ok(())
  }
}



/// Wrapper around a predicate/sample pair that SMT-prints it as an identifier.
///
/// In practice, will be printed as `format!("|p_{} {}|", pred, smpl.uid())`.
pub struct SmtSample<'a> {
  /// Predicate index.
  pub pred: PrdIdx,
  /// Reference to a sample.
  pub smpl: & 'a Args,
}
impl<'a> SmtSample<'a> {
  /// Constructor.
  pub fn new(pred: PrdIdx, smpl: & 'a Args) -> Self {
    SmtSample { pred, smpl }
  }
}
impl<'a> Expr2Smt<()> for SmtSample<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!( w, "|p_{} {}|", self.pred, self.smpl.uid() ) ? ;
    Ok(())
  }
}
impl<'a> Sym2Smt<()> for SmtSample<'a> {
  fn sym_to_smt2<Writer>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> where Writer: Write {
    self.expr_to_smt2(w, ())
  }
}


/// Wrapper around constraints that forces smt printing consistent with
/// [`SmtSample`][swrap].
///
/// [swrap]: struct.SmtSample.html (SmtSample struct)
pub struct SmtConstraint<'a> {
  /// Reference to the constraint.
  pub constr: & 'a Constraint,
}
impl<'a> SmtConstraint<'a> {
  /// Constructor.
  pub fn new(constr: & 'a Constraint) -> Self {
    SmtConstraint { constr }
  }
}
impl<'a> Expr2Smt<()> for SmtConstraint<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "(=> ") ? ;
    if let Some(lhs) = self.constr.lhs() {
      write!(w, "(and") ? ;
      for (pred, samples) in lhs {
        for sample in samples {
          write!(w, " ", ) ? ;
          SmtSample::new(
            * pred, sample
          ).expr_to_smt2(w, ()) ?
        }
      }
      write!(w, ") ") ?
    } else {
      write!(w, "false ") ?
    }
    if let Some(rhs) = self.constr.rhs() {
      SmtSample::new(
        rhs.pred, & rhs.args
      ).expr_to_smt2(w, ()) ?
    } else {
      write!(w, "false") ? ;
    }
    write!(w, ")") ? ;
    Ok(())
  }
}


/// Wrapper for activation literals activating samples for some predicate.
///
/// `Sym2Smt` implementation just yields the actlit, used to declare said
/// actlit. `Expr2Smt` is the actual activation expression
///
/// ```bash
/// (=> <actlit> (and <samples>))
/// ```
///
/// Used by the ICE learner.
pub struct SmtActSamples<Samples> {
  /// Activation literal.
  pub actlit: Actlit,
  /// Predicate.
  pub pred: PrdIdx,
  /// Samples.
  pub unc: Samples,
  /// Indicates whether we're assuming the samples positive or negative.
  pub pos: bool,
}
impl<Samples> SmtActSamples<Samples> {
  /// Constructor.
  pub fn new<Parser>(
    solver: & mut Solver<Parser>, pred: PrdIdx, unc: Samples, pos: bool
  ) -> Res<Self> {
    let actlit = solver.get_actlit() ? ;
    Ok( SmtActSamples { actlit, pred, unc, pos } )
  }

  /// Sets the actlit to `pos` and destroys itself.
  pub fn force<Parser>(
    self, solver: & mut Solver<Parser>, pos: bool
  ) -> Res<()> {
    solver.set_actlit(self.actlit, pos) ? ;
    Ok(())
  }
}
impl<'a> Expr2Smt<()> for SmtActSamples<& 'a Vec<Args>> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "(=> ") ? ;
    self.actlit.write(w) ? ;
    write!(
      w, " ({}", if self.pos { "and" } else { "not (or" }
    ) ? ;
    for unc in self.unc {
      write!(w, " ", ) ? ;
      SmtSample::new(self.pred, unc).expr_to_smt2(w, ()) ?
    }
    write!(w, "))") ? ;
    if ! self.pos {
      write!(w, ")") ?
    }
    Ok(())
  }
}
impl<'a, T> Expr2Smt<()> for SmtActSamples<
  & 'a HConMap<Args, T>
> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "(=> ") ? ;
    self.actlit.write(w) ? ;
    write!(
      w, " ({}", if self.pos { "and" } else { "not (or" }
    ) ? ;
    for (unc, _) in self.unc {
      write!(w, " ", ) ? ;
      SmtSample::new(self.pred, unc).expr_to_smt2(w, ()) ?
    }
    write!(w, "))") ? ;
    if ! self.pos {
      write!(w, ")") ?
    }
    Ok(())
  }
}



/// Wrapper around some terms and some values for these terms.
///
/// Asserts that each term is equal to the corresponding value.
pub struct EqConj<'a> {
  /// Terms.
  pub terms: & 'a Vec<Term>,
  /// Values.
  pub vals: & 'a Args,
}
impl<'a> EqConj<'a> {
  /// Constructor.
  ///
  /// Both lists must have the same length.
  pub fn new(terms: & 'a Vec<Term>, vals: & 'a Args) -> Self {
    debug_assert_eq! { terms.len(), vals.len() }

    EqConj { terms, vals }
  }
}
impl<'a> Expr2Smt<()> for EqConj<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    let mut is_first = true ;
    for (term, val) in self.terms.iter().zip( self.vals.iter() ) {
      if ! val.is_known() {
        continue
      }
      if is_first {
        write!(w, "(and") ? ;
        is_first = false
      }
      write!(w, " (= ") ? ;
      term.write(w, |w, var| write!(w, "{}", var.default_str())) ? ;
      write!(w, " ") ? ;
      val.expr_to_smt2(w, ()) ? ;
      write!(w, ")") ?
    }
    if is_first {
      write!(w, "true") ?
    } else {
      write!(w, ")") ?
    }
    Ok(())
  }
}



/// Wrapper for some arguments and a disjunction of terms.
///
/// Corresponds to the disjunction of `(= args v)` for `v` in `vals`.
pub struct DisjArgs<'a> {
  /// Arguments.
  pub args: & 'a HTArgs,
  /// Values to force the arguments to.
  pub vals: & 'a ArgsSet,
}
impl<'a> DisjArgs<'a> {
  /// Constructor.
  ///
  /// Error if `args` or `vals` is empty.
  #[inline]
  pub fn new(
    args: & 'a HTArgs, vals: & 'a ArgsSet
  ) -> Res<Self> {
    if args.is_empty() {
      bail!("can't create a `DisjArgs` with empty `args`")
    }
    if vals.is_empty() {
      bail!("can't create an empty `DisjArgs`")
    }
    Ok( DisjArgs { args, vals } )
  }
}
impl<'a> Expr2Smt<()> for DisjArgs<'a> {
  fn expr_to_smt2<Writer: Write>(
    & self, w: & mut Writer, _: ()
  ) -> SmtRes<()> {
    write!(w, "(or") ? ;
    for vals in self.vals {
      write!(w, " (and") ? ;
      debug_assert_eq! { self.args.len(), vals.len() }
      let mut at_least_one = false ;
      for (arg, val) in self.args.iter().zip( vals.iter() ) {
        if val.is_known() {
          at_least_one = true ;
          write!(w, " (= ") ? ;
          arg.write(w, |w, var| write!(w, "{}", var.default_str())) ? ;
          write!(w, " ") ? ;
          val.expr_to_smt2(w, ()) ? ;
          write!(w, ")") ?
        }
      }
      if ! at_least_one {
        write!(w, " true") ?
      }
      write!(w, ")") ?
    }
    write!(w, ")") ? ;

    Ok(())
  }
}





/// Unit type parsing the output of the SMT solver.
///
/// Parses variables of the form `v<int>` and constants. It is designed to
/// parse models of the falsification of a single clause, where the
/// variables of the clause are written as `v<index>` in smt2.
#[derive(Clone, Copy)]
pub struct FullParser ;

impl<'a> IdentParser<VarIdx, (), & 'a str> for FullParser {
  fn parse_ident(self, input: & 'a str) -> SmtRes<VarIdx> {
    debug_assert_eq!( & input[0..2], "v_" ) ;
    match usize::from_str(& input[2..]) {
      Ok(idx) => Ok( idx.into() ),
      Err(e) => bail!(
        "could not retrieve var index from `{}`: {}", input, e
      ),
    }
  }
  fn parse_type(self, _: & 'a str) -> SmtRes<()> {
    Ok(())
  }
}

impl<'a, Br> ValueParser<Val, & 'a mut SmtParser<Br>> for FullParser
where Br: BufRead {
  fn parse_value(self, input: & 'a mut SmtParser<Br>) -> SmtRes<Val> {
    if let Some(val) = input.try_int::<
      _, _, ::num::bigint::ParseBigIntError
    >(
      |int, pos| {
        let int = Int::from_str(int) ? ;
        Ok( if ! pos { - int } else { int } )
      }
    ) ? {
      Ok( Val::I(val) )
    } else if let Some(val) = input.try_bool() ? {
      Ok( Val::B(val) )
    } else if let Some(val) = input.try_rat::<
      _, _, ::num::bigint::ParseBigIntError
    >(
      |num, den, pos| {
        let (num, den) = (
          Int::from_str(num) ?, Int::from_str(den) ?
        ) ;
        let rat = Rat::new(num, den) ;
        Ok( if ! pos { - rat } else { rat } )
      }
    ) ? {
      let mut val = Val::R(val) ;
      Ok(val)
    } else {
      input.fail_with("unexpected value")
    }
  }
}