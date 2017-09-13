//! Terms structure and factory.

use std::sync::RwLock ;

use hashconsing::* ;

use common::* ;
use self::info::* ;

pub mod info ;
// pub mod build ;
pub mod parse ;
pub mod preproc ;

/// Types.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub enum Typ {
  /// Integers.
  Int,
  /// Booleans.
  Bool,
}
impl Typ {
  /// Type parser.
  #[allow(unused_variables)]
  pub fn parse(
    bytes: & [u8]
  ) -> ::nom::IResult<& [u8], Self, Error> {
    fix_error!(
      bytes,
      Error,
      alt_complete!(
        map!(tag!("Int"),  |_| Typ::Int)  |
        map!(tag!("Bool"), |_| Typ::Bool)
      )
    )
  }
  /// Default value of a type.
  pub fn default_val(& self) -> Val {
    match * self {
      Typ::Int => Val::I( Int::zero() ),
      Typ::Bool => Val::B( true ),
    }
  }
}
impl ::rsmt2::Sort2Smt for Typ {
  fn sort_to_smt2<Writer>(
    & self, w: &mut Writer
  ) -> SmtRes<()> where Writer: Write {
    smt_cast_io!( "while writing type as smt2" => write!(w, "{}", self) )
  }
}
impl_fmt!{
  Typ(self, fmt) {
    use instance::Typ::* ;
    match * self {
      Int => fmt.write_str("Int"),
      Bool => fmt.write_str("Bool"),
    }
  }
}



/// A real term.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum RTerm {
  /// A clause variable.
  Var(VarIdx),
  /// An integer.
  Int(Int),
  /// A boolean.
  Bool(bool),
  /// An operator application.
  App {
    /// The operator.
    op: Op,
    /// The arguments.
    args: Vec<Term>,
  },
}
impl RTerm {

  /// Write a real term using a special function to write variables.
  pub fn write<W, WriteVar>(
    & self, w: & mut W, write_var: WriteVar
  ) -> IoRes<()>
  where W: Write, WriteVar: Fn(& mut W, VarIdx) -> IoRes<()> {
    let mut stack = vec![
      (vec![self], "", "")
    // ^^^^^^^^^|  ^|  ^^~~~ termination string (written once vector's empty)
    //          |   |~~~~~~~ prefix string      (written before next element)
    //          |~~~~~~~~~~~ elements to write
    ] ;
    while let Some( (mut to_do, sep, end) ) = stack.pop() {
      use self::RTerm::* ;
      if let Some(term) = to_do.pop() {
        stack.push( (to_do, sep, end) ) ;
        match * term {
          Var(v) => {
            write!(w, "{}", sep) ? ;
            write_var(w, v) ?
          },
          Int(ref i) => {
            write!(w, "{}", sep) ? ;
            if i.is_negative() {
              write!(w, "(- {})", - i) ?
            } else {
              write!(w, "{}", i) ?
            }
          },
          Bool(b) => write!(w, "{}{}", sep, b) ?,
          App { op, ref args } => {
            write!(w, "{}({}", sep, op) ? ;
            stack.push(
              (args.iter().rev().map(|t| t.get()).collect(), " ", ")")
            )
          },
        }
      } else { w.write_all( end.as_bytes() ) ? }
    }
    Ok(())
  }

  /// Term evaluation (int).
  pub fn int_eval(& self, model: & VarMap<Val>) -> Res< Option<Int> > {
    self.eval(model)?.to_int()
  }

  /// Term evaluation (bool).
  pub fn bool_eval(& self, model: & VarMap<Val>) -> Res< Option<bool> > {
    self.eval(model)?.to_bool()
  }

  /// True if the term has no variables and evaluates to true.
  ///
  /// ```
  /// # use hoice_lib::instance::* ;
  /// let instance = & Instance::mk(10, 10, 10) ;
  ///
  /// let term = instance.bool(true) ;
  /// println!("true") ;
  /// assert!( term.is_true() ) ;
  /// let term = instance.bool(false) ;
  /// println!("false") ;
  /// assert!( ! term.is_true() ) ;
  /// let term = instance.eq(
  ///   instance.int(7), instance.var(1.into())
  /// ) ;
  /// println!("7 = v_1") ;
  /// assert!( ! term.is_true() ) ;
  /// let term = instance.eq(
  ///   instance.int(9), instance.int(9)
  /// ) ;
  /// println!("9 = 9") ;
  /// assert!( term.is_true() ) ;
  /// let term = instance.eq(
  ///   instance.int(1), instance.int(9)
  /// ) ;
  /// println!("1 = 9") ;
  /// assert!( ! term.is_true() ) ;
  /// let term = instance.le(
  ///   instance.op(
  ///     Op::Add, vec![ instance.int(3), instance.int(4) ]
  ///   ), instance.int(9)
  /// ) ;
  /// println!("3 + 4 = 9") ;
  /// assert!( term.is_true() ) ;
  /// ```
  pub fn is_true(& self) -> bool {
    match self.bool_eval( & VarMap::with_capacity(0) ) {
      Ok(Some(b)) => b,
      _ => false,
    }
  }
  
  /// True if the term has no variables and evaluates to true.
  ///
  /// ```
  /// # use hoice_lib::instance::* ;
  /// let instance = & Instance::mk(10, 10, 10) ;
  ///
  /// let term = instance.bool(true) ;
  /// println!("true") ;
  /// assert!( ! term.is_false() ) ;
  /// let term = instance.bool(false) ;
  /// println!("false") ;
  /// assert!( term.is_false() ) ;
  /// let term = instance.eq(
  ///   instance.int(7), instance.var(1.into())
  /// ) ;
  /// println!("7 = v_1") ;
  /// assert!( ! term.is_false() ) ;
  /// let term = instance.eq(
  ///   instance.int(9), instance.int(9)
  /// ) ;
  /// println!("9 = 9") ;
  /// assert!( ! term.is_false() ) ;
  /// let term = instance.eq(
  ///   instance.int(1), instance.int(9)
  /// ) ;
  /// println!("1 = 9") ;
  /// assert!( term.is_false() ) ;
  /// let term = instance.le(
  ///   instance.int(9), instance.op(
  ///     Op::Add, vec![ instance.int(3), instance.int(4) ]
  ///   )
  /// ) ;
  /// println!("9 <= 3 + 4") ;
  /// assert!( term.is_false() ) ;
  /// ```
  pub fn is_false(& self) -> bool {
    match self.bool_eval( & VarMap::with_capacity(0) ) {
      Ok(Some(b)) => ! b,
      _ => false,
    }
  }
  /// Boolean a constant boolean term evaluates to.
  pub fn bool(& self) -> Option<bool> {
    match self.bool_eval( & VarMap::with_capacity(0) ) {
      Ok(Some(b)) => Some(b),
      _ => None
    }
  }
  /// Integer a constant integer term evaluates to.
  pub fn int(& self) -> Option<Int> {
    match self.int_eval( & VarMap::with_capacity(0) ) {
      Ok(Some(i)) => Some(i),
      _ => None
    }
  }

  /// The kids of this term, if any.
  pub fn kids(& self) -> Option<& [Term]> {
    if let RTerm::App{ ref args, .. } = * self {
      Some(args)
    } else {
      None
    }
  }
  /// Checks whether the term is a relation.
  pub fn is_relation(& self) -> bool {
    match * self {
      RTerm::App { op: Op::Eql, .. } |
      RTerm::App { op: Op::Gt, .. } |
      RTerm::App { op: Op::Ge, .. } |
      RTerm::App { op: Op::Lt, .. } |
      RTerm::App { op: Op::Le, .. } => true,
      RTerm::App { op: Op::Not, ref args } => args[0].is_relation(),
      _ => false,
    }
  }


  /// Term evaluation.
  pub fn eval(& self, model: & VarMap<Val>) -> Res<Val> {
    use self::RTerm::* ;
    let mut current = self ;
    let mut stack = vec![] ;

    'eval: loop {

      // Go down applications.
      let mut evaled = match * current {
        App { op, ref args } => {
          current = & args[0] ;
          stack.push( (op, & args[1..], vec![]) ) ;
          continue 'eval
        },
        // Rest are leaves, going up.
        Var(v) => if v < model.len() {
          model[v].clone()
        } else {
          bail!("model is too short")
        },
        Int(ref i) => Val::I( i.clone() ),
        Bool(b) => Val::B(b),
      } ;

      // Go up.
      'go_up: loop {
        if let Some( (op, to_do, mut values) ) = stack.pop() {
          if to_do.is_empty() {
            values.push(evaled) ;
            evaled = op.eval(values).chain_err(
              || format!("while evaluating operator `{}`", op)
            ) ? ;
            continue 'go_up
          } else {
            // Going down the first element of `to_do`.
            current = & to_do[0] ;
            values.push(evaled) ;
            stack.push( (op, & to_do[1..], values) ) ;
            // Go down.
            continue 'eval
          }
        } else {
          // We are at the top level, done.
          return Ok(evaled)
        }
      }

    }
  }

  /// If the term's an integer constants, returns the value.
  pub fn int_val(& self) -> Option<Int> {
    if let RTerm::Int(ref i) = * self { Some( i.clone() ) } else { None }
  }

  /// The highest variable index appearing in the term.
  pub fn highest_var(& self) -> Option<VarIdx> {
    let mut to_do = vec![ self ] ;
    let mut max = None ;
    while let Some(term) = to_do.pop() {
      match * term {
        RTerm::Var(i) => max = Some(
          ::std::cmp::max( i, max.unwrap_or(0.into()) )
        ),
        RTerm::Int(_) => (),
        RTerm::Bool(_) => (),
        RTerm::App{ ref args, .. } => for arg in args {
          to_do.push(arg)
        },
      }
    }
    max
  }

  /// All the variables appearing in a term.
  pub fn vars(& self) -> VarSet {
    let mut to_do = vec![ self ] ;
    let mut set = VarSet::with_capacity(11) ;
    while let Some(term) = to_do.pop() {
      match * term {
        RTerm::Var(i) => {
          let _ = set.insert(i) ; ()
        },
        RTerm::Int(_) => (),
        RTerm::Bool(_) => (),
        RTerm::App{ ref args, .. } => for arg in args {
          to_do.push(arg)
        },
      }
    }
    set.shrink_to_fit() ;
    set
  }

  /// Returns the variable index if the term is a variable.
  pub fn var_idx(& self) -> Option<VarIdx> {
    match * self {
      RTerm::Var(i) => Some(i),
      _ => None,
    }
  }

  /// If the term is a negation, returns what's below the negation.
  pub fn rm_neg(& self) -> Option<Term> {
    match * self {
      RTerm::App { op: Op::Not, ref args } => {
        debug_assert_eq!( args.len(), 1 ) ;
        Some( args[0].clone() )
      },
      _ => None,
    }
  }
}
impl_fmt!{
  RTerm(self, fmt) {
    let mut buf = Vec::with_capacity(250) ;
    self.write(& mut buf, |w, var| var.default_write(w)).expect(
      "fatal error during real term pretty printing"
    ) ;
    let s = ::std::str::from_utf8(& buf).expect(
      "fatal error during real term pretty printing"
    ) ;
    write!(fmt, "{}", s)
  }
}

// impl<'a, WriteVar> ::rsmt2::Expr2Smt<WriteVar> for SWrap<'a>
// where WriteVar: Fn(VarIdx) -> & Val {
//   fn expr_to_smt2<Writer: Write>(
//     & self, w: & mut Writer, _: & ()
//   ) -> SmtRes<()> {
//     smt_cast_io!(
//       "writing sample as expression" => write!(
//         w, "|p_{} {}|", self.0, self.1.uid()
//       )
//     )
//   }
// }



/// Hash consed term.
pub type Term = HConsed<RTerm> ;











/// Top term, as they appear in clauses.
#[derive(Clone, PartialEq, Eq)]
pub enum TTerm {
  /// A predicate application.
  P {
    /// Predicate applied.
    pred: PrdIdx,
    /// The arguments.
    args: VarMap<Term>,
  },
  /// Just a term.
  T(Term),
}
impl TTerm {
  /// True if the top term is a term with no variables and evaluates to true.
  pub fn is_true(& self) -> bool {
    match * self {
      TTerm::T(ref t) => t.is_true(),
      _ => false,
    }
  }
  /// True if the top term is a term with no variables and evaluates to false.
  pub fn is_false(& self) -> bool {
    match * self {
      TTerm::T(ref t) => t.is_false(),
      _ => false,
    }
  }
  /// Boolean corresponding to the top term if it's a bool constant.
  pub fn bool(& self) -> Option<bool> {
    match * self {
      TTerm::T(ref t) => t.bool(),
      _ => None,
    }
  }
  /// Boolean corresponding to the top term if it's an integer constant.
  pub fn int(& self) -> Option<Int> {
    match * self {
      TTerm::T(ref t) => t.int(),
      _ => None,
    }
  }

  /// The predicate a top term is an application of, if any.
  pub fn pred(& self) -> Option<PrdIdx> {
    match * self {
      TTerm::P { pred, .. } => Some(pred),
      _ => None,
    }
  }

  /// The arguments of a top term if it's a predicate application.
  pub fn args(& self) -> Option<& VarMap<Term>> {
    match * self {
      TTerm::P { ref args, .. } => Some(args),
      _ => None,
    }
  }

  /// Variables appearing in a top term.
  pub fn vars(& self) -> VarSet {
    match * self {
      TTerm::P { ref args, .. } => {
        use std::iter::Extend ;
        let mut vars = VarSet::with_capacity(17) ;
        for term in args {
          vars.extend( term.vars() )
        }
        vars
      },
      TTerm::T(ref term) => term.vars(),
    }
  }

  /// Writes a top term using special functions for writing predicates and
  /// variables.
  pub fn write<W, WriteVar, WritePrd>(
    & self, w: & mut W, write_var: WriteVar, write_prd: WritePrd
  ) -> IoRes<()>
  where
  W: Write,
  WriteVar: Fn(& mut W, VarIdx) -> IoRes<()>,
  WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    use self::TTerm::* ;
    match * self {
      P { pred, ref args } => write_prd(w, pred, args),
      T(ref t) => t.write(w, write_var),
    }
  }

  /// Writes a top term smt2 style using a special function for writing
  /// predicates.
  pub fn write_smt2<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where
  W: Write,
  WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    self.write(
      w, |w, var| var.default_write(w), write_prd
    )
  }
}
impl_fmt!{
  TTerm(self, fmt) {
    match * self {
      TTerm::P { pred, ref args } => {
        write!(fmt, "(p_{}", pred) ? ;
        for arg in args {
          write!(fmt, " {}", arg) ?
        }
        write!(fmt, ")")
      },
      TTerm::T(ref t) => write!(fmt, "{}", t),
    }
  }
}









/// A clause.
pub struct Clause {
  vars: VarMap<VarInfo>,
  lhs: Vec<TTerm>,
  rhs: TTerm,
}
impl Clause {
  /// Creates a clause.
  pub fn mk(
    vars: VarMap<VarInfo>, lhs: Vec<TTerm>, rhs: TTerm
  ) -> Self {
    Clause { vars, lhs, rhs }
  }

  /// LHS accessor.
  pub fn lhs(& self) -> & [TTerm] {
    & self.lhs
  }
  /// RHS accessor.
  pub fn rhs(& self) -> & TTerm {
    & self.rhs
  }

  /// Variables accessor.
  pub fn vars(& self) -> & VarMap<VarInfo> {
    & self.vars
  }

  // /// Replaces a predicate application by some top terms.
  // ///
  // /// Does not preserve the order of the top terms.
  // pub fn subst_top(& mut self, pred: PrdIdx, top) -> 

  /// Writes a clause given a special function to write predicates.  
  fn write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    use common::consts::keywords ;

    write!(w, "({} ({}\n  (", keywords::assert, keywords::forall) ? ;
    for var in & self.vars {
      write!(w, " ({} {})", var.name, var.typ) ?
    }
    write!(w, " )\n") ? ;

    let (pref, suff) = if ! self.lhs.is_empty() {
      write!(w, "  (=>") ? ;
      let (pref, suff) = if self.lhs.len() > 1 {
        write!(w, "\n    (and") ? ;
        ("      ", Some("    )"))
      } else {
        ("    ", None)
      } ;

      for tterm in & self.lhs {
        write!(w, "\n{}", pref) ? ;
        tterm.write(
          w, |w, var| w.write_all( self.vars[var].as_bytes() ), & write_prd
        ) ?
      }

      write!(w, "\n") ? ;
      if let Some(suff) = suff {
        write!(w, "{}\n", suff) ?
      }
      ("    ", Some("  )"))
    } else {
      ("  ", None)
    } ;

    write!(w, "{}", pref) ? ;
    self.rhs.write(
      w, |w, var| w.write_all( self.vars[var].as_bytes() ), & write_prd
    ) ? ;
    write!(w, "\n") ? ;
    if let Some(suff) = suff {
      write!(w, "{}", suff) ?
    }
    write!(w, "\n))")
  }
}
impl ::std::ops::Index<VarIdx> for Clause {
  type Output = VarInfo ;
  fn index(& self, index: VarIdx) -> & VarInfo {
    & self.vars[index]
  }
}
impl<'a> ::rsmt2::Expr2Smt<
  (& 'a PrdSet, & 'a PrdSet, & 'a PrdMap<PrdInfo>)
> for Clause {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, info: & (
      & 'a PrdSet, & 'a PrdSet, & 'a PrdMap<PrdInfo>
    )
  ) -> SmtRes<()> {
    let (ref true_preds, ref false_preds, ref prd_info) = * info ;
    smt_cast_io!{
      "writing clause as smt2" =>
        write!(writer, "(not ") ;
        if self.lhs.is_empty() {
          Ok(())
        } else {
          write!(writer, "(=> (and")
        } ;
        {
          for lhs in & self.lhs {
            smtry_io!(
              "writing clause's lhs" =>
              write!(writer, " ") ;
              lhs.write_smt2(
                writer, |w, prd, args| {
                  if true_preds.contains(& prd) {
                    write!(w, "true")
                  } else if false_preds.contains(& prd) {
                    write!(w, "false")
                  } else {
                    write!(w, "({}", prd_info[prd].name) ? ;
                    for arg in args {
                      write!(w, " ") ? ;
                      arg.write(w, |w, var| var.default_write(w)) ?
                    }
                    write!(w, ")")
                  }
                }
              )
            )
          }
          Ok(()) as IoRes<()>
        } ;
        if self.lhs.is_empty() { Ok(()) } else {
          write!(writer, ") ")
        } ;
        self.rhs.write_smt2(
          writer, |w, prd, args| {
            if true_preds.contains(& prd) {
              write!(w, "true")
            } else if false_preds.contains(& prd) {
              write!(w, "false")
            } else {
              write!(w, "({}", prd_info[prd].name) ? ;
              for arg in args {
                write!(w, " ") ? ;
                arg.write(w, |w, var| var.default_write(w)) ?
              }
              write!(w, ")")
            }
          }
        ) ;
        if self.lhs.is_empty() { Ok(()) } else {
          write!(writer, ")")
        } ;
        write!(writer, ")")
    }
  }
}


/// Type of the underlying factory.
type Factory = RwLock< HashConsign<RTerm> > ;



/// Performs variable substitution over terms.
pub trait SubstExt {
  /// Variable substitution.
  ///
  /// Returns the new term and a boolean indicating whether any substitution
  /// occured.
  ///
  /// Used for substitutions in the same clause / predicate scope.
  fn subst(
    & self, map: & VarHMap<Term>, term: & Term
  ) -> (Term, bool) {
    self.subst_custom(map, term, false).expect("total substitution can't fail")
  }
  /// In-place variable substitution for top terms.
  ///
  /// Returns the new term and a boolean indicating whether any substitution
  /// occured.
  ///
  /// Used for substitutions in the same clause / predicate scope.
  fn tterm_subst(
    & self, map: & VarHMap<Term>, term: & mut TTerm
  ) {
    match * term {
      TTerm::T(ref mut term) => {
        * term = self.subst(map, term).0
      },
      TTerm::P { ref mut args, .. } => {
        for arg in args.iter_mut() {
          * arg = self.subst(map, arg).0
        }
      },
    }
  }

  /// Fixed-point variable substitution.
  ///
  /// Returns the new term and a boolean indicating whether any substitution
  /// occured.
  fn subst_fp(& self, map: & VarHMap<Term>, term: & Term) -> (Term, bool) {
    let (mut term, mut changed) = self.subst(map, term) ;
    while changed {
      let (new_term, new_changed) = self.subst(map, & term) ;
      term = new_term ;
      changed = new_changed
    }
    (term, changed)
  }

  /// Total variable substition, returns `None` if there was a variable in the
  /// term that was not in the map.
  ///
  /// Returns the new term and a boolean indicating whether any substitution
  /// occured.
  ///
  /// Used for substitutions between different same clause / predicate scopes.
  fn subst_total(
    & self, map: & VarHMap<Term>, term: & Term
  ) -> Option< (Term, bool) > {
    self.subst_custom(map, term, true)
  }

  /// Variable substitution.
  ///
  /// Returns the new term and a boolean indicating whether any substitution
  /// occured.
  ///
  /// The substitution *fails* by returning `None` if
  ///
  /// - `total` and the term contains a variable that's not in the map
  ///
  /// Used by qualifier extraction.
  fn subst_custom(
    & self, map: & VarHMap<Term>, term: & Term, total: bool
  ) -> Option<(Term, bool)> ;
}

impl SubstExt for Factory {
  fn subst_custom(
    & self, map: & VarHMap<Term>, term: & Term, total: bool
  ) -> Option<(Term, bool)> {
    let mut current = term ;
    // Stack for traversal.
    let mut stack = vec![] ;
    // Number of substitutions performed.
    let mut subst_count = 0 ;

    'go_down: loop {

      // Go down.
      let mut term = match * current.get() {
        RTerm::Var(var) => if let Some(term) = map.get(& var) {
          subst_count += 1 ;
          term.clone()
        } else if total {
          return None
        } else {
          current.clone()
        },
        RTerm::App { op, ref args } => {
          current = & args[0] ;
          stack.push(
            (op, & args[1..], Vec::with_capacity( args.len() ))
          ) ;
          continue 'go_down
        },
        _ => current.clone(),
      } ;

      // Go up.
      'go_up: while let Some(
        (op, args, mut new_args)
      ) = stack.pop() {
        new_args.push( term ) ;
        
        if args.is_empty() {
          term = self.mk( RTerm::App { op, args: new_args } ) ;
          continue 'go_up // Just for readability
        } else {
          current = & args[0] ;
          stack.push( (op, & args[1..], new_args) ) ;
          continue 'go_down
        }
      }

      // Only way to get here is if the stack is empty, meaning we're done.
      return Some( (term, subst_count > 0) )
    }
  }
}





impl SubstExt for Instance {
  fn subst_custom(
    & self, map: & VarHMap<Term>, term: & Term, total: bool
  ) -> Option<(Term, bool)> {
    self.factory.subst_custom(map, term, total)
  }
}






/// Stores the instance: the clauses, the factory and so on.
///
/// # NB
///
/// Clause indices can vary during instance building, because of the
/// simplifications that can remove clauses.
///
/// So, `pred_to_clauses` has to be carefully maintained, the easiest way to
/// do this is to never access an instance's fields directly from the outside.
///
/// # TO DO
///
/// - tests for `pred_to_clauses` consistency
pub struct Instance {
  /// Term factory.
  factory: Factory,
  /// Constants constructed so far.
  consts: HConSet<RTerm>,
  /// Predicates.
  preds: PrdMap<PrdInfo>,
  /// Predicates for which a suitable term has been found.
  pred_terms: PrdMap< Option< Vec<TTerm> > >,
  /// Predicates defined in `pred_terms`, sorted by predicate dependencies.
  ///
  /// Populated by the `finalize` function.
  sorted_pred_terms: Vec<PrdIdx>,
  /// Max arity of the predicates.
  pub max_pred_arity: Arity,
  /// Clauses.
  clauses: ClsMap<Clause>,
  /// Maps predicates to the clauses where they appear in the lhs and rhs
  /// respectively.
  pred_to_clauses: PrdMap< (ClsSet, ClsSet) >,
  /// Maps clauses to the predicates appearing in them.
  clause_to_preds: ClsMap< (PrdSet, Option<PrdIdx>) >,
}
impl Instance {
  /// Instance constructor.
  pub fn mk(
    term_capa: usize, clauses_capa: usize, pred_capa: usize
  ) -> Instance {
    let mut instance = Instance {
      factory: RwLock::new(
        HashConsign::with_capacity(term_capa)
      ),
      consts: HConSet::with_capacity(103),
      preds: PrdMap::with_capacity(pred_capa),
      pred_terms: PrdMap::with_capacity(pred_capa),
      sorted_pred_terms: Vec::with_capacity(pred_capa),
      max_pred_arity: 0.into(),
      clauses: ClsMap::with_capacity(clauses_capa),
      pred_to_clauses: PrdMap::with_capacity(pred_capa),
      clause_to_preds: ClsMap::with_capacity(clauses_capa),
    } ;
    // Create basic constants, adding to consts to have mining take them into account.
    let (wan,too) = (instance.one(), instance.zero()) ;
    instance.consts.insert(wan) ;
    instance.consts.insert(too) ;
    instance
  }

  /// Returns the model corresponding to the input predicates and the forced
  /// predicates.
  ///
  /// The model is sorted in topological order.
  pub fn model_of(& self, candidates: Candidates) -> Res<Model> {
    use std::iter::Extend ;
    let mut res = Model::with_capacity( self.preds.len() ) ;
    res.extend(
      candidates.into_index_iter().filter_map(
        |(pred, tterms_opt)| tterms_opt.map(
          |term| (pred, vec![ TTerm::T(term) ])
        )
      )
    ) ;
    for pred in & self.sorted_pred_terms {
      let pred = * pred ;
      if let Some(ref tterms) = self.pred_terms[pred] {
        res.push( (pred, tterms.clone()) )
      } else {
        bail!("inconsistency in sorted forced predicates")
      }
    }
    Ok(res)
  }

  /// Returns a model for the instance when all the predicates have terms
  /// assigned to them.
  pub fn is_trivial(& self) -> Res< Option<Model> > {
    for term_opt in & self.pred_terms {
      if term_opt.is_none() { return Ok(None) }
    }
    // Only reachable if all elements of `self.pred_terms` are `Some(_)`.
    self.model_of( vec![].into() ).map(|res| Some(res))
  }


  /// Prints a top term as a term in a model.
  ///
  /// Meaning a variables are printed with default printing: `<var_idx>` is
  /// printed as `v_<var_idx>`.
  pub fn print_tterm_as_model<W: Write>(
    & self, w: & mut W, tterm: & TTerm
  ) -> ::std::io::Result<()> {
    match * tterm {
      TTerm::T(ref term) => write!(w, "{}", term),
      TTerm::P { pred, ref args } => {
        write!(w, "({}", self[pred]) ? ;
        for arg in args {
          write!(w, " {}", arg) ?
        }
        write!(w, ")")
      },
    }
  }

  /// Finalizes instance creation.
  ///
  /// - shrinks all collections
  /// - sorts forced predicates by dependencies
  ///
  /// # TO DO
  ///
  /// - optimize sorting of forced preds by dependencies (low priority)
  pub fn finalize(& mut self) {
    self.consts.shrink_to_fit() ;
    self.preds.shrink_to_fit() ;
    self.pred_terms.shrink_to_fit() ;
    self.clauses.shrink_to_fit() ;

    let mut tmp: Vec< (PrdIdx, PrdSet) > = Vec::with_capacity(
      self.preds.len()
    ) ;

    // Populate `sorted_pred_terms`.
    for (pred, tterms) in self.pred_terms.index_iter() {
      if let Some(ref tterms) = * tterms {
        let mut deps = PrdSet::with_capacity( self.preds.len() ) ;
        for tterm in tterms {
          if let Some(pred) = tterm.pred() {
            deps.insert(pred) ;
          }
        }
        tmp.push( (pred, deps) )
      }
    }

    // Sort by dependencies.
    let mut known_preds = PrdSet::with_capacity( self.preds.len() ) ;
    for (pred, want_none) in self.pred_terms.index_iter() {
      if want_none.is_none() { known_preds.insert(pred) ; () }
    }
    while ! tmp.is_empty() {
      let mut cnt = 0 ; // Will use swap remove.
      'find_preds: while cnt < tmp.len() {
        for pred in & tmp[cnt].1 {
          if ! known_preds.contains(pred) {
            // Don't know this predicate, keep going in `tmp`.
            cnt += 1 ;
            continue 'find_preds
          }
        }
        // Reachable only we already have all of the current pred's
        // dependencies.
        let (pred, _) = tmp.swap_remove(cnt) ;
        self.sorted_pred_terms.push(pred) ;
        known_preds.insert(pred) ;
        () // No `cnt` increment after swap remove.
      }
    }

    self.sorted_pred_terms.shrink_to_fit()
  }


  /// Returns the term we already know works for a predicate, if any.
  pub fn forced_terms_of(& self, pred: PrdIdx) -> Option<& Vec<TTerm>> {
    self.pred_terms[pred].as_ref()
  }

  /// If the input predicate is forced to a constant boolean, returns its
  /// value.
  pub fn bool_value_of(& self, pred: PrdIdx) -> Option<bool> {
    self.forced_terms_of(pred).and_then(
      |terms| if terms.len() == 1 {
        if let TTerm::T(ref term) = terms[0] {
          term.bool()
        } else { None }
      } else {
        None
      }
    )
  }

  /// Forced predicates in topological order.
  pub fn sorted_forced_terms(& self) -> & Vec<PrdIdx> {
    & self.sorted_pred_terms
  }

  /// Returns the clauses in which the predicate appears in the lhs and rhs
  /// respectively.
  pub fn clauses_of(& self, pred: PrdIdx) -> (& ClsSet, & ClsSet) {
    (& self.pred_to_clauses[pred].0, & self.pred_to_clauses[pred].1)
  }

  /// Adds some terms to the lhs of a clause.
  ///
  /// Updates `pred_to_clauses`.
  pub fn clause_lhs_extend(
    & mut self, clause: ClsIdx, tterms: & mut Vec<TTerm>
  ) {
    self.clauses[clause].lhs.reserve( tterms.len() ) ;
    for tterm in tterms.drain(0..) {
      if let TTerm::P { pred, .. } = tterm {
        self.pred_to_clauses[pred].0.insert(clause) ;
      }
      self.clauses[clause].lhs.push(tterm)
    }
  }

  /// Replaces the rhs of a clause.
  pub fn clause_rhs_force(
    & mut self, clause: ClsIdx, tterm: TTerm
  ) {
    if let TTerm::P { pred, .. } = self.clauses[clause].rhs {
      self.pred_to_clauses[pred].1.remove(& clause) ;
    }
    if let TTerm::P { pred, .. } = tterm {
      self.pred_to_clauses[pred].1.insert(clause) ;
    }
    self.clauses[clause].rhs = tterm
  }

  // /// Evaluates the term a predicate is forced to, if any.
  // pub fn eval_term_of(
  //   & self, pred: PrdIdx, model: & VarMap<Val>
  // ) -> Res< Option<bool> > {
  //   if let Some(term) = self.term_of(pred) {
  //     match term.bool_eval(model) {
  //       Ok(None) => bail!("partial model during predicate term evaluation"),
  //       res => res,
  //     }
  //   } else {
  //     Ok(None)
  //   }
  // }

  /// Set of int constants **appearing in the predicates**. If more constants
  /// are created after the instance building step, they will not appear here.
  pub fn consts(& self) -> & HConSet<RTerm> {
    & self.consts
  }

  /// Range over the predicate indices.
  pub fn pred_indices(& self) -> PrdRange {
    PrdRange::zero_to( self.preds.len() )
  }

  /// Predicate accessor.
  pub fn preds(& self) -> & PrdMap<PrdInfo> {
    & self.preds
  }
  /// Clause accessor.
  pub fn clauses(& self) -> & ClsMap<Clause> {
    & self.clauses
  }

  /// Pushes a new predicate and returns its index.
  pub fn push_pred(
    & mut self, name: String, sig: VarMap<Typ>
  ) -> PrdIdx {
    self.max_pred_arity = ::std::cmp::max(
      self.max_pred_arity, sig.len().into()
    ) ;
    let idx = self.preds.next_index() ;
    self.preds.push( PrdInfo { name, idx, sig } ) ;
    self.pred_terms.push(None) ;
    self.pred_to_clauses.push(
      ( ClsSet::with_capacity(17), ClsSet::with_capacity(17) )
    ) ;
    idx
  }

  /// Forces a predicate to be equal to something.
  ///
  /// Does not impact `pred_to_clauses`.
  pub fn force_pred(& mut self, pred: PrdIdx, terms: Vec<TTerm>) -> Res<()> {
    if let Some(ts) = self.pred_terms[pred].as_ref() {
      if ts != & terms {
        bail!(
          "[bug] trying to force predicate {} twice",
          conf.sad(& self[pred].name)
        )
      }
    }
    self.pred_terms[pred] = Some(terms) ;
    Ok(())
  }

  /// Unlinks a predicate from all the clauses it's linked to, and conversely.
  fn drain_unlink_pred(
    & mut self, pred: PrdIdx, lhs: & mut ClsSet, rhs: & mut ClsSet
  ) -> () {
    for clause in self.pred_to_clauses[pred].0.drain() {
      let was_there = self.clause_to_preds[clause].0.remove(& pred) ;
      debug_assert!( was_there ) ;
      let _ = lhs.insert(clause) ;
    }
    for clause in self.pred_to_clauses[pred].1.drain() {
      debug_assert_eq!( self.clause_to_preds[clause].1, Some(pred) ) ;
      self.clause_to_preds[clause].1 = None ;
      let _ = rhs.insert(clause) ;
    }
  }

  /// Goes trough the predicates in `from`, and updates `pred_to_clauses` so
  /// that they point to `to` instead.
  ///
  /// - swaps `clause_to_preds[from]` and `clause_to_preds[to]`
  /// - only legal if `clause_to_preds[to].0.is_empty()` and
  ///   `clause_to_preds[to].1.is_none()`
  fn relink_preds_to_clauses(
    & mut self, from: ClsIdx, to: ClsIdx
  ) -> Res<()> {
    let mut _set = if_not_bench!{
      // This set remembers the predicates removed. The first `debug_assert`
      // consistency check below fails when a predicate appears more than
      // once in the lhs. Hence the set.
      then { PrdSet::new() } else { () }
    } ;
    if ! self.clause_to_preds[to].0.is_empty() {
      bail!("illegal relinking, clause `{}` still has lhs links", to)
    }
    if self.clause_to_preds[to].1.is_some() {
      bail!("illegal relinking, clause `{}` is still has an rhs link", to)
    }
    self.clause_to_preds.swap(from, to) ;
    for lhs in self.clauses[from].lhs() {
      if let TTerm::P { pred, .. } = * lhs {
        let _already_rmed = if_not_bench!{
          then { ! _set.insert(pred) } else { true }
        } ;
        let was_there = self.pred_to_clauses[pred].0.remove(& from) ;
        let _ = self.pred_to_clauses[pred].0.insert(to) ;
        debug_assert!({ was_there || _already_rmed } )
      }
    }
    if let TTerm::P { pred, .. } = * self.clauses[from].rhs() {
      let was_there = self.pred_to_clauses[pred].1.remove(& from) ;
      let _ = self.pred_to_clauses[pred].1.insert(to) ;
      debug_assert!(was_there)
    }
    Ok(())
  }

  // /// Unlinks a predicate from a clause.
  // fn unlink_pred_and_clause(
  //   & mut self, pred: PrdIdx, clause: ClsIdx
  // ) -> Res<()> {
  //   let in_lhs = self.pred_to_clauses[pred].0.remove(& clause) ;
  //   let in_rhs = self.pred_to_clauses[pred].1.remove(& clause) ;
  //   if ! (in_lhs && in_rhs ) {
  //     bail!(
  //       "predicate {} is not linked to clause number {}, failed to unlink",
  //       conf.sad(& self[pred].name), clause
  //     )
  //   } else {
  //     Ok(())
  //   }
  // }

  /// Forget some clauses.
  fn forget_clauses(& mut self, mut clauses: Vec<ClsIdx>) -> Res<()> {
    // Forgetting is done by swap remove, so we sort in DESCENDING order so
    // that indices always make sense.
    clauses.sort_unstable_by(
      |c_1, c_2| c_2.cmp(c_1)
    ) ;
    for clause in clauses {
      let _ = self.forget_clause(clause) ? ;
    }
    self.check("after `forget_clause`") ? ;
    Ok(())
  }

  /// Forget a clause. **Does not preserve the order of the clauses.**
  ///
  /// Also unlinks predicates from `pred_to_clauses`.
  fn forget_clause(& mut self, clause: ClsIdx) -> Res<Clause> {
    // Remove all links from the clause's predicates to this clause.
    let mut _set = if_not_bench!{
      // This set remembers the predicates removed. The first `debug_assert`
      // consistency check below fails when a predicate appears more than
      // once in the lhs. Hence the set.
      then { PrdSet::new() } else { () }
    } ;
    for lhs in self.clauses[clause].lhs() {
      if let TTerm::P { pred, .. } = * lhs {
        let _already_rmed = if_not_bench!{
          then { ! _set.insert(pred) } else { true }
        } ;
        let was_there = self.pred_to_clauses[pred].0.remove(& clause) ;
        debug_assert!(
          was_there || _already_rmed || self.pred_terms[pred].is_some()
        ) ;
        let was_there = self.clause_to_preds[clause].0.remove(& pred) ;
        debug_assert!(
          was_there || _already_rmed || self.pred_terms[pred].is_some()
        )
      }
    }
    if let TTerm::P { pred, .. } = * self.clauses[clause].rhs() {
      let was_there = self.pred_to_clauses[pred].1.remove(& clause) ;
      debug_assert!(
        was_there || self.pred_terms[pred].is_some()
      ) ;
      debug_assert!(
        self.clause_to_preds[clause].1 == Some(pred) ||
        self.pred_terms[pred].is_some()
      ) ;
      self.clause_to_preds[clause].1 = None
    }
    // Relink the last clause as its index is going to be `clause`. Except if
    // `clause` is already the last one.
    let last_clause: ClsIdx = ( self.clauses.len() - 1 ).into() ;
    if clause != last_clause {
      self.relink_preds_to_clauses(last_clause, clause) ?
    }
    let res = self.clauses.swap_remove(clause) ;
    // self.check("forgetting clause") ? ;
    Ok(res)
  }

  /// Pushes a new clause.
  fn push_clause(& mut self, clause: Clause) -> Res<()> {
    let clause_index = self.clauses.next_index() ;
    let mut lhs_preds = PrdSet::with_capacity( clause.lhs.len() ) ;
    let mut rhs_pred = None ;
    for lhs in clause.lhs() {
      if let Some(pred) = lhs.pred() {
        let _ = self.pred_to_clauses[pred].0.insert(clause_index) ;
        let _ = lhs_preds.insert(pred) ;
      }
    }
    if let Some(pred) = clause.rhs.pred() {
      rhs_pred = Some(pred) ;
      let _ = self.pred_to_clauses[pred].1.insert(clause_index) ;
    }
    self.clause_to_preds.push( (lhs_preds, rhs_pred) ) ;
    self.clauses.push(clause) ;
    self.check("after `push_clause`")
  }

  /// Creates a variable.
  pub fn var(& self, v: VarIdx) -> Term {
    self.factory.mk( RTerm::Var(v) )
  }
  /// Creates a constant.
  pub fn int<I: Into<Int>>(& self, i: I) -> Term {
    self.factory.mk(
      RTerm::Int( i.into() )
    )
  }
  /// Creates the constant `0`.
  pub fn zero(& self) -> Term {
    self.int( Int::zero() )
  }
  /// Creates the constant `1`.
  pub fn one(& self) -> Term {
    self.int( Int::one() )
  }
  /// Creates a boolean.
  pub fn bool(& self, b: bool) -> Term {
    self.factory.mk( RTerm::Bool(b) )
  }
  /// Creates an operator application.
  pub fn op(& self, op: Op, args: Vec<Term>) -> Term {
    op.simplify(self, args)
  }

  /// Creates a less than or equal to.
  pub fn le(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Op::Le, vec![lhs, rhs])
  }
  /// Creates a less than.
  pub fn lt(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Op::Lt, vec![lhs, rhs])
  }
  /// Creates a greater than.
  pub fn gt(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Op::Gt, vec![lhs, rhs])
  }
  /// Creates a greater than or equal to.
  pub fn ge(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Op::Ge, vec![lhs, rhs])
  }

  /// Creates an equality.
  pub fn eq(& self, lhs: Term, rhs: Term) -> Term {
    self.op(Op::Eql, vec![lhs, rhs])
  }

  /// Simplifies the clauses.
  ///
  /// - propagates variable equalities in clauses' lhs
  ///
  /// # TO DO
  ///
  /// - currently kind of assumes equalities are binary, fix?
  pub fn simplify_clauses(& mut self) -> Res<()> {
    // Used to detect cycles in variable equalities.
    let mut cycle_set = VarSet::with_capacity( 29 ) ;
    // Stores equalities between variables.
    let mut var_map = VarHMap::with_capacity( 29 ) ;
    // Stores equalities between representatives and constants.
    let mut rep_cst_map = VarHMap::with_capacity( 29 ) ;
    // Stores equalities between variables and terms.
    let mut var_term_map = VarHMap::with_capacity( 29 ) ;

    // Clauses to remove at the end.
    let mut clauses_to_rm = vec![] ;
    // Terms to add the current clause's lhs.
    let mut terms_to_add = vec![] ;

    let mut stable_var_map: VarHMap<Term> = VarHMap::with_capacity(29) ;
    let mut last_stable_var_map = VarHMap::with_capacity(29) ;

    'clause_iter: for clause_index in ClsRange::zero_to( self.clauses.len() ) {
      let clause = & mut self.clauses[clause_index] ;

      var_map.clear() ;
      rep_cst_map.clear() ;
      var_term_map.clear() ;

      // log_info!{ "working on a clause" }
      // println!(
      //   "looking at clause\n{}", clause.to_string_info(& self.preds) ?
      // ) ;

      // log_info!{ "  iterating on lhs" }

      // Find equalities and add to map.
      //
      // Iterating with a counter so that we can remove terms on the fly with
      // `swap_remove`.
      let mut cnt = 0 ;
      'lhs_iter: while cnt < clause.lhs.len() {
        let current = cnt ;
        cnt += 1 ; // Incrementing because moving on is done via `continue`.

        match clause.lhs[current] {
          TTerm::T(ref term) => match * term.get() {
            RTerm::App { op: Op::Eql, ref args } => {
              debug_assert!( args.len() >= 2 ) ;

              match (
                args[0].var_idx(), args[1].var_idx(),
                args[0].int_val(), args[1].int_val(),
              ) {

                ( Some(lhs_var), Some(rhs_var), _, _ ) => match (
                  var_map.get(& lhs_var).map(|idx| * idx),
                  var_map.get(& rhs_var).map(|idx| * idx),
                ) {
                  ( Some(lhs_rep), Some(rhs_rep) ) => {
                    if lhs_rep != rhs_rep {
                      let _ = var_map.insert(lhs_rep, rhs_rep) ;
                      let _prev = var_map.insert(lhs_var, rhs_rep) ;
                      debug_assert!( _prev.is_some() )
                    }
                  },
                  ( Some(lhs_rep), None ) => {
                    let _prev = var_map.insert(rhs_var, lhs_rep) ;
                    debug_assert!( _prev.is_none() )
                  },
                  ( None, Some(rhs_rep) ) => {
                    let _prev = var_map.insert(lhs_var, rhs_rep) ;
                    debug_assert!( _prev.is_none() )
                  },
                  ( None, None ) => {
                    let _prev = var_map.insert(lhs_var, rhs_var) ;
                    debug_assert!( _prev.is_none() )
                  },
                },

                ( Some(var), _, _, Some(int) ) |
                ( _, Some(var), Some(int), _ ) => {
                  let var = if let Some(rep) = var_map.get(& var) {
                    * rep
                  } else {
                    var
                  } ;
                  let prev = rep_cst_map.insert(
                    var, self.factory.mk( RTerm::Int(int.clone()) )
                  ) ;
                  if let Some(prev) = prev {
                    if prev.int_val().unwrap() != int {
                      clauses_to_rm.push(clause_index) ;
                      continue 'clause_iter
                    }
                  }
                },

                ( Some(var), _, _, _ ) => {
                  // log_info!{
                  //   "{}", term.to_string_info( clause.vars() ) ?
                  // }
                  let term = args[1].clone() ;
                  if let Some(prev) = var_term_map.insert(var, term) {
                    if prev != args[1] {
                      terms_to_add.push(
                        TTerm::T(
                          self.factory.mk(
                            RTerm::App {
                              op: Op::Eql, args: vec![ args[1].clone(), prev ]
                            }
                          )
                        )
                      )
                    }
                  }
                },
                ( _, Some(var), _, _ ) => {
                  let term = args[0].clone() ;
                  if let Some(prev) = var_term_map.insert(var, term) {
                    if prev != args[0] {
                      terms_to_add.push(
                        TTerm::T(
                          self.factory.mk(
                            RTerm::App {
                              op: Op::Eql, args: vec![ args[0].clone(), prev ]
                            }
                          )
                        )
                      )
                    }
                  }
                },
                _ => continue 'lhs_iter,
              }

            },
            _ => continue 'lhs_iter,
          },
          _ => continue 'lhs_iter,
        }

        // Only reachable if the top term was an equality we're gonna
        // propagate.
        clause.lhs.swap_remove(current) ;
        cnt = current // <- we just swap removed, need to backtrack counter
        // * tterm = TTerm::T( self.factory.mk( RTerm::Bool(true) ) )
      }

      use std::iter::Extend ;
      clause.lhs.extend( terms_to_add.drain(0..) ) ;

      // log_info!{ " \n  stabilizing var_map" }

      stable_var_map.clear() ;
      last_stable_var_map.clear() ;

      'stabilize: for (var, rep) in & var_map {
        if stable_var_map.contains_key(var) { continue }
        cycle_set.clear() ;

        let mut cst = rep_cst_map.remove(var) ;
        let mut trm = var_term_map.remove(var) ;

        let (var, mut rep) = (* var, * rep) ;
        // log_info!{ "  {}", clause.vars()[var] }

        let _ = cycle_set.insert(var) ;

        let mut rep_term = loop {
          // log_info!{ "  -> {}", clause.vars()[rep] }
          if let Some(nu_cst) = rep_cst_map.remove(& rep) {
            if let Some(ref cst) = cst {
              if cst != & nu_cst {
                clauses_to_rm.push(clause_index) ;
                continue 'clause_iter
              }
            } else {
              cst = Some(nu_cst)
            }
          }

          if let Some(nu_trm) = var_term_map.remove(& rep) {
            if let Some(ref trm) = trm {
              if * trm != nu_trm {
                clause.lhs.push(
                  TTerm::T(
                    self.factory.mk(
                      RTerm::App {
                        op: Op::Eql, args: vec![
                          nu_trm, trm.clone()
                        ]
                      }
                    )
                  )
                )
              }
            } else {
              trm = Some(nu_trm)
            }
          }

          if let Some(rep_term) = stable_var_map.get(& rep) {
            // Bonafide representative.
            break rep_term.clone()
          } else if let Some(nu_rep) = var_map.get(& rep) {
            cycle_set.insert(rep) ;
            if cycle_set.contains(& nu_rep) {
              // Cycle, we make `nu_rep` the representative and we done.
              cycle_set.remove(nu_rep) ;
              break self.factory.mk( RTerm::Var(* nu_rep) )
            } else {
              // Following equivalence relation.
              rep = * nu_rep
            }
          } else {
            // Reached the top-most representative.
            break self.factory.mk( RTerm::Var(rep) )
          }
        } ;


        if let Some(cst_term) = cst {
          if let Some(trm) = trm {
            if cst_term != trm {
              clause.lhs.push(
                TTerm::T(
                  self.factory.mk(
                    RTerm::App {
                      op: Op::Eql, args: vec![ cst_term.clone(), trm.clone() ]
                    }
                  )
                )
              )
            }
          }
          if let Some(rep) = rep_term.var_idx() {
            for (_, other_rep) in stable_var_map.iter_mut() {
              if * other_rep == rep_term {
                * other_rep = cst_term.clone()
              }
            }
            cycle_set.insert(rep) ;
          }
          rep_term = cst_term
        } else if let Some(trm) = trm {
          if let Some(rep) = rep_term.var_idx() {
            for (_, other_rep) in stable_var_map.iter_mut() {
              if * other_rep == rep_term {
                * other_rep = trm.clone()
              }
            }
            cycle_set.insert(rep) ;
          }
          // log_info!{ "  => {}", trm.to_string_info( clause.vars() ) ? }
          rep_term = trm.clone()
        } else if let Some(rep) = rep_term.var_idx() {
          // Avoid cycles.
          if cycle_set.contains(& rep) {
            cycle_set.remove(& rep) ;
          }
        }

        // log_info!{ "  => {}", rep_term.to_string_info( clause.vars() ) ? }

        for var in cycle_set.drain() {
          // log_info!{
          //   "    {} -> {}",
          //   clause.vars()[var],
          //   rep_term.to_string_info( clause.vars() ) ?
          // }
          let _prev = stable_var_map.insert(var, rep_term.clone()) ;
          debug_assert!( _prev.is_none() )
        }
      }

      // log_info!{ " \n  stabilized map {{" }
      // for (var, rep) in & stable_var_map {
      //   log_info!{
      //     "    {} -> {}",
      //     clause.vars()[* var],
      //     rep.to_string_info( clause.vars() ) ?
      //   }
      // }
      // log_info!{ "  }}" }

      for (var, term) in & stable_var_map {
        // log_info!{ "1" }
        let term = self.factory.subst_fp(
          & var_term_map, & term
        ).0 ;
        // log_info!{ "2" }
        let term = self.factory.subst_fp(
          & rep_cst_map, & term
        ).0 ;
        // log_info!{ "3" }
        let term = self.factory.subst_fp(
          & stable_var_map, & term
        ).0 ;
        let _prev = last_stable_var_map.insert(
          * var, term
        ) ;
        debug_assert!( _prev.is_none() )
      }
      for (var, term) in & var_term_map {
        // log_info!{ "4" }
        let term = self.factory.subst_fp(
          & rep_cst_map, & term
        ).0 ;
        // log_info!{ "5" }
        let term = self.factory.subst_fp(
          & var_term_map, & term
        ).0 ;
        // log_info!{ "6" }
        let term = self.factory.subst_fp(
          & rep_cst_map, & term
        ).0 ;
        // log_info!{ "7" }
        let term = self.factory.subst_fp(
          & stable_var_map, & term
        ).0 ;
        let _prev = last_stable_var_map.insert(* var, term) ;
        debug_assert!( _prev.is_none() )
      }
      for (var, int) in rep_cst_map.drain() {
        let _prev = last_stable_var_map.insert(var, int) ;
        debug_assert!( _prev.is_none() )
      }

      // log_info!{ " \n  stabilized map {{" }
      // for (var, rep) in & last_stable_var_map {
      //   log_info!{
      //     "    {} -> {}",
      //     clause.vars()[* var],
      //     rep.to_string_info( clause.vars() ) ?
      //   }
      // }
      // log_info!{ "  }}" }

      use mylib::coll::* ;
      for tterm in clause.lhs.iter_mut().chain_one(& mut clause.rhs) {
        self.factory.tterm_subst(& last_stable_var_map, tterm)
      }

      // Counter for swap remove in lhs.
      let mut cnt = 0 ;
      'lhs_subst: while cnt < clause.lhs.len() {
        self.factory.tterm_subst(
          & last_stable_var_map, & mut clause.lhs[cnt]
        ) ;
        match clause.lhs[cnt].bool() {
          Some(true) => {
            let _ = clause.lhs.swap_remove(cnt) ;
            ()
          },
          Some(false) => {
            clauses_to_rm.push(clause_index) ;
            continue 'clause_iter
          },
          None => cnt += 1,
        }
      }

      self.factory.tterm_subst(& last_stable_var_map, & mut clause.rhs) ;
      match clause.rhs.bool() {
        Some(true) => {
          clauses_to_rm.push(clause_index) ;
          continue 'clause_iter
        },
        Some(false) => clause.rhs = TTerm::T(
          self.factory.mk( RTerm::Bool(false) )
        ),
        None => (),
      }

    }

    self.forget_clauses( clauses_to_rm ) ? ;

    Ok(())
  }

  /// Extracts some qualifiers from all clauses.
  pub fn qualifiers(& self) -> HConSet<RTerm> {
    let mut set = HConSet::new() ;
    for clause in & self.clauses {
      self.qualifiers_of_clause(clause, & mut set)
    }
    set
  }

  /// Extracts some qualifiers from a clause.
  ///
  /// # TO DO
  ///
  /// - write an explanation of what actually happens
  /// - and some tests, probably
  pub fn qualifiers_of_clause(
    & self, clause: & Clause, quals: & mut HConSet<RTerm>
  ) {
    use mylib::coll::* ;

    // println!(
    //   "looking at clause {}", clause.to_string_info(self.preds()).unwrap()
    // ) ;

    // Extraction of the variables map based on the way the predicates are
    // used.
    let mut maps = vec![] ;

    for tterm in clause.lhs().iter().chain_one( clause.rhs() ) {
      match * tterm {
        
        TTerm::P { ref args, .. } => {
          // All the *clause var* to *pred var* maps for this predicate
          // application.
          let mut these_maps = vec![ VarHMap::with_capacity( args.len() ) ] ;

          for (pred_var_index, term) in args.index_iter() {
            if let Some(clause_var_index) = term.var_idx() {
              // Stores the new maps to add in case a clause variable is bound
              // several times.
              let mut to_add = vec![] ;
              for map in & mut these_maps {
                if map.contains_key(& clause_var_index) {
                  // Current clause variable is already bound in this map,
                  // clone it, change the binding, and remember to add it
                  // later.
                  let mut map = map.clone() ;
                  let _ = map.insert(
                    clause_var_index, self.var(pred_var_index)
                  ) ;
                  to_add.push(map)
                } else {
                  // Current clause variable not bound in this map, just add
                  // the new binding.
                  let _ = map.insert(
                    clause_var_index, self.var(pred_var_index)
                  ) ;
                }
              }
              use std::iter::Extend ;
              these_maps.extend( to_add )
            }
          }

          for map in these_maps {
            // Push if non-empty.
            if ! map.is_empty() {
              maps.push(map)
            }
          }
        },
        
        _ => ()
      }
    }

    // println!("maps {{") ;
    // for map in & maps {
    //   let mut is_first = true ;
    //   for (idx, term) in map.iter() {
    //     println!("  {} {} -> {}", if is_first {"-"} else {" "}, idx, term) ;
    //     is_first = false
    //   }
    // }
    // println!("}} quals {{") ;

    // Now look for atoms and try to apply the mappings above.
    for tterm in clause.lhs().iter().chain_one( clause.rhs() ) {

      match * tterm {
        TTerm::T(ref term) => for map in & maps {
          if let Some( (term, true) ) = self.subst_total(map, term) {
            let term = if let Some(term) = term.rm_neg() {
              term
            } else { term } ;
            let _ = quals.insert(term) ;
          }
          // else if let Some(kids) = term.kids() {
          //   for kid in kids {
          //     if kid.is_relation() {
          //       if let Some( (term, true) ) = self.subst_total(map, kid) {
          //         log_info!("-> {}", term) ;
          //         let term = if let Some(term) = term.rm_neg() {
          //           term
          //         } else { term } ;
          //         let _ = quals.insert(term) ;
          //       }
          //     }
          //   }
          // }
        },
        _ => ()
      }

    }
    // println!("}}")

  }

  /// Turns a teacher counterexample into learning data.
  pub fn cexs_to_data(
    & self, data: & mut ::common::data::Data, cexs: Cexs
  ) -> Res<()> {

    for (clause, cex) in cexs.into_iter() {
      log_debug!{ "    working on clause {}...", clause }
      let clause = & self[clause] ;
      log_debug!{ "    getting antecedents..." }
      let mut antecedents = Vec::with_capacity( clause.lhs().len() ) ;
      log_debug!{ "    translating tterms..." }


      log_debug!{ "    working on lhs..." }
      for tterm in clause.lhs() {
        match * tterm {
          TTerm::P { pred, ref args } => {
            log_debug!{ "        pred: {} / {} ({})", pred, self.preds.len(), self.pred_terms.len() }
            if self.pred_terms[pred].is_none() {
              log_debug!{ "        -> is none" }
              let mut values = VarMap::with_capacity( args.len() ) ;
              for arg in args {
                values.push(
                  arg.eval(& cex).chain_err(
                    || "during argument evaluation to generate learning data"
                  ) ?
                )
              }
              antecedents.push(
                (pred, values)
              )
            } else {
              log_debug!{ "      -> is some" }
            }
          },
          _ => (),
        }
      }
      antecedents.shrink_to_fit() ;
      
      log_debug!{ "    working on rhs..." }
      let consequent = match * clause.rhs() {
        TTerm::P { pred, ref args } => {
          log_debug!{ "        pred: {} / {} ({})", pred, self.preds.len(), self.pred_terms.len() }
          let mut values = VarMap::with_capacity( args.len() ) ;
          'pred_args: for arg in args {
            values.push(
              arg.eval(& cex).chain_err(
                || "during argument evaluation to generate learning data"
              ) ?
            )
          }
          Some( (pred, values) )
        },
        _ => None,
      } ;

      log_debug!{ "    antecedent: {:?}", antecedents }
      log_debug!{ "    consequent: {:?}", consequent }

      match ( antecedents.len(), consequent ) {
        (0, None) => bail!(
          "[unimplemented] clause with no predicate has a cex (unsafe)"
        ),
        (1, None) => {
          let (pred, args) = antecedents.pop().unwrap() ;
          data.stage_raw_neg(pred, args) ?
        },
        (0, Some( (pred, args) )) => data.stage_raw_pos(pred, args) ?,
        (_, consequent) => data.add_cstr(antecedents, consequent) ?,
      }
    }

    Ok(())
  }



  /// Checks that the instance has no inconsistencies.
  ///
  /// Only active in debug.
  #[cfg(not(debug_assertions))]
  #[inline(always)]
  pub fn check(& self, _: & 'static str) -> Res<()> { Ok(()) }

  #[cfg(debug_assertions)]
  pub fn check(& self, s: & 'static str) -> Res<()> {
    self.check_pred_to_clauses().chain_err(
      || format!("while checking `{}`", conf.sad("pred_to_clauses"))
    ).chain_err(
      || format!("instance consistency check failed: {}", conf.emph(s))
    ) ? ;

    self.check_clause_to_preds().chain_err(
      || format!("while checking `{}`", conf.sad("clause_to_preds"))
    ).chain_err(
      || format!("instance consistency check failed: {}", conf.emph(s))
    ) ? ;
    Ok(())
  }

  /// Pretty printer for a set of predicates.
  fn pretty_preds(& self, preds: & PrdSet) -> String {
    let mut s = String::new() ;
    s.push('{') ;
    for pred in preds {
      s.push(' ') ;
      s.push_str(& self[* pred].name)
    }
    s.push(' ') ;
    s.push('}') ;
    s
  }

  /// Pretty printer for a predicate option.
  fn pretty_pred_opt(& self, pred: & Option<PrdIdx>) -> String {
    if let Some(pred) = * pred {
      format!("{}", self[pred].name)
    } else {
      "none".into()
    }
  }

  /// Pretty printer for a set of clauses.
  fn pretty_clauses(& self, clauses: & ClsSet) -> String {
    let mut s = String::new() ;
    s.push('{') ;
    for clause in clauses {
      s.push(' ') ;
      s.push_str(& format!("{}", clause))
    }
    s.push(' ') ;
    s.push('}') ;
    s
  }

  /// Checks the consistency of `pred_to_clauses`.
  fn check_pred_to_clauses(& self) -> Res<()> {
    for (cls_idx, clause) in self.clauses.index_iter() {
      for lhs in clause.lhs() {
        if let Some(pred) = lhs.pred() {
          if ! self.pred_to_clauses[pred].0.contains(& cls_idx) {
            bail!(
              "predicate {} appears in lhs of clause {} \
              but is not registered as such\n{}\nlhs: {}\nrhs: {}",
              self[pred], cls_idx,
              self.clauses[cls_idx].to_string_info(self.preds()) ?,
              self.pretty_clauses(
                & self.pred_to_clauses[pred].0
              ), self.pretty_clauses(
                & self.pred_to_clauses[pred].1
              )
            )
          }
        }
      }
      if let Some(pred) = clause.rhs.pred() {
        if ! self.pred_to_clauses[pred].1.contains(& cls_idx) {
          bail!(
            "predicate {} appears in rhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_clauses(
              & self.pred_to_clauses[pred].0
            ), self.pretty_clauses(
              & self.pred_to_clauses[pred].1
            )
          )
        }
      }
    }
    for (pred, & (ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
      'pred_clauses: for clause in lhs {
        for tterm in & self.clauses[* clause].lhs {
          if let Some(this_pred) = tterm.pred() {
            if this_pred == pred {
              continue 'pred_clauses
            }
          }
        }
        bail!(
          "predicate {} is registered as appearing in lhs of clause {} \
          but it's not the case\n{}\nlhs: {}\nrhs: {}",
          self[pred], clause,
          self.clauses[* clause].to_string_info(self.preds()) ?,
          self.pretty_clauses(
            & self.pred_to_clauses[pred].0
          ), self.pretty_clauses(
            & self.pred_to_clauses[pred].1
          )
        )
      }
      for clause in rhs {
        if let Some(this_pred) = self.clauses[* clause].rhs.pred() {
          if this_pred == pred {
            continue
          }
        }
        bail!(
          "predicate {} is registered to appear in rhs of clause {} \
          but it's not the case\n{}\nlhs: {}\nrhs: {}",
          self[pred], clause,
          self.clauses[* clause].to_string_info(self.preds()) ?,
          self.pretty_clauses(
            & self.pred_to_clauses[pred].0
          ), self.pretty_clauses(
            & self.pred_to_clauses[pred].1
          )
        )
      }
    }
    Ok(())
  }

  /// Checks the consistency of `clause_to_preds`.
  fn check_clause_to_preds(& self) -> Res<()> {
    for (cls_idx, clause) in self.clauses.index_iter() {
      for lhs in clause.lhs() {
        if let Some(pred) = lhs.pred() {
          if ! self.clause_to_preds[cls_idx].0.contains(& pred) {
            bail!(
              "predicate {} appears in lhs of clause {} \
              but is not registered as such\n{}\nlhs: {}\nrhs: {}",
              self[pred], cls_idx,
              self.clauses[cls_idx].to_string_info(self.preds()) ?,
              self.pretty_preds(
                & self.clause_to_preds[cls_idx].0
              ), self.pretty_pred_opt(
                & self.clause_to_preds[cls_idx].1
              )
            )
          }
        }
      }
      if let Some(pred) = clause.rhs.pred() {
        if self.clause_to_preds[cls_idx].1 != Some(pred) {
          bail!(
            "predicate {} appears in rhs of clause {} \
            but is not registered as such\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_preds(
              & self.clause_to_preds[cls_idx].0
            ), self.pretty_pred_opt(
              & self.clause_to_preds[cls_idx].1
            )
          )
        }
      }
    }
    for (cls_idx, & (ref lhs, ref rhs)) in self.clause_to_preds.index_iter() {
      'pred_clauses: for pred in lhs {
        for tterm in & self.clauses[cls_idx].lhs {
          if let Some(this_pred) = tterm.pred() {
            if this_pred == * pred {
              continue 'pred_clauses
            }
          }
        }
        bail!(
          "predicate {} is registered to appear in lhs of clause {} \
          but it's not the case\n{}\nlhs: {}\nrhs: {}",
          self[* pred], cls_idx,
          self.clauses[cls_idx].to_string_info(self.preds()) ?,
          self.pretty_preds(
            & self.clause_to_preds[cls_idx].0
          ), self.pretty_pred_opt(
            & self.clause_to_preds[cls_idx].1
          )
        )
      }
      if let Some(pred) = * rhs {
        if self.clauses[cls_idx].rhs.pred() != Some(pred) {
          bail!(
            "predicate {} is registered to appear in rhs of clause {} \
            but it's not the case\n{}\nlhs: {}\nrhs: {}",
            self[pred], cls_idx,
            self.clauses[cls_idx].to_string_info(self.preds()) ?,
            self.pretty_preds(
              & self.clause_to_preds[cls_idx].0
            ), self.pretty_pred_opt(
              & self.clause_to_preds[cls_idx].1
            )
          )
        }
      }
    }
    Ok(())
  }
}
impl ::std::ops::Index<ClsIdx> for Instance {
  type Output = Clause ;
  fn index(& self, index: ClsIdx) -> & Clause {
    & self.clauses[index]
  }
}
impl ::std::ops::Index<PrdIdx> for Instance {
  type Output = PrdInfo ;
  fn index(& self, index: PrdIdx) -> & PrdInfo {
    & self.preds[index]
  }
}












/// Operators.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Op {
  /// Addition.
  Add,
  /// Subtraction.
  Sub,
  /// Multiplication.
  Mul,
  /// Division.
  Div,
  /// Modulo.
  Mod,
  /// Greater than.
  Gt,
  /// Greater than or equal to.
  Ge,
  /// Less than or equal to.
  Le,
  /// Less than.
  Lt,
  /// Implication.
  Impl,
  /// Equal to.
  Eql,
  /// Negation.
  Not,
  /// Conjunction.
  And,
  /// Disjunction.
  Or,
}
impl Op {
  /// String representation.
  pub fn as_str(& self) -> & str {
    use instance::Op::* ;
    match * self {
      Add => "+", Sub => "-", Mul => "*", Div => "div", Mod => "mod",
      Gt => ">", Ge => ">=", Le => "<=", Lt => "<", Eql => "=",
      Not => "not", And => "and", Or => "or", Impl => "=>",
    }
  }

  /// Tries to simplify an operator application.
  ///
  /// # Nullary / unary applications of `And` and `Or`
  ///
  /// ```
  /// # use hoice_lib::instance::* ;
  /// let instance = & Instance::mk(10, 10, 10) ;
  ///
  /// let tru = instance.bool(true) ;
  /// let fls = instance.bool(false) ;
  /// let var_1 = instance.var( 7.into() ) ;
  /// let var_2 = instance.var( 2.into() ) ;
  ///
  /// assert_eq!( fls, Op::And.simplify(instance, vec![]) ) ;
  /// assert_eq!( tru, Op::Or.simplify(instance, vec![]) ) ;
  /// assert_eq!( var_2, Op::And.simplify(instance, vec![ var_2.clone() ]) ) ;
  /// assert_eq!( var_1, Op::Or.simplify(instance, vec![ var_1.clone() ]) ) ;
  ///
  /// let and = instance.op(Op::And, vec![ var_2.clone(), var_1.clone() ]) ;
  /// assert_eq!(
  ///   and, Op::And.simplify(instance, vec![ var_2.clone(), var_1.clone() ])
  /// ) ;
  /// let or = instance.op(Op::Or, vec![ var_2.clone(), var_1.clone() ]) ;
  /// assert_eq!(
  ///   or, Op::Or.simplify(instance, vec![ var_2.clone(), var_1.clone() ])
  /// ) ;
  /// ```
  ///
  /// # Double negations
  ///
  /// ```
  /// # use hoice_lib::instance::* ;
  /// let instance = & Instance::mk(10, 10, 10) ;
  ///
  /// let var_1 = instance.var( 7.into() ) ;
  /// let n_var_1 = instance.op( Op::Not, vec![ var_1.clone() ] ) ;
  /// assert_eq!( var_1, Op::Not.simplify(instance, vec![ n_var_1 ]) ) ;
  ///
  /// let var_1 = instance.var( 7.into() ) ;
  /// let n_var_1 = instance.op( Op::Not, vec![ var_1.clone() ] ) ;
  /// assert_eq!( n_var_1, Op::Not.simplify(instance, vec![ var_1 ]) ) ;
  /// ```
  pub fn simplify(
    self, instance: & Instance, mut args: Vec<Term>
  ) -> Term {
    let (op, args) = match self {
      Op::And => if args.is_empty() {
        return instance.bool(false)
      } else if args.len() == 1 {
        return args.pop().unwrap()
      } else {
        (self, args)
      },
      Op::Or => if args.is_empty() {
        return instance.bool(true)
      } else if args.len() == 1 {
        return args.pop().unwrap()
      } else {
        (self, args)
      },
      Op::Not => {
        assert!( args.len() == 1 ) ;
        match * args[0] {
          RTerm::App { op: Op::Not, ref args } => {
            return args[0].clone()
          },
          _ => (),
        }
        (self, args)
      },
      Op::Add => {
        let mut cnt = 0 ;
        let mut zero = None ;
        'remove_zeros: while cnt < args.len() {
          if let Some(int) = args[0].int_val() {
            if int.is_zero() {
              zero = Some( args.swap_remove(cnt) ) ;
              continue 'remove_zeros
            }
          }
          cnt += 1
        }
        if args.len() == 0 {
          return zero.expect("trying to construct an empty application")
        } else if args.len() == 1 {
          return args.pop().unwrap()
        } else {
          (self, args)
        }
      },
      // Op::Gt => if args.len() != 2 {
      //   panic!( "[bug] operator `>` applied to {} operands", args.len() )
      // } else {
      //   if let Some( i ) = args[0].int_val() {
      //     // Checks whether it's zero before decreasing.
      //     if i.is_zero() {
      //       // Args is unchanged, term is equivalent to false anyway.
      //       (Op::Ge, args)
      //     } else {
      //       args[0] = instance.int(i - Int::one()) ;
      //       (Op::Ge, args)
      //     }
      //   } else if let Some( i ) = args[1].int_val() {
      //     args[1] = instance.int(i + Int::one()) ;
      //     (Op::Ge, args)
      //   } else {
      //     (self, args)
      //   }
      // },
      // Op::Lt => if args.len() != 2 {
      //   panic!( "[bug] operator `<` applied to {} operands", args.len() )
      // } else {
      //   if let Some( i ) = args[0].int_val() {
      //     args[0] = instance.int(i + Int::one()) ;
      //     (Op::Le, args)
      //   } else if let Some( i ) = args[1].int_val() {
      //     // Checks whether it's zero before decreasing.
      //     if i.is_zero() {
      //       // Args is unchanged, term is equivalent to false anyway.
      //       (Op::Le, args)
      //     } else {
      //       args[1] = instance.int(i - Int::one()) ;
      //       (Op::Le, args)
      //     }
      //   } else {
      //     (self, args)
      //   }
      // },
      _ => (self, args),
    } ;
    instance.factory.mk( RTerm::App { op, args } )
  }

  /// Operator parser.
  #[allow(unused_variables)]
  pub fn parse(
    bytes: & [u8]
  ) -> ::nom::IResult<& [u8], Self, Error> {
    fix_error!(
      bytes,
      Error,
      alt_complete!(
        map!(tag!("+"),   |_| Op::Add ) |
        map!(tag!("-"),   |_| Op::Sub ) |
        map!(tag!("*"),   |_| Op::Mul ) |
        map!(tag!("div"), |_| Op::Div ) |
        map!(tag!("mod"), |_| Op::Mod ) |
        map!(tag!("<="),  |_| Op::Le  ) |
        map!(tag!("<"),   |_| Op::Lt  ) |
        map!(tag!(">="),  |_| Op::Ge  ) |
        map!(tag!(">"),   |_| Op::Gt  ) |
        map!(tag!("=>"),  |_| Op::Impl) |
        map!(tag!("="),   |_| Op::Eql ) |
        map!(tag!("not"), |_| Op::Not ) |
        map!(tag!("and"), |_| Op::And ) |
        map!(tag!("or"),  |_| Op::Or  )
      )
    )
  }


  /// Evaluation.
  pub fn eval(& self, mut args: Vec<Val>) -> Res<Val> {
    use instance::Op::* ;
    if args.is_empty() {
      bail!("evaluating operator on 0 elements")
    }
    match * self {
      Add => {
        let mut res ;
        for_first!{
          args.into_iter() => {
            |fst| res = try_val!(int fst),
            then |nxt| res = res + try_val!(int nxt),
            yild Ok( Val::I(res) )
          } else unreachable!()
        }
      },
      Sub => if args.len() == 1 {
        Ok(
          Val::I(
            - try_val!( int args.pop().unwrap() )
          )
        )
      } else {
        let mut res ;
        for_first!{
          args.into_iter() => {
            |fst| res = try_val!(int fst),
            then |nxt| res = res - try_val!(int nxt),
            yild Ok( Val::I(res) )
          } else unreachable!()
        }
      },
      Mul => {
        let mut res ;
        for_first!{
          args.into_iter() => {
            |fst| res = try_val!(int fst),
            then |nxt| res = res * try_val!(int nxt),
            yild Ok( Val::I(res) )
          } else unreachable!()
        }
      },
      Div => {
        let mut res ;
        for_first!{
          args.into_iter() => {
            |fst| res = try_val!(int fst),
            then |nxt| res = res / try_val!(int nxt),
            yild Ok( Val::I(res) )
          } else unreachable!()
        }
      },
      Mod => if args.len() != 2 {
        bail!(
          format!("evaluating `Div` with {} (!= 2) arguments", args.len())
        )
      } else {
        use num::Integer ;
        let b = try_val!( int args.pop().unwrap() ) ;
        let a = try_val!( int args.pop().unwrap() ) ;
        debug_assert!( args.is_empty() ) ;
        Ok(
          Val::I( a.mod_floor(& b) )
        )
      },

      // Bool operators.

      Gt => {
        let mut last ;
        for_first!{
          args.into_iter() => {
            |fst| last = try_val!(int fst),
            then |nxt| {
              let nxt = try_val!(int nxt) ;
              if last > nxt { last = nxt } else {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },
      Ge => {
        let mut last ;
        for_first!{
          args.into_iter() => {
            |fst| last = try_val!(int fst),
            then |nxt| {
              let nxt = try_val!(int nxt) ;
              if last >= nxt { last = nxt } else {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },
      Le => {
        let mut last ;
        for_first!{
          args.into_iter() => {
            |fst| last = try_val!(int fst),
            then |nxt| {
              let nxt = try_val!(int nxt) ;
              if last <= nxt { last = nxt } else {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },
      Lt => {
        let mut last ;
        for_first!{
          args.into_iter() => {
            |fst| last = try_val!(int fst),
            then |nxt| {
              let nxt = try_val!(int nxt) ;
              if last < nxt { last = nxt } else {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },
      Eql => {
        let mem ;
        for_first!{
          args.into_iter() => {
            |fst| mem = fst,
            then |nxt| {
              if mem != nxt {
                return Ok( Val::B(false) )
              }
            },
            yild Ok( Val::B(true) )
          } else unreachable!()
        }
      },
      Not => if args.len() != 1 {
        bail!(
          format!("evaluating `Not` with {} (!= 1) arguments", args.len())
        )
      } else {
        let b = try_val!( bool args.pop().unwrap() ) ;
        Ok( Val::B(! b) )
      },
      And => {
        let mut unknown = false ;
        for arg in args {
          match arg.to_bool() ? {
            Some(false) => return Ok( Val::B(false) ),
            None => unknown = true,
            _ => ()
          }
        }
        if unknown {
          Ok( Val::N )
        } else {
          Ok( Val::B(true) )
        }
      },
      Or => {
        let mut unknown = false ;
        for arg in args {
          match arg.to_bool() ? {
            Some(true) => return Ok( Val::B(true) ),
            None => unknown = true,
            _ => ()
          }
        }
        if unknown {
          Ok( Val::N )
        } else {
          Ok( Val::B(false) )
        }
      },
      Impl => if args.len() != 2 {
        bail!(
          format!("evaluating `Impl` with {} (!= 2) arguments", args.len())
        )
      } else {
        // Safe because of the check above.
        let rhs = args.pop().unwrap() ;
        let lhs = args.pop().unwrap() ;
        match ( lhs.to_bool() ?, rhs.to_bool() ? ) {
          (_, Some(true)) | (Some(false), _) => Ok( Val::B(true) ),
          (Some(lhs), Some(rhs)) => Ok( Val::B(rhs || ! lhs) ),
          _ => Ok(Val::N),
        }
      },
    }
  }
}
impl_fmt!{
  Op(self, fmt) {
    fmt.write_str( self.as_str() )
  }
}
















impl<'a> PebcakFmt<'a> for RTerm {
  type Info = & 'a VarMap<VarInfo> ;
  fn pebcak_err(& self) -> ErrorKind {
    "during term pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, vars: & 'a VarMap<VarInfo>
  ) -> IoRes<()> {
    self.write(
      w, |w, var| w.write_all( vars[var].as_bytes() )
    )
  }
}

// impl<'a> PebcakFmt<'a> for TTerm {
//   type Info = (& 'a VarMap<VarInfo>, & 'a PrdMap<PrdInfo>) ;
//   fn pebcak_err(& self) -> ErrorKind {
//     "during top term pebcak formatting".into()
//   }
//   fn pebcak_io_fmt<W: Write>(
//     & self, w: & mut W,
//     (vars, prds): (& 'a VarMap<VarInfo>, & 'a PrdMap<PrdInfo>)
//   ) -> IoRes<()> {
//     self.write(
//       w,
//       |w, var| w.write_all( vars[var].as_bytes() ),
//       |w, prd| w.write_all( prds[prd].as_bytes() )
//     )
//   }
// }

impl<'a> PebcakFmt<'a> for Clause {
  type Info = & 'a PrdMap<PrdInfo> ;
  fn pebcak_err(& self) -> ErrorKind {
    "during clause pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, prds: & 'a PrdMap<PrdInfo>
  ) -> IoRes<()> {
    self.write(
      w, |w, prd, args| {
        write!(w, "(") ? ;
        w.write_all( prds[prd].as_bytes() ) ? ;
        for arg in args {
          write!(w, " ") ? ;
          arg.write(w, |w, var| w.write_all( self.vars[var].as_bytes() )) ?
        }
        write!(w, ")")
      }
    )
  }
}

impl<'a> PebcakFmt<'a> for Instance {
  type Info = () ;
  fn pebcak_err(& self) -> ErrorKind {
    "during instance pebcak formatting".into()
  }
  fn pebcak_io_fmt<W: Write>(
    & self, w: & mut W, _: ()
  ) -> IoRes<()> {
    use common::consts::keywords ;

    for (pred_idx, pred) in self.preds.index_iter() {
      if self.pred_terms[pred_idx].is_none() {
        write!(
          w, "({}\n  {}\n  (", keywords::prd_dec, pred.name
        ) ? ;
        for typ in & pred.sig {
          write!(w, " {}", typ) ?
        }
        write!(w, " ) Bool\n)\n") ?
      }
    }

    for pred in & self.sorted_pred_terms {
      write!(w, "({} {}\n  (", keywords::prd_dec, self[* pred]) ? ;
      for (var, typ) in self[* pred].sig.index_iter() {
        write!(w, " (v_{} {})", var, typ) ?
      }
      let tterms = self.pred_terms[* pred].as_ref().unwrap() ;
      write!(w, " ) Bool") ? ;
      if tterms.len() > 1 {
        write!(w, "\n  (and") ?
      }
      for tterm in self.pred_terms[* pred].as_ref().unwrap() {
        write!(w, "\n      {}", tterm) ?
      }
      if tterms.len() > 1 {
        write!(w, "\n  )") ?
      }
      write!(w, "\n  )\n)\n") ?
    }

    for clause in & self.clauses {
      write!(w, "\n") ? ;
      clause.pebcak_io_fmt(w, & self.preds) ?
    }

    write!(w, "\npred to clauses:\n") ? ;
    for (pred, & (ref lhs, ref rhs)) in self.pred_to_clauses.index_iter() {
      write!(w, "  {}: lhs {{", self[pred]) ? ;
      for lhs in lhs {
        write!(w, " {}", lhs) ?
      }
      write!(w, " }}, rhs {{") ? ;
      for rhs in rhs {
        write!(w, " {}", rhs) ?
      }
      write!(w, " }}\n") ?
    }

    Ok(())
  }
}








#[test]
fn simplify() {
  let instance = & Instance::mk(10, 10, 10) ;
  let tru = instance.bool(true) ;
  let fls = instance.bool(false) ;
  let var_1 = instance.var( 7.into() ) ;
  let var_2 = instance.var( 2.into() ) ;

  assert_eq!( fls, Op::And.simplify(instance, vec![]) ) ;
  assert_eq!( tru, Op::Or.simplify(instance, vec![]) ) ;
  assert_eq!( var_2, Op::And.simplify(instance, vec![ var_2.clone() ]) ) ;
  assert_eq!( var_1, Op::Or.simplify(instance, vec![ var_1.clone() ]) ) ;
  let and = instance.op(Op::And, vec![ var_2.clone(), var_1.clone() ]) ;
  assert_eq!(
    and, Op::And.simplify(instance, vec![ var_2.clone(), var_1.clone() ])
  ) ;
  let or = instance.op(Op::Or, vec![ var_2.clone(), and.clone() ]) ;
  assert_eq!(
    or, Op::Or.simplify(instance, vec![ var_2.clone(), and.clone() ])
  ) ;
}





#[cfg(test)]
mod evaluation {
  // use common::* ;
  use instance::* ;

  #[cfg(test)]
  macro_rules! model {
    ( $($values:expr),* ) => (
      $crate::common::VarMap::of(
        vec![ $( $values.into() ),* ]
      )
    ) ;
  }

  #[cfg(test)]
  macro_rules! assert_eval {
    ( int $model:expr => $expr:expr, $value:expr ) => ({
      let res = $expr.eval(& $model).unwrap().to_int().unwrap().unwrap() ;
      println!(
        "{} evaluated with {} is {}, expecting {}", $expr, $model, res, $value
      ) ;
      assert_eq!( res, $value.into() )
    }) ;
    ( bool $model:expr => $expr:expr ) => ({
      let res = $expr.eval(& $model).unwrap().to_bool().unwrap().unwrap() ;
      println!(
        "{} evaluated with {} is {}, expecting true", $expr, $model, res
      ) ;
      assert!( res )
    }) ;
    ( bool not $model:expr => $expr:expr ) => ({
      let res = $expr.eval(& $model).unwrap().to_bool().unwrap().unwrap() ;
      println!(
        "{} evaluated with {} is {}, expecting false", $expr, $model, res
      ) ;
      assert!( ! res )
    }) ;
  }

  /// Just creates an instance.
  fn instance() -> Instance {
    Instance::mk(100, 100, 100)
  }

  #[test]
  fn cst_add() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let sum = instance.op( Op::Add, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      int model => sum, 10
    )
  }

  #[test]
  fn cst_sub_1() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let sub = instance.op( Op::Sub, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      int model => sub, 4
    )
  }

  #[test]
  fn cst_sub_2() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let sub = instance.op( Op::Sub, vec![ c_1 ] ) ;
    let model = model!() ;
    assert_eval!(
      int model => sub, (-7)
    )
  }

  #[test]
  fn cst_mul() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let mul = instance.op( Op::Mul, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      int model => mul, 21
    )
  }

  #[test]
  fn cst_div() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let div = instance.op( Op::Div, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      int model => div, 2
    )
  }

  #[test]
  fn cst_mod() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let m0d = instance.op( Op::Mod, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      int model => m0d, 1
    )
  }

  #[test]
  fn cst_gt_1() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let gt = instance.op( Op::Gt, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => gt
    )
  }

  #[test]
  fn cst_gt_2() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(7) ;
    let gt = instance.op( Op::Gt, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => gt
    )
  }

  #[test]
  fn cst_ge_1() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let ge = instance.op( Op::Ge, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => ge
    )
  }

  #[test]
  fn cst_ge_2() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(7) ;
    let ge = instance.op( Op::Ge, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => ge
    )
  }

  #[test]
  fn cst_le_1() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let le = instance.op( Op::Le, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => le
    )
  }

  #[test]
  fn cst_le_2() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(7) ;
    let le = instance.op( Op::Le, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => le
    )
  }

  #[test]
  fn cst_lt_1() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let lt = instance.op( Op::Lt, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => lt
    )
  }

  #[test]
  fn cst_lt_2() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(7) ;
    let lt = instance.op( Op::Lt, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => lt
    )
  }

  #[test]
  fn cst_eq_1() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(7) ;
    let eq = instance.op( Op::Eql, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => eq
    )
  }

  #[test]
  fn cst_eq_2() {
    let instance = instance() ;
    let c_1 = instance.int(7) ;
    let c_2 = instance.int(3) ;
    let eq = instance.op( Op::Eql, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => eq
    )
  }

  #[test]
  fn cst_eq_3() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let c_2 = instance.bool(true) ;
    let eq = instance.op( Op::Eql, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => eq
    )
  }

  #[test]
  fn cst_eq_4() {
    let instance = instance() ;
    let c_1 = instance.bool(false) ;
    let c_2 = instance.bool(true) ;
    let eq = instance.op( Op::Eql, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => eq
    )
  }

  #[test]
  fn cst_impl_1() {
    let instance = instance() ;
    let c_1 = instance.bool(false) ;
    let c_2 = instance.bool(false) ;
    let imp = instance.op( Op::Impl, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => imp
    )
  }

  #[test]
  fn cst_impl_2() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let c_2 = instance.bool(false) ;
    let imp = instance.op( Op::Impl, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => imp
    )
  }

  #[test]
  fn cst_impl_3() {
    let instance = instance() ;
    let c_1 = instance.bool(false) ;
    let c_2 = instance.bool(true) ;
    let imp = instance.op( Op::Impl, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => imp
    )
  }

  #[test]
  fn cst_impl_4() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let c_2 = instance.bool(true) ;
    let imp = instance.op( Op::Impl, vec![ c_1, c_2 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => imp
    )
  }

  #[test]
  fn cst_not_1() {
    let instance = instance() ;
    let c_1 = instance.bool(false) ;
    let not = instance.op( Op::Not, vec![ c_1 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => not
    )
  }

  #[test]
  fn cst_not_2() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let not = instance.op( Op::Not, vec![ c_1 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => not
    )
  }

  #[test]
  fn cst_and_1() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let c_2 = instance.bool(true) ;
    let c_3 = instance.bool(true) ;
    let c_4 = instance.bool(true) ;
    let and = instance.op( Op::And, vec![ c_1, c_2, c_3, c_4 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => and
    )
  }

  #[test]
  fn cst_and_2() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let c_2 = instance.bool(true) ;
    let c_3 = instance.bool(false) ;
    let c_4 = instance.bool(true) ;
    let and = instance.op( Op::And, vec![ c_1, c_2, c_3, c_4 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => and
    )
  }

  #[test]
  fn cst_and_3() {
    let instance = instance() ;
    let c_1 = instance.bool(false) ;
    let c_2 = instance.bool(true) ;
    let c_3 = instance.bool(true) ;
    let c_4 = instance.bool(true) ;
    let and = instance.op( Op::And, vec![ c_1, c_2, c_3, c_4 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => and
    )
  }

  #[test]
  fn cst_and_4() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let c_2 = instance.bool(false) ;
    let c_3 = instance.bool(false) ;
    let c_4 = instance.bool(true) ;
    let and = instance.op( Op::And, vec![ c_1, c_2, c_3, c_4 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => and
    )
  }

  #[test]
  fn cst_or_1() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let c_2 = instance.bool(true) ;
    let c_3 = instance.bool(true) ;
    let c_4 = instance.bool(true) ;
    let or = instance.op( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => or
    )
  }

  #[test]
  fn cst_or_2() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let c_2 = instance.bool(true) ;
    let c_3 = instance.bool(false) ;
    let c_4 = instance.bool(true) ;
    let or = instance.op( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => or
    )
  }

  #[test]
  fn cst_or_3() {
    let instance = instance() ;
    let c_1 = instance.bool(false) ;
    let c_2 = instance.bool(true) ;
    let c_3 = instance.bool(true) ;
    let c_4 = instance.bool(true) ;
    let or = instance.op( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => or
    )
  }

  #[test]
  fn cst_or_4() {
    let instance = instance() ;
    let c_1 = instance.bool(true) ;
    let c_2 = instance.bool(false) ;
    let c_3 = instance.bool(false) ;
    let c_4 = instance.bool(true) ;
    let or = instance.op( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool model => or
    )
  }

  #[test]
  fn cst_or_5() {
    let instance = instance() ;
    let c_1 = instance.bool(false) ;
    let c_2 = instance.bool(false) ;
    let c_3 = instance.bool(false) ;
    let c_4 = instance.bool(false) ;
    let or = instance.op( Op::Or, vec![ c_1, c_2, c_3, c_4 ] ) ;
    let model = model!() ;
    assert_eval!(
      bool not model => or
    )
  }

  #[test]
  fn models() {
    let instance = instance() ;
    let v_1 = instance.var( 0.into() ) ;
    let v_2 = instance.var( 1.into() ) ;
    let v_3 = instance.var( 2.into() ) ;


    let model_1 = model!( true, 2, 3 ) ;
    let model_2 = model!( true, 7, 0 ) ;

    // (7 - v_2) + (v_2 * 2) + (- v_3)
    let lhs = instance.op(
      Op::Add, vec![
        instance.op( Op::Sub, vec![ instance.int(7), v_2.clone() ] ),
        instance.op( Op::Mul, vec![ v_2.clone(), instance.int(2) ] ),
        instance.op( Op::Sub, vec![ v_3.clone() ] ),
      ]
    ) ;
    assert_eval!(int model_1 => lhs, 6) ;
    assert_eval!(int model_2 => lhs, 14) ;

    // v_3 * 3
    let rhs = instance.op(
      Op::Mul, vec![ v_3.clone(), instance.int(3) ]
    ) ;
    assert_eval!(int model_1 => rhs, 9) ;
    assert_eval!(int model_2 => rhs, 0) ;

    // 7 + v_2 + (- v_3) > v_3 * 3
    let gt = instance.op(
      Op::Gt, vec![ lhs.clone(), rhs.clone() ]
    ) ;
    assert_eval!(bool not model_1 => gt) ;
    assert_eval!(bool     model_2 => gt) ;

    // v_1 && (7 + v_2 + (- v_3) > v_3 * 3)
    let and = instance.op(
      Op::And, vec![ v_1.clone(), gt.clone() ]
    ) ;
    assert_eval!(bool not model_1 => and) ;
    assert_eval!(bool     model_2 => and) ;

    ()
  }
}