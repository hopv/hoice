//! Terms structure and factory.

use std::sync::RwLock ;

use hashconsing::* ;

use common::* ;
use self::info::* ;

pub mod info ;
pub mod build ;

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


/// Values.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Val {
  /// Boolean value.
  B(bool),
  /// Integer value.
  I(Int),
  /// No value (context was incomplete).
  N,
}
impl Val {
  /// Extracts a boolean value.
  pub fn to_bool(self) -> Res<Option<bool>> {
    match self {
      Val::B(b) => Ok( Some(b) ),
      Val::I(_) => bail!("expected boolean value, found integer"),
      Val::N => Ok(None),
    }
  }
  /// Extracts an integer value.
  pub fn to_int(self) -> Res<Option<Int>> {
    match self {
      Val::B(_) => bail!("expected integer value, found boolean"),
      Val::I(i) => Ok( Some(i) ),
      Val::N => Ok(None),
    }
  }
  /// Value parser.
  #[allow(unused_variables)]
  pub fn parse(
    bytes: & [u8]
  ) -> ::nom::IResult<& [u8], Self, Error> {
    use self::build::* ;
    fix_error!(
      bytes,
      Error,
      alt_complete!(
        map!( tag!("true"), |_| Val::B(true) ) |
        map!( tag!("false"), |_| Val::B(false) ) |
        map!( int, |i| Val::I(i) ) |
        do_parse!(
          char!('(') >>
          spc_cmt >> char!('-') >>
          spc_cmt >> value: int >>
          spc_cmt >> char!(')') >>
          ( Val::I(- value) )
        )
      )
    )
  }
}
impl_fmt!{
  Val(self, fmt) {
    match * self {
      Val::I(ref i) => write!(fmt, "{}", i),
      Val::B(b) => write!(fmt, "{}", b),
      Val::N => fmt.write_str("?"),
    }
  }
}
macro_rules! try_val {
  (int $e:expr) => (
    if let Some(i) = $e.to_int()? { i } else {
      return Ok( Val::N )
    }
  ) ;
  (bool $e:expr) => (
    if let Some(b) = $e.to_bool()? { b } else {
      return Ok( Val::N )
    }
  ) ;
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
          Int(ref i) => write!(w, "{}{}", sep, i) ?,
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
        Var(v) => model[v].clone(),
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
}
impl_fmt!{
  RTerm(self, fmt) {
    let mut buf = Vec::with_capacity(250) ;
    self.write(& mut buf, |w, idx| write!(w, "v_{}", idx)).expect(
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
pub enum TTerm {
  /// A predicate application.
  P {
    /// Predicate applied.
    pred: PrdIdx,
    /// The arguments.
    args: VarMap<Term>,
  },
  /// Negation of something.
  N(Term),
  /// Just a term.
  T(Term),
}
impl TTerm {
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
      N(ref t) => {
        write!(w, "(not ") ? ;
        t.write(w, write_var) ? ;
        write!(w, ")", )
      },
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
      w, |w, v| write!(w, "v{}", v), write_prd
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
      TTerm::N(ref t) => write!(fmt, "(not {})", t),
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

  /// Writes a clause given a special function to write predicates.  
  fn write<W, WritePrd>(
    & self, w: & mut W, write_prd: WritePrd
  ) -> IoRes<()>
  where W: Write, WritePrd: Fn(& mut W, PrdIdx, & VarMap<Term>) -> IoRes<()> {
    write!(w, "({}\n  (", ::common::consts::keywords::clause_def) ? ;
    for var in & self.vars {
      write!(w, " ({} {})", var.name, var.typ) ?
    }
    write!(w, " )\n  ") ? ;
    for_first!{
      self.lhs.iter() => {
        |fst| {
          write!(w, "( ") ? ;
          fst.write(
            w, |w, var| w.write_all( self.vars[var].as_bytes() ), & write_prd
          ) ?
        }, then |nxt| {
          write!(w, "\n    ") ? ;
          nxt.write(
            w, |w, var| w.write_all( self.vars[var].as_bytes() ), & write_prd
          ) ?
        }, yild write!(w, "\n  )") ?
      } else write!(w, "()") ?
    }

    write!(w, "\n  ") ? ;
    self.rhs.write(
      w, |w, var| w.write_all( self.vars[var].as_bytes() ), & write_prd
    ) ? ;
    write!(w, "\n)")
  }
}
impl ::std::ops::Index<VarIdx> for Clause {
  type Output = VarInfo ;
  fn index(& self, index: VarIdx) -> & VarInfo {
    & self.vars[index]
  }
}
impl ::rsmt2::Expr2Smt<Candidates> for Clause {
  fn expr_to_smt2<Writer: Write>(
    & self, writer: & mut Writer, cands: & Candidates
  ) -> SmtRes<()> {
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
                  cands[prd].write(
                    w, |w, var| args[var].write(
                      w, |w, var| write!(w, "v{}", var)
                    )
                  )
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
            cands[prd].write(
              w, |w, var| args[var].write(
                w, |w, var| write!(w, "v{}", var)
              )
            )
          }
        ) ;
        if self.lhs.is_empty() { Ok(()) } else {
          write!(writer, ")")
        } ;
        write!(writer, ")")
    }
  }
}




/// Stores the instance: the clauses, the factory and so on.
pub struct Instance {
  /// Term factory.
  factory: RwLock< HashConsign<RTerm> >,
  /// Constants constructed so far.
  consts: HConSet<RTerm>,
  /// Predicates.
  preds: PrdMap<PrdInfo>,
  /// Predicates for which a suitable term has been found.
  preds_term: PrdMap< Option<Term> >,
  /// Max arity of the predicates.
  pub max_pred_arity: Arity,
  /// Clauses.
  clauses: ClsMap<Clause>,
}
impl Instance {
  /// Instance constructor.
  pub fn mk(
    term_capa: usize, clauses_capa: usize, pred_capa: usize
  ) -> Instance {
    let preds_term = vec![ None ; pred_capa ].into() ;
    let mut instance = Instance {
      factory: RwLock::new(
        HashConsign::with_capacity(term_capa)
      ),
      consts: HConSet::with_capacity(103),
      preds: PrdMap::with_capacity(pred_capa), preds_term,
      max_pred_arity: 0.into(),
      clauses: ClsMap::with_capacity(clauses_capa),
    } ;
    // Create basic constants, adding to consts to have mining take them into account.
    let (wan,too) = (instance.one(), instance.zero()) ;
    instance.consts.insert(wan) ;
    instance.consts.insert(too) ;
    instance
  }


  /// Returns the term we already know works for a predicate, if any.
  pub fn term_of(& self, pred: PrdIdx) -> Option<& Term> {
    self.preds_term[pred].as_ref()
  }

  /// Set of int constants **appearing in the predicates**. If more constants
  /// are created after the instance building step, they will not appear here.
  pub fn consts(& self) -> & HConSet<RTerm> {
    & self.consts
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
    idx
  }

  /// Pushes a new clause.
  pub fn push_clause(& mut self, clause: Clause) {
    self.clauses.push(clause)
  }


  /// Creates a variable.
  pub fn var(& self, v: VarIdx) -> Term {
    self.factory.mk( RTerm::Var(v) )
  }
  /// Creates a variable.
  pub fn int(& self, i: Int) -> Term {
    self.factory.mk( RTerm::Int(i) )
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
    op.normalize(self, args)
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

  /// Turns a teacher counterexample into learning data.
  pub fn cexs_to_data(
    & self, data: & ::common::data::Data, cexs: ::teacher::Cexs
  ) -> Res< ::common::data::LearningData > {
    use common::data::* ;

    let mut pos = Vec::with_capacity(10) ;
    let mut neg = Vec::with_capacity(10) ;
    let mut ctr = Vec::with_capacity(10) ;

    for (clause, cex) in cexs.into_iter() {
      let clause = & self[clause] ;
      let mut antecedents = Vec::with_capacity( clause.lhs().len() ) ;
      for tterm in clause.lhs() {
        match * tterm {
          TTerm::P { pred, ref args } => if self.preds_term[pred].is_none() {
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
          },
          _ => (),
        }
      }
      antecedents.shrink_to_fit() ;
      let consequent = match * clause.rhs() {
        TTerm::P { pred, ref args } => {
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

      match ( antecedents.len(), consequent ) {
        (0, None) => bail!(
          "[unimplemented] clause with no predicate has a cex (unsafe)"
        ),
        (1, None) => {
          let (pred, args) = antecedents.pop().unwrap() ;
          neg.push(
            data.add_neg(pred, args) ?
          )
        },
        (0, Some( (pred, args) )) => pos.push(
          data.add_pos(pred, args) ?
        ),
        (_, consequent) => match data.add_cstr(
          antecedents, consequent
        ) ? {
          Some( Either::Lft(ct) ) => ctr.push(ct),
          Some( Either::Rgt((s, true)) ) => pos.push(s),
          Some( Either::Rgt((s, false)) ) => neg.push(s),
          None => (),
        },
      }
    }

    pos.shrink_to_fit() ;
    neg.shrink_to_fit() ;
    ctr.shrink_to_fit() ;

    Ok( LearningData::mk(pos, neg, ctr) )
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
      Add => "+", Sub => "-", Mul => "*", Div => "/", Mod => "mod",
      Gt => ">", Ge => ">=", Le => "<=", Lt => "<", Eql => "=",
      Not => "not", And => "and", Or => "or",
    }
  }

  /// Normalizes its arguments.
  ///
  /// - assumes `(self == Op::Gt || self == Op::Lt) => args.len() == 2`
  pub fn normalize(
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
      Op::Gt => if args.len() != 2 {
        panic!( "[bug] operator `>` applied to {} operands", args.len() )
      } else {
        if let Some( i ) = args[0].int_val() {
          // Checks whether it's zero before decreasing.
          if i.is_zero() {
            // Args is unchanged, term is equivalent to false anyway.
            (Op::Ge, args)
          } else {
            args[0] = instance.int(i - Int::one()) ;
            (Op::Ge, args)
          }
        } else if let Some( i ) = args[1].int_val() {
          args[1] = instance.int(i + Int::one()) ;
          (Op::Ge, args)
        } else {
          (self, args)
        }
      },
      Op::Lt => if args.len() != 2 {
        panic!( "[bug] operator `<` applied to {} operands", args.len() )
      } else {
        if let Some( i ) = args[0].int_val() {
          args[0] = instance.int(i + Int::one()) ;
          (Op::Ge, args)
        } else if let Some( i ) = args[1].int_val() {
          // Checks whether it's zero before decreasing.
          if i.is_zero() {
            // Args is unchanged, term is equivalent to false anyway.
            (Op::Ge, args)
          } else {
            args[1] = instance.int(i - Int::one()) ;
            (Op::Ge, args)
          }
        } else {
          (self, args)
        }
      },
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
        map!(tag!("+"),   |_| Op::Add) |
        map!(tag!("-"),   |_| Op::Sub) |
        map!(tag!("*"),   |_| Op::Mul) |
        map!(tag!("/"),   |_| Op::Div) |
        map!(tag!("mod"), |_| Op::Mod) |
        map!(tag!("<="),  |_| Op::Le ) |
        map!(tag!("<"),   |_| Op::Lt ) |
        map!(tag!(">="),  |_| Op::Ge ) |
        map!(tag!(">"),   |_| Op::Gt ) |
        map!(tag!("="),   |_| Op::Eql) |
        map!(tag!("not"), |_| Op::Not) |
        map!(tag!("and"), |_| Op::And) |
        map!(tag!("or"),  |_| Op::Or )
      )
    )
  }


  /// Evaluation.
  ///
  /// # TO DO
  ///
  /// - add test cases, many of them
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
      Sub => {
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
    for pred in & self.preds {
      write!(
        w, "({}\n  {} (", ::common::consts::keywords::prd_dec, pred.name
      ) ? ;
      for typ in & pred.sig {
        write!(w, " {}", typ) ?
      }
      write!(w, " )\n)\n") ?
    }
    for clause in & self.clauses {
      write!(w, "\n") ? ;
      clause.pebcak_io_fmt(w, & self.preds) ?
    }
    write!(w, "\n")
  }
}