#![doc = r#"Hashconsed terms.

The factory is a `static_ref` for easy creation.
"#]

use hashconsing::* ;

use common::* ;
use instance::Instance ;

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
  /// let instance = & Instance::new(10, 10, 10) ;
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
  /// let instance = & Instance::new(10, 10, 10) ;
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
  /// let instance = & Instance::new(10, 10, 10) ;
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
  /// let instance = & Instance::new(10, 10, 10) ;
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
    instance.mk( RTerm::App { op, args } )
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
