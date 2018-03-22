//! Operators.

use common::* ;


/// Operators.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Op {
  /// Addition.
  Add,
  /// Subtraction.
  Sub,
  /// Multiplication.
  Mul,
  /// Multiplication by a constant.
  ///
  /// Its arguments should always be [ constant, term ].
  CMul,
  /// Integer division.
  IDiv,
  /// Division.
  Div,
  /// Remainder.
  Rem,
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
  /// If-then-else.
  Ite,
  /// Conversion from `Int` to `Real`.
  ToInt,
  /// Conversion from `Real` to `Int`.
  ToReal,
}
impl Op {
  /// String representation.
  pub fn as_str(& self) -> & str {
    use self::Op::* ;
    use keywords::op::* ;
    match * self {
      Add => add_,
      Sub => sub_,
      Mul => mul_,
      CMul => mul_,
      IDiv => idiv_,
      Div => div_,
      Rem => rem_,
      Mod => mod_,
      Gt => gt_,
      Ge => ge_,
      Le => le_,
      Lt => lt_,
      Eql => eq_,
      Not => not_,
      And => and_,
      Or => or_,
      Impl => impl_,
      Ite => ite_,
      ToInt => to_int_,
      ToReal => to_real_,
    }
  }


  /// Type checking.
  ///
  /// Checks that a potentially incomplete list of types makes sense for an
  /// operator.
  ///
  /// If there is an error, returns the type the last argument should have (if
  /// this type it should have is known) and the one found.
  pub fn type_check(
    & self, args: & Vec<Term>
  ) -> Result<
    Typ, Either< (Option<Typ>, (Typ, usize)), String >
  > {
    use Op::* ;
    let mut args_iter = args.iter().enumerate() ;
    macro_rules! err {
      (lft $($lft:tt)*) => (
        return Err( Either::Left($($lft)*) )
      ) ;

      (rgt $($lft:tt)*) => (
        return Err( Either::Right($($lft)*) )
      ) ;

      (nullary) => (
        err!(rgt
          format!("illegal nullary application of `{}`", self)
        )
      ) ;
    }

    macro_rules! arity_check {
      ( [ $min:tt, . ] => $e:expr ) => (
        if args_iter.len() < $min {
          err!(rgt
            format!(
              "illegal application of `{}` to {} arguments (> {})",
              self, args_iter.len(), $min
            )
          )
        } else {
          $e
        }
      ) ;

      ( [ $min:tt, $max:tt ] => $e:expr ) => (
        if args_iter.len() > $max {
          err!(rgt
            format!(
              "illegal application of `{}` to {} arguments (> {})",
              self, args_iter.len(), $max
            )
          )
        } else {
          arity_check!( [ $min, .] => $e )
        }
      ) ;
    }

    macro_rules! all_same {
      (arith) => (
        if let Some((index, fst)) = args_iter.next() {
          let typ = fst.typ() ;
          if ! typ.is_arith() {
            err!(lft (None, (typ, index)))
          }
          while let Some((index, next)) = args_iter.next() {
            if typ != next.typ() {
              err!(lft (Some(next.typ()), (typ, index)) )
            }
          }
          typ
        } else {
          err!(nullary)
        }
      ) ;

      (bool) => ({
        while let Some((index, fst)) = args_iter.next() {
          let typ = fst.typ() ;
          if typ != Typ::Bool {
            err!(lft (Some(Typ::Bool), (typ, index)) )
          }
        }
        Typ::Bool
      }) ;

      () => ({
        if let Some((_, fst)) = args_iter.next() {
          let typ = fst.typ() ;
          while let Some((index, next)) = args_iter.next() {
            if typ != next.typ() {
              err!(lft (Some(typ), (next.typ(), index)) )
            }
          }
          typ
        } else {
          err!(nullary)
        }
      }) ;

      ($typ:expr) => ({
        while let Some((index, fst)) = args_iter.next() {
          if fst.typ() != $typ {
            err!(lft (Some($typ), (fst.typ(), index)))
          }
        }
        $typ
      }) ;
    }

    let res = match * self {
      Add | Sub | Mul | Div | CMul => {
        all_same!(arith)
      },
      IDiv | Rem | Mod => arity_check!(
        [ 2, 2 ] => {
          all_same!(Typ::Int)
        }
      ),
      Gt | Ge | Le | Lt => arity_check!(
        [ 2, 2 ] => {
          all_same!(arith) ;
          Typ::Bool
        }
      ),
      Eql => {
        all_same!() ;
        Typ::Bool
      },
      Not => arity_check!(
        [ 1, 1 ] => all_same!(Typ::Bool)
      ),
      And | Or | Impl => all_same!(bool),
      ToInt => arity_check!(
        [ 1, 1 ] => all_same!(Typ::Real)
      ),
      ToReal => arity_check!(
        [ 1, 1 ] => all_same!(Typ::Int)
      ),
      Ite => arity_check!(
        [ 3, 3 ] => if let Some((index, cond)) = args_iter.next() {
          if ! cond.typ().is_bool() {
            err!(lft (Some(Typ::Bool), (cond.typ(), index)))
          }
          all_same!()
        } else {
          err!(nullary)
        }
      ),
    } ;
    Ok(res)
  }


  /// Evaluation.
  pub fn eval(& self, mut args: Vec<Val>) -> Res<Val> {
    use term::Op::* ;
    if args.is_empty() {
      bail!("evaluating operator on 0 elements")
    }

    // print!("evaluating `({}", self) ;
    // for val in & args {
    //   print!(" {}", val)
    // }
    // println!(")`") ;

    macro_rules! arith_app {
      (relation $op:tt $str:tt => $args:expr) => ({
        let mut args = $args.into_iter() ;
        if let (
          Some(fst), Some(mut pre)
        ) = (args.next(), args.next()) {
          let mut res = fst.$op( pre.clone() ) ? ;
          for arg in args {
            res = res.and( pre.$op( arg.clone() ) ? ) ? ;
            pre = arg
          }
          Ok(res)
        } else {
          bail!("`{}` applied to 0 or 1 argument(s)")
        }
      }) ;
      ($op:tt $str:tt => $args:expr) => ({
        let mut args = $args.into_iter() ;
        if let Some(mut acc) = args.next() {
          for arg in args {
            acc = acc.$op(arg) ?
          }
          Ok(acc)
        } else {
          bail!("`{}` applied to zero arguments", $str)
        }
      }) ;
    }

    match * self {
      Add => arith_app!(add "+" => args),

      Sub => if args.len() == 1 {
        args.pop().unwrap().minus()
      } else {
        arith_app!(sub "-" => args)
      },

      Mul => {
        let mut res: Val = 1.into() ;
        for arg in args.into_iter() {
          res = res.mul(arg) ?
        }
        Ok(res)
      },

      CMul => {
        let mut res: Val = 1.into() ;
        for arg in args.into_iter() {
          res = res.mul(arg) ?
        }
        Ok(res)
      },

      Div => {
        let (den, num) = (
          if let Some(den) = args.pop() { den } else {
            bail!(
              "illegal application of division to less than two arguments"
            )
          },
          if let Some(num) = args.pop() { num } else {
            bail!(
              "illegal application of division to less than two arguments"
            )
          }
        ) ;
        if args.pop().is_some() {
          bail!("unexpected division over {} numbers", args.len())
        }

        let res = match (num.clone(), den.clone()) {
          (num, Val::N) => if num.is_zero() {
            Ok(num)
          } else {
            Ok(Val::N)
          },

          (Val::I(num), Val::I(den)) => if num.is_zero() {
            Ok( Val::I(num) )
          } else if & num % & den == Int::zero() {
            Ok( Val::I( num / den ) )
          } else {
            Ok( Val::R( Rat::new(num, den) ) )
          },

          (Val::I(num), Val::R(den)) => if num.is_zero() {
            Ok( Val::I(num) )
          } else {
            Ok( Val::R( Rat::new(num, 1.into()) / den ) )
          },

          (Val::R(num), Val::I(den)) => if num.is_zero() {
            Ok( Val::R(num) )
          } else {
            Ok( Val::R( num / Rat::new(den, 1.into()) ) )
          },

          (Val::R(num), Val::R(den)) => if num.is_zero() {
            Ok( Val::R(num) )
          } else {
            Ok( Val::R( num / den ) )
          },

          (Val::B(_), _) | (_, Val::B(_)) => bail!(
            "illegal application of division to booleans"
          ),

          (Val::N, _) => Ok(Val::N),
        } ;

        // println!("(/ {} {}) = {}", num, den, res.as_ref().unwrap()) ;

        res

      },

      IDiv => if args.len() != 2 {
        bail!("unexpected division over {} numbers", args.len())
      } else {
        let den = try_val!( int args.pop().unwrap() ) ;
        let num = try_val!( int args.pop().unwrap() ) ;
        if den.is_zero() {
          bail!("denominator is zero...")
        }
        let mut res = & num / & den ;
        use num::Signed ;
        if num.is_negative() ^ den.is_negative() {
          if den.clone() * & res != num {
            res = res - 1
          }
        }
        // println!("(div {} {}) = {}", num, den, res) ;
        Ok( Val::I(res) )
      },

      Rem => if args.len() != 2 {
        bail!(
          format!("evaluating `{}` with {} (!= 2) arguments", self, args.len())
        )
      } else {
        use num::Integer ;
        let b = try_val!( int args.pop().unwrap() ) ;
        if b == 1.into() {
          Ok( 0.into() )
        } else {
          let a = try_val!( int args.pop().unwrap() ) ;
          Ok( Val::I( a.div_rem(& b).1 ) )
        }
      },

      Mod => if args.len() != 2 {
        bail!(
          format!("evaluating `{}` with {} (!= 2) arguments", self, args.len())
        )
      } else {
        use num::{ Integer, Signed } ;
        let b = try_val!( int args.pop().unwrap() ) ;
        if b == 1.into() {
          Ok( 0.into() )
        } else {
          let a = try_val!( int args.pop().unwrap() ) ;
          let res = a.mod_floor(& b) ;
          let res = if res.is_negative() {
            b.abs() - res.abs()
          } else {
            res
          } ;
          Ok( Val::I( res ) )
        }
      },

      // Bool operators.

      Gt => arith_app! {
        relation gt ">" => args
      },

      Ge => arith_app! {
        relation ge ">=" => args
      },

      Le => arith_app! {
        relation le "<=" => args
      },

      Lt => arith_app! {
        relation lt "<" => args
      },

      Eql => {
        let mem ;
        let mut res = true ;
        for_first!{
          args.into_iter() => {
            |fst| mem = fst,
            then |nxt| {
              // println!("{} != {} : {}", mem, nxt, mem != nxt) ;
              if ! mem.same_type( & nxt ) {
                return Ok(Val::N)
              }
              if mem != nxt {
                res = false ;
                break
              }
            },
          } else unreachable!()
        }
        Ok( Val::B(res) )
      },

      Not => if args.len() != 1 {
        bail!(
          format!("evaluating `Not` with {} (!= 1) arguments", args.len())
        )
      } else {
        if let Some(b) = args.pop().unwrap().to_bool() ? {
          Ok( Val::B(! b) )
        } else {
          Ok(Val::N)
        }
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

      Ite => if args.len() != 3 {
        bail!(
          format!("evaluating `Ite` with {} (!= 3) arguments", args.len())
        )
      } else {
        let (els, thn, cnd) = (
          args.pop().unwrap(), args.pop().unwrap(), args.pop().unwrap()
        ) ;
        match cnd.to_bool() ? {
          Some(true) => Ok(thn),
          Some(false) => Ok(els),
          _ => Ok(Val::N),
        }
      }

      ToInt => if let Some(val) = args.pop() {
        if ! args.is_empty() {
          bail!(
            "expected two arguments for `{}`, found {}", ToInt, args.len() + 1
          )
        }
        if let Some(rat) = val.to_real() ? {
          let res = rat.denom() / rat.denom() ;
          if rat.denom().is_negative() ^ rat.denom().is_negative() {
            Ok( Val::I(- res) )
          } else {
            Ok( Val::I(res) )
          }
        } else {
          Ok(Val::N)
        }
      } else {
        bail!("expected one argument for `{}`, found none", ToInt)
      },

      ToReal => if let Some(val) = args.pop() {
        if ! args.is_empty() {
          bail!(
            "expected two arguments for `{}`, found {}", ToReal, args.len() + 1
          )
        }
        if let Some(i) = val.to_int() ? {
          Ok( Val::R( Rat::new(i.clone(), 1.into()) ) )
        } else {
          Ok(Val::N)
        }
      } else {
        bail!("expected one argument for `{}`, found none", ToReal)
      },

    }
  }
}
impl_fmt!{
  Op(self, fmt) {
    fmt.write_str( self.as_str() )
  }
}