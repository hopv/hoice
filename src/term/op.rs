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
  /// Distinct.
  Distinct,

  /// Conversion from `Int` to `Real`.
  ToInt,
  /// Conversion from `Real` to `Int`.
  ToReal,

  /// Updater for arrays.
  Store,
  /// Accessor for arrays.
  Select,
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
      Store => store_,
      Select => select_,
      Distinct => distinct_,
    }
  }


  /// Type checking.
  ///
  /// If there is an error, returns the type the spurious argument should have
  /// (if it is known) and the one found.
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
        return Err( Either::Right( format!($($lft)*)) )
      ) ;

      (nullary) => (
        err!(rgt
          "illegal nullary application of `{}`", self
        )
      ) ;
    }

    macro_rules! arity_check {
      ( [ $min:tt, . ] => $e:expr ) => (
        if args_iter.len() < $min {
          err!(rgt
            "illegal application of `{}` to {} arguments (> {})",
            self, args_iter.len(), $min
          )
        } else {
          $e
        }
      ) ;

      ( [ $min:tt, $max:tt ] => $e:expr ) => (
        if args_iter.len() > $max {
          err!(rgt
            "illegal application of `{}` to {} arguments (> {})",
            self, args_iter.len(), $max
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
              err!(lft (Some(typ), (next.typ(), index)) )
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
          if typ != typ::bool() {
            err!(lft (Some(typ::bool()), (typ, index)) )
          }
        }
        typ::bool()
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
          all_same!(typ::int())
        }
      ),
      Gt | Ge | Le | Lt => arity_check!(
        [ 2, 2 ] => {
          all_same!(arith) ;
          typ::bool()
        }
      ),

      Distinct |
      Eql => {
        all_same!() ;
        typ::bool()
      },
      Not => arity_check!(
        [ 1, 1 ] => all_same!(typ::bool())
      ),
      And | Or | Impl => all_same!(bool),
      ToInt => arity_check!(
        [ 1, 1 ] => {
          all_same!(typ::real()) ;
          typ::int()
        }
      ),
      ToReal => arity_check!(
        [ 1, 1 ] => {
          all_same!(typ::int()) ;
          typ::real()
        }
      ),
      Ite => arity_check!(
        [ 3, 3 ] => if let Some((index, cond)) = args_iter.next() {
          if ! cond.typ().is_bool() {
            err!(lft (Some(typ::bool()), (cond.typ(), index)))
          }
          all_same!()
        } else {
          err!(nullary)
        }
      ),

      Store => arity_check!(
        [ 3, 3 ] => if let Some((src, tgt)) = args[0].typ().array_inspect() {
          if args[1].typ() != * src {
            err!(
              lft ( Some(src.clone()), (args[1].typ(), 1) )
            )
          } else if args[2].typ() != * tgt {
            err!(
              lft ( Some(tgt.clone()), (args[2].typ(), 2) )
            )
          } else {
            args[0].typ()
          }
        } else {
          err!(lft (None, (args[0].typ(), 0)))
        }
      ),

      Select => arity_check!(
        [ 2, 2 ] => if let Some((src, tgt)) = args[0].typ().array_inspect() {
          if args[1].typ() != * src {
            err!(
              lft ( Some(src.clone()), (args[1].typ(), 1) )
            )
          } else {
            tgt.clone()
          }
        } else {
          err!(lft (None, (args[0].typ(), 0)))
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

          let mut res = fst.get().$op( & pre ) ? ;

          for arg in args {
            res = res.and( & pre.get().$op( & arg ) ? ) ? ;
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
            acc = acc.$op(& arg) ?
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
        let mut res: Val = val::int(1) ;
        for arg in args.into_iter() {
          res = res.mul(& arg) ?
        }
        Ok(res)
      },

      CMul => {
        let mut res: Val = val::int(1) ;
        for arg in args.into_iter() {
          res = res.mul(& arg) ?
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
          bail!("unexpected division over {} numbers", args.len() + 3)
        }

        let res = match (num.get(), den.get()) {
          (num_val, & val::RVal::N(ref typ))
          if typ.is_arith() => if num_val.is_zero() {
            Ok(num.clone())
          } else {
            Ok(val::none(typ::real()))
          },

          (
            & val::RVal::I(ref num), & val::RVal::I(ref den)
          ) => if num.is_zero() {
            Ok( val::int(num.clone()) )
          } else if num % den == Int::zero() {
            Ok( val::int( num / den ) )
          } else {
            Ok( val::real( Rat::new(num.clone(), den.clone()) ) )
          },

          (
            & val::RVal::I(ref num_val), & val::RVal::R(ref den_val)
          ) => if num_val.is_zero() {
            Ok( val::real(Rat::new(0.into(), 1.into())) )
          } else {
            Ok(
              val::real( Rat::new(num_val.clone(), 1.into()) / den_val.clone() )
            )
          },

          (
            & val::RVal::R(ref num_val), & val::RVal::I(ref den_val)
          ) => if num.is_zero() {
            Ok( val::real(Rat::new(0.into(), 1.into())) )
          } else {
            Ok(
              val::real(
                num_val.clone() / Rat::new(den_val.clone(), 1.into())
              )
            )
          },

          (
            & val::RVal::R(ref num_val), & val::RVal::R(ref den_val)
          ) => if num.is_zero() {
            Ok( val::real(Rat::new(0.into(), 1.into())) )
          } else {
            Ok( val::real( num_val.clone() / den_val.clone() ) )
          },

          (& val::RVal::N(ref t_1), & val::RVal::I(ref i))
          if t_1.is_arith() => if i.is_zero() {
            bail!("division by zero, aborting...")
          } else {
            Ok(val::none(t_1.clone()))
          },

          (& val::RVal::N(ref t_1), & val::RVal::R(ref r))
          if t_1.is_arith() => if r.is_zero() {
            bail!("division by zero, aborting...")
          } else {
            Ok(val::none(typ::real()))
          },

          (num, den) => bail!(
            "illegal division application to {} ({}) {} ({})",
            num, num.typ(), den, den.typ()
          ),
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
          bail!("division by zero, aborting...")
        }
        let mut res = & num / & den ;
        use num::Signed ;
        if num.is_negative() ^ den.is_negative() {
          if den.clone() * & res != num {
            res = res - 1
          }
        }
        // println!("(div {} {}) = {}", num, den, res) ;
        Ok( val::int(res) )
      },

      Rem => if args.len() != 2 {
        bail!(
          format!("evaluating `{}` with {} (!= 2) arguments", self, args.len())
        )
      } else {
        use num::Integer ;
        let b = try_val!( int args.pop().unwrap() ) ;
        if b == 1.into() {
          Ok( val::int(0) )
        } else {
          let a = try_val!( int args.pop().unwrap() ) ;
          Ok( val::int( a.div_rem(& b).1 ) )
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
          Ok( val::int(0) )
        } else {
          let a = try_val!( int args.pop().unwrap() ) ;
          let res = a.mod_floor(& b) ;
          let res = if res.is_negative() {
            b.abs() - res.abs()
          } else {
            res
          } ;
          Ok( val::int( res ) )
        }
      },

      // Bool operators.

      Gt => arith_app! {
        relation g_t ">" => args
      },

      Ge => arith_app! {
        relation g_e ">=" => args
      },

      Le => arith_app! {
        relation l_e "<=" => args
      },

      Lt => arith_app! {
        relation l_t "<" => args
      },

      Distinct => {
        while let Some(arg) = args.pop() {
          for other in & args {
            if arg.eql(& other).to_bool() ? != Some(true) {
              return Ok( val::bool(false) )
            }
          }
        }
        Ok( val::bool(true) )
      },

      Eql => {
        let mem ;
        for_first!{
          args.into_iter() => {
            |fst| mem = fst,
            then |nxt| {
              let tmp = nxt.eql(& mem) ;
              if tmp.to_bool() ? != Some(true) {
                return Ok(tmp)
              }
            },
          } else unreachable!()
        }
        Ok( val::bool(true) )
      },

      Not => if args.len() != 1 {
        bail!(
          format!("evaluating `Not` with {} (!= 1) arguments", args.len())
        )
      } else {
        if let Some(b) = args.pop().unwrap().to_bool() ? {
          Ok( val::bool(! b) )
        } else {
          Ok(val::none(typ::bool()))
        }
      },

      And => {
        let mut res = val::bool(true) ;
        for arg in args {
          res = res.and(& arg) ? ;
          if res.is_false() {
            return Ok(res)
          }
        }
        Ok(res)
      },

      Or => {
        let mut res = val::bool(false) ;
        for arg in args {
          res = res.or(& arg) ? ;
          if res.is_true() {
            return Ok(res)
          }
        }
        Ok(res)
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
          (_, Some(true)) | (Some(false), _) => Ok( val::bool(true) ),
          (Some(lhs), Some(rhs)) => Ok( val::bool(rhs || ! lhs) ),
          _ => Ok(val::none(typ::bool())),
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

        if thn.get().equal(& els) {
          return Ok(thn)
        }

        match cnd.to_bool() ? {
          Some(true) => Ok(thn),
          Some(false) => Ok(els),
          None => match (
            thn.get().typ().is_real(), els.get().typ().is_real()
          ) {
            (true, _) | (_, true) => Ok(val::none(typ::real())),
            _ => Ok(val::none(thn.get().typ().clone())),
          }
        }
      }

      ToInt => if let Some(val) = args.pop() {
        if ! args.is_empty() {
          bail!(
            "expected one arguments for `{}`, found {}", self, args.len() + 1
          )
        }
        if let Some(rat) = val.to_real() ? {
          let res = rat.denom() / rat.denom() ;
          if rat.denom().is_negative() ^ rat.denom().is_negative() {
            Ok( val::int(- res) )
          } else {
            Ok( val::int(res) )
          }
        } else {
          Ok(val::none(typ::int()))
        }
      } else {
        bail!("expected one argument for `{}`, found none", self)
      },

      ToReal => if let Some(val) = args.pop() {
        if ! args.is_empty() {
          bail!(
            "expected one arguments for `{}`, found {}", self, args.len() + 1
          )
        }
        if let Some(i) = val.to_int() ? {
          Ok( val::real( Rat::new(i.clone(), 1.into()) ) )
        } else {
          Ok(val::none(typ::real()))
        }
      } else {
        bail!("expected one argument for `{}`, found none", self)
      },

      Store => if args.len() == 3 {
        let (val, idx, array) = (
          args.pop().unwrap(),
          args.pop().unwrap(),
          args.pop().unwrap()
        ) ;
        Ok( array.store(idx, val) )
      } else {
        bail!("expected three arguments for `{}`, found {}", self, args.len())
      },

      Select => if args.len() == 2 {
        let (idx, array) = (
          args.pop().unwrap(),
          args.pop().unwrap()
        ) ;
        Ok( array.select(idx) )
      } else {
        bail!("expected two arguments for `{}`, found {}", self, args.len())
      }

    }
  }
}
impl_fmt!{
  Op(self, fmt) {
    fmt.write_str( self.as_str() )
  }
}