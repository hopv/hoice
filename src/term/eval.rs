//! Term evaluation using the term zipper.

use std::slice::Iter ;

use common::* ;
use term::zip::* ;

/// Zipper frames for term evaluation.
pub type Frame<'a> = ZipFrame< 'a, Vec<Val> > ;
/// Zipper command for term evaluation.
pub type Cmd<'a> = ZipDo< 'a, Vec<Val>, Val > ;
/// Zipper command (total case) for term evaluation.
pub type CmdT<'a> = ZipDoTotal< 'a, Val > ;

/// Term evaluation.
pub fn eval<E: Evaluator>(term: & Term, model: & E) -> Res<Val> {
  let mut fun_ref_count = 0 ;
  let res = zip(
    term, |zip_null| leaf(model, zip_null),
    |op, typ, values| total(op, typ, values, & mut fun_ref_count),
    partial
  ) ;
  fun::decrease_ref_count(fun_ref_count) ;
  res
}


macro_rules! go {
  (up $e:expr) => (
    return Ok( ZipDo::Upp { yielded: $e } )
  ) ;
  (down $e:expr) => (
    return Ok( ZipDo::Dwn { nu_term: $e } )
  ) ;
}


fn leaf<'a, E: Evaluator>(
  model: & E, zip_null: ZipNullary<'a>,
) -> Res<Val> {
  match zip_null {
    ZipNullary::Cst(val) => Ok( val.clone() ),
    ZipNullary::Var(_, var) => if var < model.len() {
      Ok( model.get(var).clone() )
    } else {
      bail!("model is too short ({} / {})", * var, model.len())
    },
  }
}


fn total<'a>(
  op: ZipOp<'a>, typ: & 'a Typ, mut values: Vec<Val>,
  fun_ref_count: & mut usize
) -> Res< CmdT<'a> > {
  let yielded = match op {
    ZipOp::Op(op) => op.eval(values).chain_err(
      || format!("while evaluating operator `{}`", op)
    ) ?,

    ZipOp::New(name) => val::dtyp_new(
      typ.clone(), name.clone(), values
    ),

    ZipOp::Slc(name) => if values.len() == 1 {
      let value = values.pop().unwrap() ;
      if ! value.is_known() {
        val::none( typ.clone() )
      } else if let Some(
        (ty, constructor, values)
      ) = value.dtyp_inspect() {
        if let Some((dtyp, _)) = ty.dtyp_inspect() {

          if let Some(selectors) = dtyp.news.get(constructor) {

            let mut res = None ;
            for ((selector, _), value) in selectors.iter().zip(
              values.iter()
            ) {
              if selector == name {
                res = Some( value.clone() )
              }
            }

            if let Some(res) = res {
              res
            } else {
              val::none( typ.clone() )
            }

          } else {
            bail!(
              "unknown constructor `{}` for datatype {}",
              conf.bad(constructor), dtyp.name
            )
          }

        } else {
          bail!("inconsistent type {} for value {}", ty, value)
        }
      } else {
        bail!(
          "illegal application of constructor `{}` of `{}` to `{}`",
          conf.bad(& name), typ, value
        )
      }
    } else {
      bail!(
        "expected one value for datatype selection, found {}", values.len()
      )
    },

    ZipOp::CArray => if values.len() == 1 {
      let default = values.pop().unwrap() ;
      val::array( typ.clone(), default )
    } else {
      bail!(
        "expected one value for constant array construction, found {}",
        values.len()
      )
    },

    ZipOp::Fun(name) => {
      let fun = if let Some(fun) = fun::get_as_ref(name) {
        fun
      } else {
        bail!("cannot evaluate unknown function `{}`", conf.bad(name))
      } ;
      * fun_ref_count += 1 ;

      if values.len() != fun.sig.len() {
        bail!(
          "illegal application of function `{}` to {} arguments (expected {})",
          conf.bad(name), values.len(), fun.sig.len()
        )
      }

      return Ok(
        ZipDoTotal::Dwn {
          nu_term: & fun.def,
          nu_subst: Some( values.into() ),
        }
      )
    },
  } ;

  Ok( ZipDoTotal::Upp { yielded } )
}





fn partial<'a>(
  Frame { thing, typ, lft_args, mut rgt_args }: Frame<'a>
) -> Res< Cmd<'a> > {

  match thing {
    ZipOp::Op(op) => partial_op(op, typ, lft_args, rgt_args),
    thing @ ZipOp::New(_) |
    thing @ ZipOp::Fun(_) |
    thing @ ZipOp::CArray |
    thing @ ZipOp::Slc(_) => {
      let nu_term = rgt_args.next().expect(
        "illegal call to `partial_op`: empty `rgt_args`"
      ) ;
      Ok(
        ZipDo::Trm {
          nu_term, frame: Frame { thing, typ, lft_args, rgt_args }
        }
      )
    },
  }

}




fn partial_op<'a>(
  op: Op, typ: & 'a Typ, mut lft_args: Vec<Val>, mut rgt_args: Iter<'a, Term>
) -> Res< ZipDo< 'a, Vec<Val>, Val > > {
  // Since this is called each time a value is added to `lft_args`, we only
  // need to check the last value in `lft_args`.

  match op {

    Op::Ite => if let Some(c) = lft_args.pop() {
      if ! lft_args.is_empty() {
        bail!(
          "partial `Ite` application with `lft_args` of length {}",
          lft_args.len() + 1
        )
      }

      let (t, e) = if let (Some(t), Some(e), None) = (
        rgt_args.next(), rgt_args.next(), rgt_args.next()
      ) {
        (t, e)
      } else {
        bail!("illegal application of `Ite`")
      } ;

      match c.to_bool().chain_err(
        || "during `Ite` condition evaluation"
      ) ? {

        // Condition is true, go into the `then` branch.
        Some(true) => go!(down t),

        // Condition is false, go into the `else` branch.
        Some(false) => go!(down e),

        // Unknown condition value. Keep going, the Ite might still be
        // evaluable if both branches are equal.
        None => (),
      }
    },

    Op::And => if let Some(last) = lft_args.pop() {
      match last.to_bool() ? {
        // False, no need to evaluate the other arguments.
        Some(false) => go!( up val::bool(false) ),
        // True, just skip.
        Some(true) => (),
        // Unknown, push back and keep going.
        None => lft_args.push(last),
      }
    },

    Op::Or => if let Some(last) = lft_args.pop() {
      match last.to_bool() ? {
        // True, no need to evaluate the other arguments.
        Some(true) => go!( up val::bool(true) ),
        // False, just skip.
        Some(false) => (),
        // Unknown, push back and keep going.
        None => lft_args.push(last),
      }
    },

    Op::Mul => if let Some(last) = lft_args.last() {
      if last.is_zero() || ! last.is_known() {
        go!( up last.clone() )
      }
    },

    Op::Mod | Op::Rem => if let Some(last) = lft_args.last() {
      debug_assert! { lft_args.len() == 1 }
      if last.is_zero() || ! last.is_known() {
        go!( up last.clone() )
      }
    },

    Op::Impl => if let Some(last) = lft_args.last() {
      debug_assert! { lft_args.len() == 1 }
      if last.is_false() {
        go!( up val::bool(true) )
      }
    },

    Op::Distinct => if let Some(last) = lft_args.last() {
      if last.is_known() {
        for other in lft_args.iter().take(lft_args.len() - 1) {
          if last == other {
            go!( up val::bool(false) )
          }
        }
      }
    },

    Op::Add | Op::Sub |
    Op::CMul | Op::IDiv | Op::Div |
    Op::Gt | Op::Ge | Op::Le | Op::Lt |
    Op::Eql
    => if let Some(last) = lft_args.last() {
      if ! last.is_known() {
        return Ok(
          ZipDo::Upp { yielded: val::none( typ.clone() ) }
        )
      }
    },

    Op::Store | Op::Select => (),

    Op::Not |
    Op::ToInt |
    Op::ToReal => bail!(
      "partial application of unary operator ({}) makes no sense", op
    ),

  }

  // Normal exit.
  let nu_term = rgt_args.next().expect(
    "illegal call to `partial_op`: empty `rgt_args`"
  ) ;
  Ok(
    ZipDo::Trm {
      nu_term, frame: Frame {
        thing: ZipOp::Op(op), typ, lft_args, rgt_args
      }
    }
  )
}





