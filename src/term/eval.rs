//! Term evaluation using the term zipper.

use common::* ;
use term::zip::* ;


/// Term evaluation.
pub fn eval<E: Evaluator>(term: & Term, model: & E) -> Res<Val> {
  zip::<Error, Vec<Val>, Val, _, _, _>(
    term,

    // Variables and constants.
    |zip_null| match zip_null {
      ZipNullary::Cst(val) => Ok( val.clone() ),
      ZipNullary::Var(_, var) => if var < model.len() {
        Ok( model.get(var).clone() )
      } else {
        bail!("model is too short ({} / {})", * var, model.len())
      },
    },

    // Applications.
    |op, typ, mut values| match op {
      ZipOp::Op(op) => op.eval(values).chain_err(
        || format!("while evaluating operator `{}`", op)
      ),

      ZipOp::New(name) => Ok(
        val::dtyp_new( typ.clone(), name.clone(), values )
      ),

      ZipOp::Slc(name) => if values.len() == 1 {
        let value = values.pop().unwrap() ;
        if ! value.is_known() {
          Ok( val::none( typ.clone() ) )
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
                Ok(res)
              } else {
                Ok( val::none( typ.clone() ) )
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
        Ok( val::array( typ.clone(), default ) )
      } else {
        bail!(
          "expected one value for constant array construction, found {}",
          values.len()
        )
      },

      ZipOp::Fun(_) => unimplemented!(),
    },

    |mut frame| if let Some(nu_term) = frame.rgt_args.next() {
      Ok(
        ZipDo::Trm { nu_term, frame }
      )
    } else {
      bail!("unreachable")
    }
  )
}