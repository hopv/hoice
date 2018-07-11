//! Zipper over terms.
//!
//! # TODO
//!
//! - explain

use std::slice::Iter ;

use common::* ;



/// The direction of the next step.
///
/// This is essentially a command from the exterior (the caller) to the zipper
/// telling it which way it will go next.
#[derive(Clone, Debug)]
pub enum ZipDo<'a, Acc, Yield> {
  /// Remember a frame and inspect a term.
  Trm {
    /// The new term to work on.
    nu_term: & 'a Term,
    /// The frame (application) inside of which we are.
    frame: ZipFrame<'a, Acc>,
  },

  /// Go down. Means "skip the current application and go directly to this".
  ///
  /// Example: when evaluating an `(ite c t e)` application: given the value of
  /// `c`, when want to go down into `t` or `e` directly, not evaluate both.
  Dwn {
    /// The term we're going down in.
    nu_term: & 'a Term,
    /// An optional substitution.
    ///
    /// The only case where this is useful currently is when evaluating a
    /// function application.
    nu_subst: Option< VarMap<Yield> >,
  },

  /// Go up. Means "here is the result, skip everything else at this level".
  ///
  /// Example: when evaluating a `(* a0 a1 ...)` application. If `a0` evaluates
  /// to `0` then we can go up directly with `0`.
  Upp {
    /// The result to propagate upwards.
    yielded: Yield
  },
}



/// The operators manipulated by the zipper.
#[derive(Clone, Copy, Debug)]
pub enum ZipOp<'a> {
  /// An operator.
  Op(Op),
  /// A datatype constructor.
  New(& 'a String),
  /// A function application.
  Fun(& 'a String),
  /// A constant array construction.
  CArray,
  /// A datatype selection.
  Slc(& 'a String),
}


// Nullary things the zipper can manipulate.
#[derive(Clone, Debug)]
pub enum ZipNullary<'a> {
  /// A constant.
  Cst(& 'a Val),
  /// A variable.
  Var(& 'a Typ, VarIdx),
}


/// A frame in the zipper.
///
/// This is both what the zipper manipulates and what the user's function will
/// take as input.
#[derive(Clone, Debug)]
pub struct ZipFrame<'a, Acc> {
  /// The thing being applied.
  pub thing: ZipOp<'a>,
  /// The type of the application.
  pub typ: & 'a Typ,
  /// The arguments that have already been handled.
  pub lft_args: Acc,
  /// The arguments that have not already been handled.
  pub rgt_args: Iter<'a, Term>,
}



/// Accumulator trait.
///
/// The goal is to let the zipper know how to construct an empty accumulator.
pub trait Accumulator<Elem> {
  /// Creates an empty accumulator.
  fn new_empty(usize) -> Self ;
  /// Pushes a new element in the accumulator.
  fn push(& mut self, Elem) ;
}
impl<T> Accumulator<T> for Vec<T> {
  fn new_empty(hint: usize) -> Self { Vec::with_capacity(hint) }
  fn push(& mut self, elem: T) { self.push(elem) }
}



/// Zip function.
pub fn zip<E, Acc, Yield, NulF, AppF, Partial>(
  term: & Term, mut nul_do: NulF, mut app_do: AppF, mut partial: Partial
) -> Result<Yield, E>
where
Acc: Accumulator<Yield>, Yield: Clone,

NulF: for<'a> FnMut(
  ZipNullary<'a>
) -> Result< Yield, E >,

AppF: for<'a> FnMut(
  ZipOp<'a>, & 'a Typ, Acc
) -> Result< Yield, E >,

Partial: for<'a> FnMut(
  ZipFrame<'a, Acc>
) -> Result< ZipDo<'a, Acc, Yield>, E > {
  // Empty vector of terms, useful when handling unary operators.
  let empty: Vec<Term> = Vec::with_capacity(0) ;

  // Current term we're going down in.
  let mut term = term ;

  // Stack of `ZipFrame`.
  let mut stack = Vec::with_capacity(7) ;
  // The current substitution, if any.
  let mut subst: Option< VarMap<Yield> > = None ;

  'inspect_term: loop {

    let mut result = match * term.get() {

      RTerm::Var(ref typ, var_idx) => if let Some(subst) = subst.as_ref() {
        subst[var_idx].clone()
      } else {
        nul_do( ZipNullary::Var(typ, var_idx) ) ?
      },

      RTerm::Cst(ref cst) => nul_do( ZipNullary::Cst(cst) ) ?,

      RTerm::CArray { ref typ, term: ref nu_term } => {
        let frame = ZipFrame {
          thing: ZipOp::CArray, typ,
          lft_args: Acc::new_empty(1),
          rgt_args: empty.iter(),
        } ;
        stack.push( (frame, subst.clone()) ) ;
        term = nu_term ;

        continue 'inspect_term
      },

      RTerm::App { op, ref typ, ref args } => {
        let mut rgt_args = args.iter() ;
        let op = ZipOp::Op(op) ;
        let lft_args = Acc::new_empty( args.len() ) ;

        if let Some(nu_term) = rgt_args.next() {
          let frame = ZipFrame {
            thing: op, typ, lft_args, rgt_args,
          } ;
          stack.push( (frame, subst.clone()) ) ;
          term = nu_term ;

          continue 'inspect_term

        } else {
          app_do(op, typ, lft_args) ?
        }
      },

      RTerm::DTypNew { ref typ, ref name, ref args } => {
        let mut rgt_args = args.iter() ;
        let op = ZipOp::New(name) ;
        let lft_args = Acc::new_empty( args.len() ) ;

        if let Some(nu_term) = rgt_args.next() {
          let frame = ZipFrame {
            thing: op, typ, lft_args, rgt_args,
          } ;
          stack.push( (frame, subst.clone()) ) ;
          term = nu_term ;

          continue 'inspect_term

        } else {
          app_do(op, typ, lft_args) ?
        }
      },

      RTerm::DTypSlc { ref typ, ref name, term: ref nu_term } => {
        let mut rgt_args = empty.iter() ;
        let op = ZipOp::Slc(name) ;
        let lft_args = Acc::new_empty(1) ;

        let frame = ZipFrame {
          thing: op, typ, lft_args, rgt_args,
        } ;
        stack.push( (frame, subst.clone()) ) ;
        term = nu_term ;

        continue 'inspect_term
      },

      RTerm::Fun { ref typ, ref name, ref args } => {
        let mut rgt_args = empty.iter() ;
        let op = ZipOp::Fun(name) ;
        let lft_args = Acc::new_empty( args.len() ) ;

        if let Some(nu_term) = rgt_args.next() {
          let frame = ZipFrame {
            thing: op, typ, lft_args, rgt_args,
          } ;
          stack.push( (frame, subst.clone()) ) ;
          term = nu_term ;

          continue 'inspect_term

        } else {
          app_do(op, typ, lft_args) ?
        }
      },

    } ;

    'inspect_do_res: loop {

      match stack.pop() {

        // Done, we're at top level.
        None => return Ok(result),

        // Work on the next frame.
        Some(
          (ZipFrame { thing, typ, mut lft_args, rgt_args }, old_subst)
        ) => {
          subst = old_subst ;

          // Update left args.
          lft_args.push( result ) ;

          if rgt_args.len() == 0 {
            result = app_do(thing, typ, lft_args) ? ;

            continue 'inspect_do_res
          } else {

            match partial(
              ZipFrame { thing, typ, lft_args, rgt_args }
            ) ? {

              ZipDo::Trm { nu_term, frame } => {
                term = nu_term ;
                stack.push( (frame, subst.clone()) ) ;
                continue 'inspect_term
              },

              ZipDo::Dwn { nu_term, nu_subst } => {
                if let Some(nu_subst) = nu_subst {
                  subst = Some(nu_subst)
                }
                term = nu_term ;
                continue 'inspect_term
              },

              ZipDo::Upp { yielded } => {
                result = yielded ;
                continue 'inspect_do_res
              },
            }
          }
        },
      }
    }
  }
}


