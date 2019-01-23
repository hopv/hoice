//! Zipper over terms.
//!
//! # TODO
//!
//! - explain

use std::{fmt, slice::Iter};

use crate::common::*;

/// The direction of the next step.
///
/// This is essentially a command from the exterior (the caller) to the zipper
/// telling it which way it will go next.
#[derive(Clone, Debug)]
pub enum ZipDo<'a, Acc, Yield> {
    /// Remember a frame and inspect a term.
    Trm {
        /// The new term to work on.
        nu_term: &'a Term,
        /// The frame (application) inside of which we are.
        frame: ZipFrame<'a, Acc>,
    },

    /// Go down. Means "skip the current application and go directly to this".
    ///
    /// Example: when evaluating an `(ite c t e)` application: given the value of
    /// `c`, when want to go down into `t` or `e` directly, not evaluate both.
    Dwn {
        /// The term we're going down in.
        nu_term: &'a Term,
    },

    /// Go up. Means "here is the result, skip everything else at this level".
    ///
    /// Example: when evaluating a `(* a0 a1 ...)` application. If `a0` evaluates
    /// to `0` then we can go up directly with `0`.
    Upp {
        /// The result to propagate upwards.
        yielded: Yield,
    },
}

/// The direction of the next step, total version.
///
/// This is what the user produces when zipping up an application and all of
/// its arguments.
pub enum ZipDoTotal<'a, Yield> {
    /// Going down.
    ///
    /// The only use case here is function application.
    Dwn {
        /// Term we're going down in.
        nu_term: &'a Term,
        /// An optional substitution.
        ///
        /// The only case where this is useful currently is when evaluating a
        /// function application.
        nu_subst: Option<VarMap<Yield>>,
    },

    /// Go up. Result.
    Upp {
        /// The result to propagate upwards.
        yielded: Yield,
    },
}

/// The operators manipulated by the zipper.
#[derive(Clone, Copy, Debug)]
pub enum ZipOp<'a> {
    /// An operator.
    Op(Op),
    /// A datatype constructor.
    New(&'a String),
    /// A function application.
    Fun(&'a String),
    /// A constant array construction.
    CArray,
    /// A datatype selection.
    Slc(&'a String),
    /// A datatype tester.
    Tst(&'a String),
}
impl<'a> ::std::fmt::Display for ZipOp<'a> {
    fn fmt(&self, fmt: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        match self {
            ZipOp::Op(inner) => write!(fmt, "Op({})", inner),
            ZipOp::New(inner) => write!(fmt, "New({})", inner),
            ZipOp::Fun(inner) => write!(fmt, "Fun({})", inner),
            ZipOp::Slc(inner) => write!(fmt, "Slc({})", inner),
            ZipOp::Tst(inner) => write!(fmt, "Tst({})", inner),
            ZipOp::CArray => write!(fmt, "array"),
        }
    }
}

// Nullary things the zipper can manipulate.
#[derive(Clone, Copy, Debug)]
pub enum ZipNullary<'a> {
    /// A constant.
    Cst(&'a Val),
    /// A variable.
    Var(&'a Typ, VarIdx),
}
impl<'a> fmt::Display for ZipNullary<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ZipNullary::Cst(val) => write!(fmt, "{}", val),
            ZipNullary::Var(typ, var) => write!(fmt, "v_{}<{}>", var, typ),
        }
    }
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
    pub typ: &'a Typ,
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
    fn new_empty(capa: usize) -> Self;
    /// Pushes a new element in the accumulator.
    fn push(&mut self, elem: Elem);
}
impl<T> Accumulator<T> for Vec<T> {
    fn new_empty(hint: usize) -> Self {
        Vec::with_capacity(hint)
    }
    fn push(&mut self, elem: T) {
        self.push(elem)
    }
}
impl<T: Ord> Accumulator<T> for BTreeSet<T> {
    fn new_empty(_: usize) -> Self {
        BTreeSet::new()
    }
    fn push(&mut self, elem: T) {
        self.insert(elem);
    }
}
impl Accumulator<()> for () {
    fn new_empty(_: usize) -> Self {}
    fn push(&mut self, _: ()) {}
}

/// Zip function.
pub fn zip<E, Acc, Yield, DwnF, NulF, AppF, Partial>(
    term: &Term,
    mut dwn_do: DwnF,
    mut nul_do: NulF,
    mut app_do: AppF,
    mut partial: Partial,
) -> Result<Yield, E>
where
    Acc: Accumulator<Yield>,
    Yield: Clone,

    DwnF: for<'a> FnMut(&'a Term) -> Result<Option<Yield>, E>,

    NulF: for<'a> FnMut(ZipNullary<'a>) -> Result<Yield, E>,

    AppF: for<'a> FnMut(ZipOp<'a>, &'a Typ, Acc) -> Result<ZipDoTotal<'a, Yield>, E>,

    Partial: for<'a> FnMut(ZipFrame<'a, Acc>) -> Result<ZipDo<'a, Acc, Yield>, E>,
{
    zip_with(
        term,
        &(),
        |_, term| dwn_do(term),
        |_, nul| nul_do(nul),
        |_, op, typ, acc| app_do(op, typ, acc),
        |_, frame| partial(frame),
    )
}

/// Zip function.
pub fn zip_with<Info, E, Acc, Yield, DwnF, NulF, AppF, Partial>(
    term: &Term,
    info: &Info,
    mut dwn_do: DwnF,
    mut nul_do: NulF,
    mut app_do: AppF,
    mut partial: Partial,
) -> Result<Yield, E>
where
    Acc: Accumulator<Yield>,
    Yield: Clone,

    DwnF: for<'a> FnMut(&'a Info, &'a Term) -> Result<Option<Yield>, E>,

    NulF: for<'a> FnMut(&'a Info, ZipNullary<'a>) -> Result<Yield, E>,

    AppF: for<'a> FnMut(&'a Info, ZipOp<'a>, &'a Typ, Acc) -> Result<ZipDoTotal<'a, Yield>, E>,

    Partial: for<'a> FnMut(&'a Info, ZipFrame<'a, Acc>) -> Result<ZipDo<'a, Acc, Yield>, E>,
{
    // Empty vector of terms, useful when handling unary operators.
    let empty: Vec<Term> = Vec::with_capacity(0);

    // Current term we're going down in.
    let mut term = term;

    // Stack of `ZipFrame`.
    let mut stack: Vec<_> = Vec::with_capacity(7);
    // The current substitution, if any.
    let mut subst: Option<VarMap<Yield>> = None;

    // macro_rules! stack_print {
    //   () => ({
    //     println!("stack {{") ;
    //     for (ZipFrame { thing, rgt_args, .. }, _) in & stack {
    //       println!("  {} > {}", thing, rgt_args.len())
    //     }
    //     println!("}}")
    //   }) ;
    // }

    'inspect_term: loop {
        // stack_print!() ;

        let result = if let Some(yielded) = dwn_do(info, term)? {
            ZipDoTotal::Upp { yielded }
        } else {
            match *term.get() {
                RTerm::Var(ref typ, var_idx) => {
                    if let Some(subst) = subst.as_ref() {
                        ZipDoTotal::Upp {
                            yielded: subst[var_idx].clone(),
                        }
                    } else {
                        ZipDoTotal::Upp {
                            yielded: nul_do(info, ZipNullary::Var(typ, var_idx))?,
                        }
                    }
                }

                RTerm::Cst(ref cst) => ZipDoTotal::Upp {
                    yielded: nul_do(info, ZipNullary::Cst(cst))?,
                },

                RTerm::CArray {
                    ref typ,
                    term: ref nu_term,
                    ..
                } => {
                    let frame = ZipFrame {
                        thing: ZipOp::CArray,
                        typ,
                        lft_args: Acc::new_empty(1),
                        rgt_args: empty.iter(),
                    };
                    stack.push((frame, subst.clone()));
                    term = nu_term;

                    continue 'inspect_term;
                }

                RTerm::App {
                    op,
                    ref typ,
                    ref args,
                    ..
                } => {
                    let mut rgt_args = args.iter();
                    let op = ZipOp::Op(op);
                    let lft_args = Acc::new_empty(args.len());

                    if let Some(nu_term) = rgt_args.next() {
                        let frame = ZipFrame {
                            thing: op,
                            typ,
                            lft_args,
                            rgt_args,
                        };
                        stack.push((frame, subst.clone()));
                        term = nu_term;

                        continue 'inspect_term;
                    } else {
                        app_do(info, op, typ, lft_args)?
                    }
                }

                RTerm::DTypNew {
                    ref typ,
                    ref name,
                    ref args,
                    ..
                } => {
                    let mut rgt_args = args.iter();
                    let op = ZipOp::New(name);
                    let lft_args = Acc::new_empty(args.len());

                    if let Some(nu_term) = rgt_args.next() {
                        let frame = ZipFrame {
                            thing: op,
                            typ,
                            lft_args,
                            rgt_args,
                        };
                        stack.push((frame, subst.clone()));
                        term = nu_term;

                        continue 'inspect_term;
                    } else {
                        app_do(info, op, typ, lft_args)?
                    }
                }

                RTerm::DTypSlc {
                    ref typ,
                    ref name,
                    term: ref nu_term,
                    ..
                } => {
                    let rgt_args = empty.iter();
                    let op = ZipOp::Slc(name);
                    let lft_args = Acc::new_empty(1);

                    let frame = ZipFrame {
                        thing: op,
                        typ,
                        lft_args,
                        rgt_args,
                    };
                    stack.push((frame, subst.clone()));
                    term = nu_term;

                    continue 'inspect_term;
                }

                RTerm::DTypTst {
                    ref typ,
                    ref name,
                    term: ref nu_term,
                    ..
                } => {
                    let rgt_args = empty.iter();
                    let op = ZipOp::Tst(name);
                    let lft_args = Acc::new_empty(1);

                    let frame = ZipFrame {
                        thing: op,
                        typ,
                        lft_args,
                        rgt_args,
                    };
                    stack.push((frame, subst.clone()));
                    term = nu_term;

                    continue 'inspect_term;
                }

                RTerm::Fun {
                    ref typ,
                    ref name,
                    ref args,
                    ..
                } => {
                    let mut rgt_args = args.iter();
                    let op = ZipOp::Fun(name);
                    let lft_args = Acc::new_empty(args.len());

                    if let Some(nu_term) = rgt_args.next() {
                        let frame = ZipFrame {
                            thing: op,
                            typ,
                            lft_args,
                            rgt_args,
                        };
                        stack.push((frame, subst.clone()));
                        term = nu_term;

                        continue 'inspect_term;
                    } else {
                        app_do(info, op, typ, lft_args)?
                    }
                }
            }
        };

        let mut result = match result {
            ZipDoTotal::Dwn { nu_term, nu_subst } => {
                if nu_subst.is_some() {
                    subst = nu_subst
                }
                term = nu_term;

                continue 'inspect_term;
            }

            ZipDoTotal::Upp { yielded } => yielded,
        };

        'inspect_do_res: loop {
            // stack_print!() ;

            match stack.pop() {
                // Done, we're at top level.
                None => return Ok(result),

                // Work on the next frame.
                Some((
                    ZipFrame {
                        thing,
                        typ,
                        mut lft_args,
                        rgt_args,
                    },
                    old_subst,
                )) => {
                    subst = old_subst;

                    // Update left args.
                    lft_args.push(result);

                    if rgt_args.len() == 0 {
                        match app_do(info, thing, typ, lft_args)? {
                            ZipDoTotal::Upp { yielded } => {
                                result = yielded;
                                continue 'inspect_do_res;
                            }

                            ZipDoTotal::Dwn { nu_term, nu_subst } => {
                                if nu_subst.is_some() {
                                    subst = nu_subst
                                }
                                term = nu_term;
                                continue 'inspect_term;
                            }
                        }
                    } else {
                        match partial(
                            info,
                            ZipFrame {
                                thing,
                                typ,
                                lft_args,
                                rgt_args,
                            },
                        )? {
                            ZipDo::Trm { nu_term, frame } => {
                                term = nu_term;
                                stack.push((frame, subst.clone()));
                                continue 'inspect_term;
                            }

                            ZipDo::Dwn { nu_term } => {
                                term = nu_term;
                                continue 'inspect_term;
                            }

                            ZipDo::Upp { yielded } => {
                                result = yielded;
                                continue 'inspect_do_res;
                            }
                        }
                    }
                }
            }
        }
    }
}
