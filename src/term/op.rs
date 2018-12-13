//! Operators.

use crate::common::*;

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
    pub fn as_str(self) -> &'static str {
        use self::Op::*;
        use crate::keywords::op::*;
        match self {
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
    pub fn type_check(self, args: &mut [Term]) -> Result<Typ, term::TypError> {
        use self::Op::*;

        macro_rules! err {
            (lft $($lft:tt)*) => (
                return Err( term::TypError::typ($($lft)*) )
            ) ;

            (rgt $($lft:tt)*) => (
                return Err( term::TypError::msg( format!($($lft)*)) )
            ) ;

            (nullary) => (
                err!(rgt
                    "illegal nullary application of `{}`", self
                )
            ) ;
        }

        macro_rules! arity_check {
            ( [ $min:tt, . ] => $e:expr ) => {
                if args.len() < $min {
                    err!(rgt
                                        "illegal application of `{}` to {} arguments (> {})",
                                        self, args.len(), $min
                                    )
                } else {
                    $e
                }
            };

            ( [ $min:tt, $max:tt ] => $e:expr ) => {
                if args.len() > $max {
                    err!(rgt
                                        "illegal application of `{}` to {} arguments (> {})",
                                        self, args.len(), $max
                                    )
                } else {
                    arity_check!( [ $min, .] => $e )
                }
            };
        }

        macro_rules! all_same {
            (arith) => {{
                let mut args_iter = args.iter_mut().enumerate();
                if let Some((index, fst)) = args_iter.next() {
                    let typ = fst.typ();
                    if !typ.is_arith() {
                        err!(lft None, typ, index)
                    }
                    for (index, next) in args_iter {
                        if typ != next.typ() {
                            err!(lft Some(typ), next.typ(), index)
                        }
                    }
                    typ
                } else {
                    err!(nullary)
                }
            }};

            (bool) => {{
                let args_iter = args.iter_mut().enumerate();
                for (index, fst) in args_iter {
                    let typ = fst.typ();
                    if typ != typ::bool() {
                        err!(lft Some(typ::bool()), typ, index)
                    }
                }
                typ::bool()
            }};

            () => {
                all_same!( sub args args.iter_mut().enumerate() )
            };

            (sub args $args:expr) => {{
                let mut args_iter = $args;
                if let Some((_, fst)) = args_iter.next() {
                    // println!("all same") ;
                    let mut typ = fst.typ();
                    // println!("  {} | {}", typ, fst) ;
                    for (index, next) in args_iter {
                        let next_typ = next.typ();
                        // println!("  {} | {}", next_typ, next) ;
                        if let Some(merged_typ) = typ.merge(&next_typ) {
                            // println!("  nu_typ: {}", merged_typ) ;
                            if let Some(nu) = fst.force_dtyp(merged_typ.clone()) {
                                typ = merged_typ.clone();
                                *fst = nu;
                                // println!("  -> {}", fst)
                                // println!("{}: {}", fst, fst.typ()) ;
                            }
                            if let Some(nu) = next.force_dtyp(merged_typ) {
                                // println!("  -> {} {}", nu, nu.typ()) ;
                                *next = nu;
                                // println!("     {} {}", next, next.typ())
                                // println!("{}: {}", next, next.typ()) ;
                            }
                        } else {
                            err!(lft Some(typ), next.typ(), index)
                        }
                    }
                    typ
                } else {
                    err!(nullary)
                }
            }};

            ($typ:expr) => {{
                for (index, fst) in args.iter_mut().enumerate() {
                    if fst.typ() != $typ {
                        err!(lft Some($typ), fst.typ(), index)
                    }
                }
                $typ
            }};
        }

        let res = match self {
            Add | Sub | Mul | Div | CMul => all_same!(arith),
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

            Distinct | Eql => {
                all_same!();
                typ::bool()
            }
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
              [ 3, 3 ] => {
                let mut args_iter = args.iter_mut().enumerate() ;

                if let Some((index, cond)) = args_iter.next() {
                  if ! cond.typ().is_bool() {
                    err!(lft Some(typ::bool()), cond.typ(), index)
                  }
                  all_same!(sub args args_iter)
                } else {
                  err!(nullary)
                }
              }
            ),

            Store => arity_check!(
              [ 3, 3 ] => if let Some((src, tgt)) = args[0].typ().array_inspect() {
                if args[1].typ() != * src {
                  err!(
                    lft Some(src.clone()), args[1].typ(), 1
                  )
                } else if args[2].typ() != * tgt {
                  err!(
                    lft Some(tgt.clone()), args[2].typ(), 2
                  )
                } else {
                  args[0].typ()
                }
              } else {
                err!(lft None, args[0].typ(), 0)
              }
            ),

            Select => arity_check!(
              [ 2, 2 ] => if let Some((src, tgt)) = args[0].typ().array_inspect() {
                if args[1].typ() != * src {
                  err!(
                    lft Some(src.clone()), args[1].typ(), 1
                  )
                } else {
                  tgt.clone()
                }
              } else {
                err!(lft None, args[0].typ(), 0)
              }
            ),
        };
        Ok(res)
    }

    /// Evaluation.
    pub fn eval(self, args: Vec<Val>) -> Res<Val> {
        use self::Op::*;
        if args.is_empty() {
            bail!("evaluating operator on 0 elements")
        }

        match self {
            // Arithmetic operators.
            Add => eval::add(args),
            Sub => eval::sub(args),
            CMul | Mul => eval::mul(args),
            Div => eval::div(args),
            IDiv => eval::idiv(args),
            Rem => eval::rem(args),
            Mod => eval::modulo(args),

            // Relations over arithmetic.
            Gt => eval::gt(args),
            Ge => eval::ge(args),
            Le => eval::le(args),
            Lt => eval::lt(args),

            // Polymorphic operators.
            Distinct => eval::distinct(args),
            Eql => eval::eql(args),
            Ite => eval::ite(args),

            // Boolean operators.
            Not => eval::not(args),
            And => eval::and(args),
            Or => eval::or(args),
            Impl => eval::implies(args),

            // Cast operators.
            ToInt => eval::to_int(args),
            ToReal => eval::to_real(args),

            // Array operators.
            Store => eval::store(args),
            Select => eval::select(args),
        }
    }
}
mylib::impl_fmt! {
  Op(self, fmt) {
    fmt.write_str( self.as_str() )
  }
}

/// Evaluation-related stuff.
mod eval {
    use crate::common::*;

    /// Applies an operation on arithmetic arguments.
    macro_rules! arith_app {
        (relation $op:tt $str:tt => $args:expr) => {{
            let mut args = $args.into_iter();
            if let (Some(fst), Some(mut pre)) = (args.next(), args.next()) {
                let mut res = fst.get().$op(&pre)?;

                for arg in args {
                    res = res.and(&pre.get().$op(&arg)?)?;
                    pre = arg
                }
                Ok(res)
            } else {
                bail!("`{}` applied to 0 or 1 argument(s)")
            }
        }};
        ($op:tt $str:tt => $args:expr) => {{
            let mut args = $args.into_iter();
            if let Some(mut acc) = args.next() {
                for arg in args {
                    acc = acc.$op(&arg)?
                }
                Ok(acc)
            } else {
                bail!("`{}` applied to zero arguments", $str)
            }
        }};
    }

    /// Arity check.
    macro_rules! arity {
        ($op:expr => $args:expr, $len:expr) => {
            if $args.len() != $len {
                bail!(
                    "illegal application of `{}` to {} arguments",
                    $op,
                    $args.len()
                )
            }
        };
    }

    /// Creates an evaluation function.
    macro_rules! eval_fun {
        ( $(fn $name:ident($args:pat) $body:expr);* $(;)* ) => (
            $(
                pub fn $name($args: Vec<Val>) -> Res<Val> { $body }
            )*
        ) ;
    }

    // Arithmetic operators.

    eval_fun! {
        // Addition.
        fn add(args) arith_app!(add "+" => args) ;

        // Subtraction.
        fn sub(mut args) if args.len() == 1 {
            args.pop().unwrap().minus()
        } else {
            arith_app!(sub "-" => args)
        } ;

        // Multiplication
        fn mul(args) arith_app!(mul "*" => args) ;

        // Division.
        fn div(args) arith_app!(div "/" => args) ;

        // Integer division.
        fn idiv(args) {
            arity!("div" => args, 2) ;
            args[0].idiv(& args[1])
        } ;

        // Remainder.
        fn rem(args) {
            arity!("rem" => args, 2) ;
            args[0].rem(& args[1])
        } ;

        // Modulo.
        fn modulo(args) {
            arity!("mod" => args, 2) ;
            args[0].modulo(& args[1])
        } ;
    }

    // Relations over arithmetic.
    eval_fun! {
        // Greater than.
        fn gt(args) arith_app!(relation g_t ">"  => args) ;
        // Greater than or equal to.
        fn ge(args) arith_app!(relation g_e ">=" => args) ;
        // Less than.
        fn lt(args) arith_app!(relation l_t "<"  => args) ;
        // Less than or equal to.
        fn le(args) arith_app!(relation l_e "<=" => args) ;
    }

    // Polymorphic operators.
    eval_fun! {
        // Distinct.
        fn distinct(mut args) {
            while let Some(arg) = args.pop() {
                for other in & args {
                    if let Some(equal) = arg.eql(& other).to_bool() ? {
                        if equal {
                            return Ok( val::bool(false) )
                        }
                    } else {
                        return Ok( val::none( typ::bool() ) )
                    }
                }
            }
            Ok( val::bool(true) )
        } ;

        // Equal.
        fn eql(mut args) {
            if let Some(fst) = args.pop() {
                for other in & args {
                    if let Some(equal) = fst.eql(other).to_bool() ? {
                        if ! equal {
                            return Ok( val::bool(false) )
                        }
                    } else {
                        return Ok( val::none( typ::bool() ) )
                    }
                }
            }
            Ok( val::bool(true) )
        } ;

        // If-then-else.
        fn ite(mut args) {
            arity!("ite" => args, 3) ;
            let (els, thn, cnd) = (
                args.pop().unwrap(), args.pop().unwrap(), args.pop().unwrap()
            ) ;
            cnd.ite(thn, els)
        }
    }

    // Boolean operators.
    eval_fun! {
        // Not.
        fn not(args) {
            arity!("not" => args, 1) ;
            args[0].not()
        } ;

        // Conjunction.
        fn and(args) {
            for arg in args {
                match arg.to_bool() ? {
                    Some(true) => (),
                    Some(false) => return Ok( val::bool(false) ),
                    None => return Ok( val::none( typ::bool() ) ),
                }
            }
            Ok( val::bool(true) )
        } ;

        // Disjunction.
        fn or(args) {
            let mut res = val::bool(false) ;
            for arg in args {
                match arg.to_bool() ? {
                    Some(true) => return Ok( val::bool(true) ),
                    Some(false) => (),
                    None => res = val::none( typ::bool() ),
                }
            }
            Ok(res)
        } ;

        // Implication.
        fn implies(args) {
            arity!("=>" => args, 2) ;
            args[0].implies( & args[1] )
        } ;
    }

    // Cast operators.
    eval_fun! {
        // To int.
        fn to_int(args) {
            arity!("to-int" => args, 1) ;
            args[0].real_to_int()
        } ;

        // To real.
        fn to_real(args) {
            arity!("to-real" => args, 1) ;
            args[0].int_to_real()
        } ;
    }

    // Array operators.
    eval_fun! {
        // Store.
        fn store(mut args) {
            arity!("store" => args, 3) ;
            let (val, idx, array) = (
                args.pop().unwrap(),
                args.pop().unwrap(),
                args.pop().unwrap(),
            ) ;
            Ok( array.store(idx, val) )
        } ;

        // Select.
        fn select(mut args) {
            arity!("select" => args, 2) ;
            let (idx, array) = (
                args.pop().unwrap(),
                args.pop().unwrap(),
            ) ;
            Ok( array.select(idx) )
        } ;
    }

}
