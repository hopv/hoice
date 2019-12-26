//! Hashconsed terms.
//!
//! # Terms
//!
//! The factory is a `static_ref` for easy creation. The `R`eal term structure is [`RTerm`] which
//! is hashconsed into [`Term`]. The factory ([`HashConsign`]) is not directly accessible. Terms
//! are created *via* the functions in this module, such as [`var`], [`int`], [`app`], *etc.* Terms
//! are simplified (when possible) at creation. In particular, the order of the arguments can
//! change, double negations will be simplified, *etc.*
//!
//! A predicate application is **not** a term, only operator applications are.
//!
//! # Top-level terms
//!
//! A [`TTerm`] is either a term or a predicate application to some terms. Top-level terms are not
//! hashconsed as they are shallow.
//!
//! # Variables
//!
//! A variable is a `usize` wrapped in a zero-cost [`VarIdx`] for safety. It has no semantics at
//! all by itself. Variables are given meaning by the `sig` field of a [`Pred`] or the [`VarInfo`]s
//! stored in a [`Clause`].
//!
//! [`RTerm`]: enum.RTerm.html (RTerm enum)
//! [`Term`]: type.Term.html (Term type)
//! [`HashConsign`]: https://crates.io/crates/hashconsing (hashconsing crate)
//! [`var`]: fn.var.html (var creation function)
//! [`int`]: fn.int.html (int creation function)
//! [`app`]: fn.app.html (app creation function)
//! [`TTerm`]: enum.tterm.html (top term enum)
//! [`VarIdx`]: ../common/struct.VarIdx.html (variable index struct)
//! [`Clause`]: ../common/struct.Clause.html (Clause struct)
//! [`VarInfo`]: ../info/struct.VarInfo.html (VarInfo struct)
//! [`Pred`]: ../info/struct.Pred.html (Pred struct)
//!
//! # Examples
//!
//! ```rust
//! # use hoice::{ term, term::{ Op, RTerm, typ } } ;
//! let some_term = term::eq(
//!     term::int(11), term::app(
//!         Op::Mul, vec![ term::int_var(5), term::int(2) ]
//!     )
//! ) ;
//! # println!("{}", some_term) ;
//!
//! // A `Term` dereferences to an `RTerm`:
//! match * some_term {
//!     RTerm::App { ref typ, op: Op::Eql, ref args, .. } => {
//!         assert_eq!( typ, & typ::bool() ) ;
//!         assert_eq!( args.len(), 2 ) ;
//!         assert_eq!( format!("{}", some_term), "(= (+ (* (- 2) v_5) 11) 0)" )
//!     },
//!     _ => panic!("not an equality"),
//! }
//! ```

use hashconsing::*;

use crate::common::*;

#[macro_use]
mod op;
pub mod bindings;
mod eval;
mod factory;
mod leaf_iter;
pub mod simplify;
mod tterms;
pub mod typ;
mod zip;

pub use self::bindings::Bindings;
pub use self::factory::*;
pub use self::leaf_iter::LeafIter;
pub use self::op::*;
pub use self::tterms::*;
pub use self::typ::Typ;

#[cfg(test)]
mod test;

/// Hash consed term.
pub type Term = HConsed<RTerm>;

/// A real term, before hashconsing.
///
/// See the [module level documentation] for more details.
///
/// [module level documentation]: ../term/index.html (term module)
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum RTerm {
    /// A clause variable.
    Var(Typ, VarIdx),

    /// A constant.
    Cst(Val),

    /// A constant array.
    ///
    /// The type is the type of **the indices** of the arrays.
    ///
    /// A constant array is not (necessarily) a (constant) value. It is an array which maps all
    /// indices to the same term.
    CArray {
        /// Depth of this term.
        depth: usize,
        /// Type of **the indices** (not the array).
        typ: Typ,
        /// Default term of the array.
        term: Term,
    },

    /// An operator application.
    App {
        /// Depth of this term.
        depth: usize,
        /// Type of the application.
        typ: Typ,
        /// The operator.
        op: Op,
        /// The arguments.
        args: Vec<Term>,
    },

    /// A datatype constructor application.
    DTypNew {
        /// Depth of this term.
        depth: usize,
        /// Type of the application.
        typ: Typ,
        /// Name of the constructor.
        name: String,
        /// Arguments of the constructor.
        args: Vec<Term>,
    },

    /// A datatype selector application.
    DTypSlc {
        /// Depth of this term.
        depth: usize,
        /// Type of the application.
        typ: Typ,
        /// Name of the selector.
        name: String,
        /// Argument of the selector.
        term: Term,
    },

    /// A datatype tester application.
    DTypTst {
        /// Depth of this term.
        depth: usize,
        /// Type of the term (always bool).
        typ: Typ,
        /// Name of the tester.
        name: String,
        /// Argument of the selector.
        term: Term,
    },

    /// A function application.
    Fun {
        /// Depth of this term.
        depth: usize,
        /// Type of this term.
        typ: Typ,
        /// Function being applied.
        name: String,
        /// Arguments of the function application.
        args: Vec<Term>,
    },
}

/// Constructors.
impl RTerm {
    /// Constructs an operator application.
    fn new_app(typ: Typ, op: Op, args: Vec<Term>) -> Self {
        let depth = args
            .iter()
            .fold(1, |acc, term| ::std::cmp::max(acc, term.depth() + 1));
        RTerm::App {
            depth,
            typ,
            op,
            args,
        }
    }

    /// Constructs a function application.
    fn new_fun<S>(typ: Typ, name: S, args: Vec<Term>) -> Self
    where
        S: Into<String>,
    {
        let depth = args
            .iter()
            .fold(1, |acc, term| ::std::cmp::max(acc, term.depth() + 1));
        let name = name.into();
        RTerm::Fun {
            depth,
            typ,
            name,
            args,
        }
    }

    /// Constructs a constant array.
    ///
    ///
    fn new_carray(typ: Typ, term: Term) -> Self {
        RTerm::CArray {
            depth: term.depth() + 1,
            typ,
            term,
        }
    }

    /// Constructs a datatype selector application.
    fn new_dtyp_slc<S>(typ: Typ, name: S, term: Term) -> Self
    where
        S: Into<String>,
    {
        let name = name.into();
        RTerm::DTypSlc {
            depth: term.depth() + 1,
            typ,
            name,
            term,
        }
    }

    /// Constructs a datatype tester application.
    fn new_dtyp_tst<S>(typ: Typ, name: S, term: Term) -> Self
    where
        S: Into<String>,
    {
        let name = name.into();
        RTerm::DTypTst {
            depth: term.depth() + 1,
            typ,
            name,
            term,
        }
    }

    /// Constructs a datatype constructor application.
    fn new_dtyp_new<S>(typ: Typ, name: S, args: Vec<Term>) -> Self
    where
        S: Into<String>,
    {
        let name = name.into();
        let depth = args
            .iter()
            .fold(1, |acc, term| ::std::cmp::max(acc, term.depth() + 1));
        RTerm::DTypNew {
            depth,
            typ,
            name,
            args,
        }
    }
}

/// Accessors and testers.
impl RTerm {
    /// Size of a term: number of subterms.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::term;
    /// let term = term::eq(
    ///     term::add(vec![
    ///         term::cmul( 2, term::int_var(0) ),
    ///         term::int_var(1)
    ///     ]), term::int(7)
    /// );
    /// assert_eq! { term.depth(), 4 }
    /// ```
    pub fn depth(&self) -> usize {
        match self {
            RTerm::Var(_, _) | RTerm::Cst(_) => 1,
            RTerm::CArray { depth, .. }
            | RTerm::App { depth, .. }
            | RTerm::DTypNew { depth, .. }
            | RTerm::DTypSlc { depth, .. }
            | RTerm::DTypTst { depth, .. }
            | RTerm::Fun { depth, .. } => *depth,
        }
    }

    /// Type of the term.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::term;
    /// let sum = term::add(vec![
    ///     term::cmul( 2, term::int_var(0) ),
    ///     term::int_var(1)
    /// ]);
    /// assert! { sum.typ().is_int() }
    ///
    /// let to_real = term::to_real(sum);
    /// assert! { to_real.typ().is_real() }
    ///
    /// let term = term::eq(
    ///     to_real, term::real_of(7.0)
    /// );
    /// assert! { term.typ().is_bool() }
    /// ```
    pub fn typ(&self) -> Typ {
        match self {
            RTerm::CArray { typ, term, .. } => typ::array(typ.clone(), term.typ()),

            RTerm::Cst(val) => val.typ(),

            RTerm::Var(typ, _)
            | RTerm::App { typ, .. }
            | RTerm::Fun { typ, .. }
            | RTerm::DTypSlc { typ, .. }
            | RTerm::DTypTst { typ, .. }
            | RTerm::DTypNew { typ, .. } => typ.clone(),
        }
    }

    /// Returns the variable index if the term is a variable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::term;
    /// let v_1 = term::int_var(1);
    /// assert_eq! { v_1.var_idx(), Some(1.into()) }
    ///
    /// let mul = term::cmul( 2, v_1 );
    /// assert_eq! { mul.var_idx(), None }
    /// ```
    pub fn var_idx(&self) -> Option<VarIdx> {
        match *self {
            RTerm::Var(_, i) => Some(i),
            _ => None,
        }
    }

    /// True if the term is zero (integer or real).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::term;
    /// let one = term::int(1);
    /// assert! { ! one.is_zero() }
    ///
    /// let sum = term::add( vec![one.clone(), term::u_minus(one)] );
    /// assert! { sum.is_zero() }
    /// ```
    pub fn is_zero(&self) -> bool {
        match (self.int(), self.real()) {
            (Some(i), _) => i.is_zero(),
            (_, Some(r)) => r.is_zero(),
            _ => false,
        }
    }

    /// True if the term is one (integer or real).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::term;
    /// let one = term::int(1);
    /// assert! { one.is_one() }
    ///
    /// let sum = term::add( vec![one.clone(), term::u_minus(one)] );
    /// assert! { ! sum.is_one() }
    /// ```
    pub fn is_one(&self) -> bool {
        match (self.int(), self.real()) {
            (Some(i), _) => i == Int::one(),
            (_, Some(r)) => r == Rat::one(),
            _ => false,
        }
    }

    /// Compares two terms as a conjunction.
    ///
    /// Returns
    ///
    /// - `None` if no conclusion was reached,
    /// - `Some(Greater)` if `lhs => rhs`,
    /// - `Some(Less)` if `lhs <= rhs`,
    /// - `Some(Equal)` if `lhs` and `rhs` are equivalent.
    ///
    /// So *greater* really means *stronger*.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::cmp::Ordering::*;
    /// use hoice::{ term, term::simplify::SimplRes::* };
    /// let eq = &term::eq( term::int_var(0), term::int(7) );
    /// let ge = &term::ge( term::int_var(0), term::int(7) );
    /// let gt = &term::gt( term::int_var(0), term::int(7) );
    /// let ge_2 = &term::ge( term::int(7), term::int_var(0) );
    ///
    /// # println!("{} cmp {}", eq, eq);
    /// assert_eq! { eq.conj_cmp(eq), Cmp(Equal  ) }
    /// # println!("{} cmp {}", eq, ge);
    /// assert_eq! { eq.conj_cmp(ge), Cmp(Greater) }
    /// # println!("{} cmp {}", ge, eq);
    /// assert_eq! { ge.conj_cmp(eq), Cmp(Less   ) }
    ///
    /// # println!();
    /// # println!("{} cmp {}", eq, gt);
    /// assert_eq! { eq.conj_cmp(gt), Yields(term::fls()) }
    /// # println!("{} cmp {}", gt, eq);
    /// assert_eq! { gt.conj_cmp(eq), Yields(term::fls()) }
    ///
    /// # println!();
    /// # println!("{} cmp {}", gt, ge);
    /// assert_eq! { gt.conj_cmp(ge), Cmp(Greater) }
    /// # println!("{} cmp {}", ge, gt);
    /// assert_eq! { ge.conj_cmp(gt), Cmp(Less   ) }
    ///
    /// # println!();
    /// # println!("{} cmp {}", ge, ge_2);
    /// assert_eq! { ge.conj_cmp(ge_2), Yields(eq.clone()) }
    /// # println!("{} cmp {}", ge_2, ge);
    /// assert_eq! { ge_2.conj_cmp(ge), Yields(eq.clone()) }
    /// ```
    pub fn conj_cmp(&self, other: &Self) -> simplify::SimplRes {
        simplify::conj_simpl(&self, &other)
    }

    /// True if the term has no variables and evaluates to true.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::{ term, term::Op };
    /// let term = term::tru() ;
    /// println!("true") ;
    /// assert!( term.is_true() ) ;
    /// let term = term::fls() ;
    /// println!("false") ;
    /// assert!( ! term.is_true() ) ;
    /// let term = term::eq(
    ///     term::int(7), term::int_var(1)
    /// ) ;
    /// println!("7 = v_1") ;
    /// assert!( ! term.is_true() ) ;
    /// let term = term::eq(
    ///     term::int(9), term::int(9)
    /// ) ;
    /// println!("9 = 9") ;
    /// assert!( term.is_true() ) ;
    /// let term = term::eq(
    ///     term::int(1), term::int(9)
    /// ) ;
    /// println!("1 = 9") ;
    /// assert!( ! term.is_true() ) ;
    /// let term = term::le(
    ///     term::app(
    ///         Op::Add, vec![ term::int(3), term::int(4) ]
    ///     ), term::int(9)
    /// ) ;
    /// println!("3 + 4 = 9") ;
    /// assert!( term.is_true() ) ;
    /// ```
    pub fn is_true(&self) -> bool {
        match self.bool_eval(&()) {
            Ok(Some(b)) => b,
            _ => false,
        }
    }

    /// True if the term has no variables and evaluates to true.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::{term, term::Op};
    /// let term = term::tru() ;
    /// println!("true") ;
    /// assert!( ! term.is_false() ) ;
    /// let term = term::fls() ;
    /// println!("false") ;
    /// assert!( term.is_false() ) ;
    /// let term = term::eq(
    ///     term::int(7), term::int_var(1)
    /// ) ;
    /// println!("7 = v_1") ;
    /// assert!( ! term.is_false() ) ;
    /// let term = term::eq(
    ///     term::int(9), term::int(9)
    /// ) ;
    /// println!("9 = 9") ;
    /// assert!( ! term.is_false() ) ;
    /// let term = term::eq(
    ///     term::int(1), term::int(9)
    /// ) ;
    /// println!("1 = 9") ;
    /// assert!( term.is_false() ) ;
    /// let term = term::le(
    ///     term::int(9), term::app(
    ///         Op::Add, vec![ term::int(3), term::int(4) ]
    ///     )
    /// ) ;
    /// println!("9 <= 3 + 4") ;
    /// assert!( term.is_false() ) ;
    /// ```
    pub fn is_false(&self) -> bool {
        match self.bool_eval(&()) {
            Ok(Some(b)) => !b,
            _ => false,
        }
    }

    /// Returns a constant arithmetic version of the term if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::term;
    /// let sum = term::add(vec![
    ///     term::cmul( 2, term::int(0) ),
    ///     term::int(1)
    /// ]);
    /// assert_eq! { sum.arith(), Some(term::int(1)) }
    ///
    /// let to_real = term::to_real(sum);
    /// assert_eq! { to_real.arith(), Some(term::real_of(1.0)) }
    ///
    /// let term = term::eq(
    ///     to_real, term::real_of(7.0)
    /// );
    /// assert_eq! { term.arith(), None }
    /// ```
    pub fn arith(&self) -> Option<Term> {
        if let Some(i) = self.int() {
            Some(term::int(i))
        } else if let Some(r) = self.real() {
            Some(term::real(r))
        } else {
            None
        }
    }

    /// If the term's an integer constant, returns the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::term;
    /// let one = term::int(1);
    /// assert_eq! { one.int_val(), Some(& 1.into()) }
    ///
    /// let sum = term::add(vec![term::int_var(0), one]);
    /// assert_eq! { sum.int_val(), None }
    ///
    /// let one = term::real_of(1.0);
    /// assert_eq! { one.int_val(), None }
    /// ```
    pub fn int_val(&self) -> Option<&Int> {
        if let RTerm::Cst(val) = self {
            if let val::RVal::I(i) = val.get() {
                return Some(i);
            }
        }
        None
    }

    /// If the term's a rational constant, returns the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ term, common::Rat };
    /// let one = term::real_of(1.0);
    /// assert_eq! { one.real_val(), Some(&Rat::new(1.into(),1.into())) }
    ///
    /// let sum = term::add(vec![term::real_var(0), one]);
    /// assert_eq! { sum.real_val(), None }
    ///
    /// let one = term::int(1);
    /// assert_eq! { one.real_val(), None }
    /// ```
    pub fn real_val(&self) -> Option<&Rat> {
        if let RTerm::Cst(val) = self {
            if let val::RVal::R(r) = val.get() {
                return Some(r);
            }
        }
        None
    }

    /// Return true if the term mentions at least one variable from `vars`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let mut vars = VarSet::new();
    /// vars.insert(7.into());
    /// vars.insert(5.into());
    /// vars.insert(3.into());
    ///
    /// let term = term::eq(
    ///     term::add(vec![
    ///         term::cmul( 2, term::int_var(0) ),
    ///         term::int_var(6),
    ///     ]),
    ///     term::int(0)
    /// );
    /// assert! { !term.mentions_one_of(&vars) }
    ///
    /// let term = term::eq(
    ///     term::add(vec![
    ///         term::cmul( 2, term::int_var(7) ),
    ///         term::int_var(6),
    ///     ]),
    ///     term::int(0)
    /// );
    /// assert! { term.mentions_one_of(&vars) }
    /// ```
    pub fn mentions_one_of(&self, vars: &VarSet) -> bool {
        for var_or_cst in self.leaf_iter() {
            if let Either::Left((_, var_idx)) = var_or_cst {
                if vars.contains(&var_idx) {
                    return true;
                }
            }
        }
        false
    }

    /// Collects all functions mentioned by a term.
    pub fn collect_funs(&self, set: &mut BTreeSet<String>) {
        use self::zip::*;
        zip_with(
            &self.to_hcons(),
            &::std::cell::RefCell::new(set),
            |set, term| {
                if let Some((name, _)) = term.fun_inspect() {
                    set.borrow_mut().insert(name.clone());
                }
                Ok(None) as Res<Option<()>>
            },
            |_, _| Ok(()),
            |set, zip_op, _, _: ()| {
                if let ZipOp::Fun(name) = zip_op {
                    set.borrow_mut().insert(name.clone());
                    ()
                }
                Ok(ZipDoTotal::Upp { yielded: () })
            },
            |set, mut frame| {
                if let ZipFrame {
                    thing: ZipOp::Fun(name),
                    ..
                } = frame
                {
                    set.borrow_mut().insert(name.clone());
                }

                let nu_term = frame.rgt_args.next().expect(
                    "illegal call to `partial_op`: \
                     empty `rgt_args` (has_fun_app_or_adt)",
                );
                Ok(ZipDo::Trm { nu_term, frame })
            },
        )
        .expect("error in `collect_funs`: entered unreachable code");

        ()
    }

    /// Returns true if the term mentions a function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ term, term::typ, dtyp, fun };
    /// fun::test::create_length_fun();
    /// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
    ///
    /// let t_1 = term::ge(
    ///     term::fun(
    ///         fun::test::length_fun_name(),
    ///         vec![ term::var(0, list.clone()) ]
    ///     ),
    ///     term::int(0)
    /// );
    /// assert! { t_1.has_fun_apps() }
    ///
    /// let t_2 = term::ge(
    ///     term::int_var(7),
    ///     term::int(0)
    /// );
    /// assert! { !t_2.has_fun_apps() }
    /// ```
    pub fn has_fun_apps(&self) -> bool {
        use self::zip::*;

        // Will be `Ok(())` if there's no function application, and `Err(())`
        // otherwise.
        let res = zip(
            &self.to_hcons(),
            |term| {
                if let Some((_, _)) = term.fun_inspect() {
                    Err(())
                } else {
                    Ok(None)
                }
            },
            |_| Ok(()),
            |zip_op, _, _: ()| match zip_op {
                ZipOp::Fun(_) => Err(()),
                _ => Ok(ZipDoTotal::Upp { yielded: () }),
            },
            |frame| match frame {
                ZipFrame {
                    thing: ZipOp::Fun(_),
                    ..
                } => Err(()),
                mut frame => {
                    let nu_term = frame.rgt_args.next().expect(
                        "illegal call to `partial_op`: \
                         empty `rgt_args` (has_fun_app_or_adt)",
                    );
                    Ok(ZipDo::Trm { nu_term, frame })
                }
            },
        );

        res.is_err()
    }

    /// Returns true if the term mentions a recursive function.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ term, term::typ, dtyp, fun, parse };
    /// fun::test::create_length_fun();
    /// // Adding a non-recursive function.
    /// parse::fun_dtyp("\
    ///     (define-fun get_head ( (lst (List Int)) ) Int
    ///         (head lst)
    ///     )
    /// ");
    /// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
    ///
    /// let t_1 = term::ge(
    ///     term::fun(
    ///         fun::test::length_fun_name(), vec![ term::var(0, list.clone()) ]
    ///     ),
    ///     term::int(0)
    /// );
    /// assert! { t_1.has_rec_fun_apps() }
    ///
    /// let t_2 = term::ge(
    ///     term::fun(
    ///         "get_head", vec![ term::var(0, list.clone()) ]
    ///     ),
    ///     term::int(0)
    /// );
    /// assert! { !t_2.has_rec_fun_apps() }
    ///
    /// let t_3 = term::ge(
    ///     term::int_var(7),
    ///     term::int(0)
    /// );
    /// assert! { !t_3.has_rec_fun_apps() }
    /// ```
    pub fn has_rec_fun_apps(&self) -> bool {
        use self::zip::*;

        // Will be `Ok(())` if there's no function application, and `Err(())`
        // otherwise.
        let res = zip(
            &self.to_hcons(),
            |term| {
                if let Some((name, _)) = term.fun_inspect() {
                    if fun::get(name)
                        .expect("inconsistent function application: unknown function")
                        .is_recursive()
                    {
                        Err(())
                    } else {
                        Ok(None)
                    }
                } else {
                    Ok(None)
                }
            },
            |_| Ok(()),
            |zip_op, _, _: ()| match zip_op {
                ZipOp::Fun(name)
                    if fun::get(name)
                        .expect("inconsistent function application: unknown function")
                        .is_recursive() =>
                {
                    Err(())
                }
                _ => Ok(ZipDoTotal::Upp { yielded: () }),
            },
            |frame| match frame {
                ZipFrame {
                    thing: ZipOp::Fun(name),
                    ..
                } if fun::get(name)
                    .expect("inconsistent function application: unknown function")
                    .is_recursive() =>
                {
                    Err(())
                }
                mut frame => {
                    let nu_term = frame.rgt_args.next().expect(
                        "illegal call to `partial_op`: \
                         empty `rgt_args` (has_fun_app_or_adt)",
                    );
                    Ok(ZipDo::Trm { nu_term, frame })
                }
            },
        );

        res.is_err()
    }

    /// Returns true if the term mentions a function or an ADT.
    pub fn has_fun_app_or_adt(&self) -> bool {
        use self::zip::*;

        // Will be `Ok(())` if there's no function application, and `Err(())`
        // otherwise.
        let res = zip(
            &self.to_hcons(),
            |term| {
                if term.fun_inspect().is_some()
                    || term.dtyp_new_inspect().is_some()
                    || term.dtyp_slc_inspect().is_some()
                {
                    Err(())
                } else {
                    Ok(None)
                }
            },
            |_| Ok(()),
            |zip_op, _, _: ()| match zip_op {
                ZipOp::Fun(_) | ZipOp::New(_) | ZipOp::Slc(_) => Err(()),
                _ => Ok(ZipDoTotal::Upp { yielded: () }),
            },
            |frame| match frame {
                ZipFrame {
                    thing: ZipOp::Fun(_),
                    ..
                }
                | ZipFrame {
                    thing: ZipOp::New(_),
                    ..
                }
                | ZipFrame {
                    thing: ZipOp::Slc(_),
                    ..
                } => Err(()),
                mut frame => {
                    let nu_term = frame.rgt_args.next().expect(
                        "illegal call to `partial_op`:
            empty `rgt_args` (has_fun_app_or_adt)",
                    );
                    Ok(ZipDo::Trm { nu_term, frame })
                }
            },
        );

        res.is_err()
    }

    /// The kids of this term, if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let kids = vec![term::int_var(0), term::int(2)];
    /// let t = term::add( kids.clone() );
    /// # println!("{}", t);
    /// assert_eq! { t.kids(), Some(&kids as &[Term]) }
    /// ```
    pub fn kids(&self) -> Option<&[Term]> {
        if let RTerm::App { ref args, .. } = *self {
            Some(args)
        } else {
            None
        }
    }

    /// Checks whether a term is an equality.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::add( vec![term::int_var(0), term::int(2)] );
    /// # println!("{}", t);
    /// assert! { ! t.is_eq() }
    /// let t = term::eq( t, term::int(42) );
    /// # println!("{}", t);
    /// assert! { t.is_eq() }
    /// ```
    pub fn is_eq(&self) -> bool {
        match *self {
            RTerm::App { op: Op::Eql, .. } => true,
            _ => false,
        }
    }
}

/// Term modifiers.
impl RTerm {
    /// Turns a real term in a hashconsed one.
    #[inline]
    pub fn to_hcons(&self) -> Term {
        term(self.clone())
    }

    /// Forces the type of a datatype constructor.
    pub fn force_dtyp(&self, nu_typ: Typ) -> Option<Term> {
        match self {
            RTerm::DTypNew {
                typ, name, args, ..
            } => {
                debug_assert! { nu_typ.is_compatible(typ) }
                Some(dtyp_new(nu_typ, name.clone(), args.clone()))
            }
            RTerm::Cst(val) => val.force_dtyp(nu_typ).map(cst),
            _ => None,
        }
    }

    /// Casts a term.
    ///
    /// Only legal if the term's type and the one provided are compatible.
    ///
    /// Returns
    ///
    /// - an error if the types are not compatible
    /// - `None` if the cast didn't do anything
    /// - the new term otherwise
    pub fn cast(&self, to_typ: &Typ) -> Res<Option<Term>> {
        let nu_typ = if let Some(typ) = self.typ().merge(to_typ) {
            if to_typ == &typ {
                return Ok(None);
            }
            typ
        } else {
            bail!("types {} and {} are incompatible", self.typ(), to_typ)
        };

        enum Frame<'a> {
            // Array frame.
            Arr(Typ),
            // Datatype constructor.
            New {
                typ: Typ,
                name: String,
                lft: Vec<Term>,
                rgt: ::std::vec::IntoIter<(Typ, &'a RTerm)>,
            },
        }

        let mut stack = vec![];
        let (mut nu_typ, mut curr) = (nu_typ, self);

        'go_down: loop {
            let mut term = match curr {
                RTerm::Var(_, idx) => term::var(*idx, nu_typ),

                RTerm::Cst(val) => {
                    if let Ok(val) = val.cast(&nu_typ) {
                        factory::cst(val)
                    } else {
                        return Ok(None);
                    }
                }

                RTerm::App { op, args, .. } => term::app(*op, args.clone()),

                RTerm::CArray { typ, term, .. } => {
                    let (src, tgt) = typ.array_inspect().unwrap();
                    stack.push(Frame::Arr(src.clone()));
                    nu_typ = tgt.clone();
                    curr = term.get();
                    continue 'go_down;
                }

                RTerm::DTypNew {
                    typ, name, args, ..
                } => {
                    let mut lft = vec![];
                    let mut next = None;
                    let mut rgt = vec![];

                    scoped! {

                      let (_, nu_prms) = nu_typ.dtyp_inspect().unwrap() ;
                      let (_, prms) = typ.dtyp_inspect().unwrap() ;
                      debug_assert_eq! { args.len(), nu_prms.len() }
                      debug_assert_eq! { args.len(), prms.len() }
                      let mut all = nu_prms.iter().zip(
                        prms.iter()
                      ).zip( args.iter() ) ;

                      while let Some(((nu, typ), arg)) = all.next()  {
                        if nu == typ {
                          lft.push( arg.clone() )
                        } else {
                          next = Some(
                            ( arg.get(), nu.clone() )
                          )
                        }
                      }

                      for ((nu_typ, _), arg) in all {
                        rgt.push( (nu_typ.clone(), arg.get()) )
                      }

                    }

                    if let Some((term, nu)) = next {
                        let frame = Frame::New {
                            typ: nu_typ,
                            name: name.clone(),
                            lft,
                            rgt: rgt.into_iter(),
                        };
                        stack.push(frame);
                        nu_typ = nu;
                        curr = term;

                        continue 'go_down;
                    } else {
                        term::dtyp_new(nu_typ, name.clone(), lft)
                    }
                }

                RTerm::DTypSlc {
                    typ, name, term, ..
                } => {
                    debug_assert_eq! { typ, & nu_typ }
                    term::dtyp_slc(typ.clone(), name.clone(), term.clone())
                }

                RTerm::DTypTst {
                    name, term, typ, ..
                } => {
                    debug_assert_eq! { typ, & nu_typ }
                    term::dtyp_tst(name.clone(), term.clone())
                }

                RTerm::Fun {
                    typ, name, args, ..
                } => {
                    debug_assert_eq! { typ, & nu_typ }
                    term::fun(name.clone(), args.clone())
                }
            };

            'go_up: loop {
                match stack.pop() {
                    None => return Ok(Some(term)),

                    Some(Frame::Arr(typ)) => {
                        term = term::cst_array(typ, term);
                        continue 'go_up;
                    }

                    Some(Frame::New {
                        typ,
                        name,
                        mut lft,
                        mut rgt,
                    }) => {
                        lft.push(term);

                        if let Some((ty, tm)) = rgt.next() {
                            nu_typ = ty;
                            curr = tm;
                            stack.push(Frame::New {
                                typ,
                                name,
                                lft,
                                rgt,
                            });
                            continue 'go_down;
                        } else {
                            term = term::dtyp_new(typ, name, lft);
                            continue 'go_up;
                        }
                    }
                }
            }
        }
    }

    /// If the term is a negation, returns what's below the negation.
    pub fn rm_neg(&self) -> Option<Term> {
        match *self {
            RTerm::App {
                op: Op::Not,
                ref args,
                ..
            } => {
                debug_assert_eq!(args.len(), 1);
                Some(args[0].clone())
            }
            _ => None,
        }
    }
}

/// Variant deconstructors.
impl RTerm {
    /// The operator and the kids of a term.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::modulo( term::int_var(0), term::int(7) );
    ///
    /// let (op, args) = t.app_inspect().unwrap();
    /// assert_eq! { op, Op::Mod }
    /// assert_eq! { args, &vec![ term::int_var(0), term::int(7) ] }
    /// ```
    pub fn app_inspect(&self) -> Option<(Op, &Vec<Term>)> {
        if let RTerm::App { op, ref args, .. } = *self {
            Some((op, args))
        } else {
            None
        }
    }

    /// Returns the kids of an ite.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::ite( term::bool_var(3), term::int_var(0), term::int(7) );
    ///
    /// let (cnd, thn, els) = t.ite_inspect().unwrap();
    /// assert_eq! { cnd, &term::bool_var(3) }
    /// assert_eq! { thn, &term::int_var(0) }
    /// assert_eq! { els, &term::int(7) }
    /// ```
    pub fn ite_inspect(&self) -> Option<(&Term, &Term, &Term)> {
        if let RTerm::App {
            op: Op::Ite,
            ref args,
            ..
        } = *self
        {
            debug_assert_eq! { args.len(), 3 }
            Some((&args[0], &args[1], &args[2]))
        } else {
            None
        }
    }

    /// Inspects a function application.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use hoice::{ term, term::typ, dtyp, fun };
    /// fun::test::create_length_fun();
    /// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
    ///
    /// let t = term::fun( fun::test::length_fun_name(), vec![ term::var(0, list.clone()) ] );
    ///
    /// let (name, args) = t.fun_inspect().unwrap();
    /// assert_eq! { name, fun::test::length_fun_name() }
    /// assert_eq! { args, & vec![ term::var(0, list) ] }
    /// ```
    pub fn fun_inspect(&self) -> Option<(&String, &Vec<Term>)> {
        if let RTerm::Fun {
            ref name, ref args, ..
        } = *self
        {
            Some((name, args))
        } else {
            None
        }
    }

    /// Returns the kid of a negation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::not(term::bool_var(3));
    ///
    /// let kid = t.neg_inspect().unwrap();
    /// assert_eq! { kid, &term::bool_var(3) }
    /// ```
    pub fn neg_inspect(&self) -> Option<&Term> {
        if let RTerm::App {
            op: Op::Not,
            ref args,
            ..
        } = *self
        {
            debug_assert_eq! { args.len(), 1 }
            Some(&args[0])
        } else {
            None
        }
    }

    /// Returns the kids of conjunctions.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let not_v_3 = term::not(term::bool_var(3));
    /// let ge = term::ge( term::int_var(0), term::int(17) );
    /// let t = term::and(vec![ not_v_3.clone(), ge.clone() ]);
    ///
    /// let kids = t.conj_inspect().unwrap();
    /// assert_eq! { kids, &vec![not_v_3, ge] }
    /// ```
    pub fn conj_inspect(&self) -> Option<&Vec<Term>> {
        if let RTerm::App {
            op: Op::And,
            ref args,
            ..
        } = *self
        {
            Some(args)
        } else {
            None
        }
    }

    /// Returns the kids of disjunctions.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let not_v_3 = term::not(term::bool_var(3));
    /// let ge = term::ge( term::int_var(0), term::int(17) );
    /// let t = term::or(vec![ not_v_3.clone(), ge.clone() ]);
    ///
    /// let kids = t.disj_inspect().unwrap();
    /// assert_eq! { kids, &vec![not_v_3, ge] }
    /// ```
    pub fn disj_inspect(&self) -> Option<&Vec<Term>> {
        if let RTerm::App {
            op: Op::Or,
            ref args,
            ..
        } = *self
        {
            Some(args)
        } else {
            None
        }
    }

    /// Returns the kids of equalities.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::eq( term::int_var(0), term::int(0) );
    ///
    /// let kids = t.eq_inspect().unwrap();
    /// assert_eq! { kids, &vec![ term::int_var(0), term::int(0) ] }
    ///
    /// // Kids will change in general. For instance:
    /// let t = term::eq( term::int_var(0), term::int(17) );
    ///
    /// let kids = t.eq_inspect().unwrap();
    /// assert_ne! { kids, &vec![ term::int_var(0), term::int(17) ] }
    /// assert_eq! {
    ///     kids, &vec![
    ///         term::add(vec![term::int_var(0), term::u_minus(term::int(17))]),
    ///         term::int(0)
    ///     ]
    /// }
    /// ```
    pub fn eq_inspect(&self) -> Option<&Vec<Term>> {
        if let RTerm::App {
            op: Op::Eql,
            ref args,
            ..
        } = *self
        {
            Some(args)
        } else {
            None
        }
    }

    /// Returns the kids of additions.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::add( vec![term::int_var(0), term::int(17)] );
    ///
    /// let kids = t.add_inspect().unwrap();
    /// assert_eq! { kids, &vec![ term::int_var(0), term::int(17) ] }
    ///
    /// // Be careful that the order might change.
    /// let t = term::add( vec![term::int_var(3), term::int_var(0)] );
    ///
    /// let kids = t.add_inspect().unwrap();
    /// assert_ne! { kids, &vec![ term::int_var(3), term::int_var(0) ] }
    /// assert_eq! { kids, &vec![ term::int_var(0), term::int_var(3) ] }
    /// ```
    pub fn add_inspect(&self) -> Option<&Vec<Term>> {
        if let RTerm::App {
            op: Op::Add,
            ref args,
            ..
        } = *self
        {
            Some(args)
        } else {
            None
        }
    }

    /// Returns the kids of subtractions.
    ///
    /// Unused currently, subtraction are rewritten as addition with unary minuses.
    #[allow(dead_code)]
    fn sub_inspect(&self) -> Option<&Vec<Term>> {
        if let RTerm::App {
            op: Op::Sub,
            ref args,
            ..
        } = *self
        {
            Some(args)
        } else {
            None
        }
    }

    /// Returns the kids of multiplications.
    ///
    /// Deconstructs *only* multiplications in the sense of [`Op::Mul`], *not to be confused* with
    /// [`Op::CMul`].
    ///
    /// [`Op::Mul`]: enum.Op.html#variant.Mul
    /// [`Op::CMul`]: enum.Op.html#variant.CMul
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::mul( vec![term::int_var(0), term::int_var(2)] );
    ///
    /// let kids = t.mul_inspect().unwrap();
    /// assert_eq! { kids, &vec![ term::int_var(0), term::int_var(2) ] }
    ///
    /// // Careful of `Op::CMul`.
    /// let t = term::mul( vec![term::int(3), term::int_var(0)] );
    ///
    /// assert! { t.mul_inspect().is_none() }
    /// assert! { t.cmul_inspect().is_some() }
    /// ```
    pub fn mul_inspect(&self) -> Option<&Vec<Term>> {
        if let RTerm::App {
            op: Op::Mul,
            ref args,
            ..
        } = *self
        {
            Some(args)
        } else {
            None
        }
    }

    /// Returns the kids of a constant multiplication.
    ///
    /// Deconstructs *only* multiplications in the sense of [`Op::CMul`], *not to be confused* with
    /// [`Op::Mul`].
    ///
    /// [`Op::Mul`]: enum.Op.html#variant.Mul
    /// [`Op::CMul`]: enum.Op.html#variant.CMul
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::mul( vec![term::int(3), term::int_var(0)] );
    ///
    /// let (val, kid) = t.cmul_inspect().unwrap();
    /// assert_eq! { val, val::int(3) }
    /// assert_eq! { kid, &term::int_var(0) }
    ///
    /// let t = term::cmul( 7, t.clone() );
    ///
    /// let (val, kid) = t.cmul_inspect().unwrap();
    /// assert_eq! { val, val::int(7 * 3) }
    /// assert_eq! { kid, &term::int_var(0) }
    /// ```
    pub fn cmul_inspect(&self) -> Option<(Val, &Term)> {
        if let RTerm::App {
            op: Op::CMul,
            ref args,
            ..
        } = *self
        {
            if args.len() == 2 {
                if let Some(val) = args[0].val() {
                    return Some((val, &args[1]));
                }
            }
            panic!("illegal c_mul application: {}", self)
        } else {
            None
        }
    }

    /// Returns the kids of a datatype tester.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
    /// let t = term::dtyp_tst("insert", term::var(0, list.clone()));
    ///
    /// # println!("{}", t);
    /// let (constructor, term) = t.dtyp_tst_inspect().unwrap();
    /// assert_eq! { constructor, "insert" }
    /// assert_eq! { term, &term::var(0, list.clone()) }
    ///
    /// // Careful of unary tester rewriting.
    /// let t = term::dtyp_tst("nil", term::var(0, list.clone()));
    /// # println!("{}", t);
    /// assert! { t.dtyp_tst_inspect().is_none() }
    ///
    /// let negated = t.neg_inspect().unwrap();
    /// let (constructor, term) = negated.dtyp_tst_inspect().unwrap();
    /// assert_eq! { constructor, "insert" }
    /// assert_eq! { term, &term::var(0, list) }
    /// ```
    pub fn dtyp_tst_inspect(&self) -> Option<(&str, &Term)> {
        if let RTerm::DTypTst { name, term, .. } = self {
            Some((name, term))
        } else {
            None
        }
    }

    /// Returns the kids of a datatype constructor.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
    /// let nil = term::dtyp_new(list.clone(), "nil", vec![]);
    /// let only_v_0 = term::dtyp_new(
    ///     list.clone(), "insert", vec![ term::int_var(0), nil.clone()]
    /// );
    ///
    /// # println!("{}", only_v_0);
    /// let (typ, constructor, kids) = only_v_0.dtyp_new_inspect().unwrap();
    /// assert_eq! { typ, & list }
    /// assert_eq! { constructor, "insert" }
    /// assert_eq! { kids, &[term::int_var(0), nil] }
    /// ```
    pub fn dtyp_new_inspect(&self) -> Option<(&Typ, &str, &[Term])> {
        if let RTerm::DTypNew {
            typ, name, args, ..
        } = self
        {
            Some((typ, name, args))
        } else {
            None
        }
    }

    /// Returns the kids of a datatype selector.
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let list = typ::dtyp(dtyp::get("List").unwrap(), vec![typ::int()].into());
    /// let only_v_0 = term::dtyp_slc(list.clone(), "tail", term::int_var(0));
    ///
    /// # println!("{}", only_v_0);
    /// let (typ, constructor, kids) = only_v_0.dtyp_slc_inspect().unwrap();
    /// assert_eq! { typ, & list }
    /// assert_eq! { constructor, "tail" }
    /// assert_eq! { kids, &term::int_var(0) }
    /// ```
    pub fn dtyp_slc_inspect(&self) -> Option<(&Typ, &str, &Term)> {
        if let RTerm::DTypSlc {
            typ, name, term, ..
        } = self
        {
            Some((typ, name, term))
        } else {
            None
        }
    }
}

/// Variable substitution.
///
/// All substitution functions take a mapping from variables to terms in the form of a
/// [`VarIndexed`].
///
/// The central variable substitution function is [`subst_custom`]. It applies a substitution and
/// takes a flag indicating whether the substitution should be considered total or not. The
/// difference is crucial: when applying a substitution to a term coming from the body of a clause
/// to form a term for a predicate definition, the substitution should **always** be total.
/// Otherwise clauses variables will end up in the predicate's definition which makes no sense and
/// is dangerous. Conversely, substitution from  a predicate term to a clause term should always be
/// total.
///
/// As such, makes sure that you use [`subst_total`] whenever you're doing clause-to-predicate or
/// predicate-to-clause conversions. Otherwise, [`subst`] performs partial variable substitution,
/// which can never fail. Last, [`subst_fp`] iterates until the fixed-point of a substitution.
///
/// [`VarIndexed`]: ../common/trait.VarIndexed.html (VarIndexed trait)
/// [`subst_custom`]: enum.RTerm.html#method.subst_custom (subst_custom function for RTerm)
/// [`subst_total`]: enum.RTerm.html#method.subst_total (subst_total function for RTerm)
/// [`subst_fp`]: enum.RTerm.html#method.subst_fp (subst_fp function for RTerm)
/// [`subst`]: enum.RTerm.html#method.subst (subst function for RTerm)
impl RTerm {
    /// Variable substitution.
    ///
    /// The `total` flag causes substitution to fail if a variable that's not in `map`. The boolean
    /// returned is true if at least one substitution occurred. The map itself is given as a
    /// [`VarIndexed`].
    ///
    /// [`VarIndexed`]: ../common/trait.VarIndexed.html (VarIndexed trait)
    ///
    /// # Examples
    ///
    /// Total substitution.
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let three_v_0 = term::cmul( 3, term::int_var(0) );
    /// let t = term::ge(
    ///     term::add(vec![ three_v_0.clone(), term::int_var(2) ]),
    ///     term::mul(vec![ term::int(3), term::int_var(1) ])
    /// );
    /// # println!("{}", t);
    /// let map: VarMap<_> = vec![
    ///     // v_0 ->
    ///     term::add( vec![term::int_var(7), term::int(2)] ),
    ///     // v_1 ->
    ///     term::int_var(8),
    ///     // v_2 ->
    ///     term::int_var(9),
    /// ].into_iter().collect();
    ///
    /// // Asking for total substitution ~~~~~~~~~~~~~~vvvv
    /// let (res, at_least_one) = t.subst_custom(&map, true).unwrap();
    /// assert! { at_least_one }
    /// assert_eq! {
    ///     &format!("{}", res), "(>= (+ v_9 (* 3 v_7) (* (- 3) v_8)) (- 6))"
    /// }
    /// ```
    ///
    /// Partial substitution.
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let three_v_0 = term::cmul( 3, term::int_var(0) );
    /// let t = term::ge(
    ///     term::add(vec![ three_v_0.clone(), term::int_var(2) ]),
    ///     term::mul(vec![ term::int(3), term::int_var(1) ])
    /// );
    /// # println!("{}", t);
    /// // Map does not mention `v_2`.
    /// let map: VarMap<_> = vec![
    ///     // v_0 ->
    ///     term::add( vec![term::int_var(7), term::int(2)] ),
    ///     // v_1 ->
    ///     term::int_var(8),
    /// ].into_iter().collect();
    ///
    /// // Asking for total substitution ~~~vvvv
    /// let res =      t.subst_custom(&map, true);
    /// // Total substitution failed.
    /// assert! { res.is_none() }
    ///
    /// // Asking for partial substitution ~vvvvv
    /// let res =      t.subst_custom(&map, false);
    /// // Success.
    /// let (res, at_least_one) = res.unwrap();
    /// assert! { at_least_one }
    /// assert_eq! {
    ///     &format!("{}", res), "(>= (+ v_2 (* 3 v_7) (* (- 3) v_8)) (- 6))"
    /// } // `v_2` is still here ~~~~~~~~^^^
    /// ```
    pub fn subst_custom<Map: VarIndexed<Term>>(
        &self,
        map: &Map,
        total: bool,
    ) -> Option<(Term, bool)> {
        use self::zip::*;
        let mut changed = false;

        let res = zip(
            &self.to_hcons(),
            |_| Ok(None),
            |zip_null| match zip_null {
                ZipNullary::Cst(val) => Ok(cst(val.clone())),
                ZipNullary::Var(typ, var) => {
                    if let Some(term) = map.var_get(var) {
                        debug_assert_eq! { typ, & term.typ() }
                        changed = true;
                        Ok(term)
                    } else if total {
                        Err(())
                    } else {
                        Ok(term::var(var, typ.clone()))
                    }
                }
            },
            |zip_op, typ, mut acc| {
                let yielded = match zip_op {
                    ZipOp::Op(op) => term::app(op, acc),
                    ZipOp::New(name) => term::dtyp_new(typ.clone(), name.clone(), acc),

                    ZipOp::Slc(name) => {
                        if let Some(kid) = acc.pop() {
                            if !acc.is_empty() {
                                panic!(
                                    "illegal application of datatype selector {} to {} arguments",
                                    conf.bad(name),
                                    acc.len() + 1
                                )
                            }
                            term::dtyp_slc(typ.clone(), name.clone(), kid)
                        } else {
                            panic!(
                                "illegal application of datatype selector {} to 0 arguments",
                                conf.bad(name)
                            )
                        }
                    }

                    ZipOp::Tst(name) => {
                        if let Some(kid) = acc.pop() {
                            if !acc.is_empty() {
                                panic!(
                                    "illegal application of datatype tester {} to {} arguments",
                                    conf.bad(name),
                                    acc.len() + 1
                                )
                            }
                            term::dtyp_tst(name.clone(), kid)
                        } else {
                            panic!(
                                "illegal application of datatype tester {} to 0 arguments",
                                conf.bad(name)
                            )
                        }
                    }

                    ZipOp::CArray => {
                        if let Some(kid) = acc.pop() {
                            if !acc.is_empty() {
                                panic!(
                                    "illegal constant array application to {} arguments",
                                    acc.len() + 1
                                )
                            }
                            term::cst_array(typ.clone(), kid)
                        } else {
                            panic!("illegal constant array application to 0 arguments")
                        }
                    }
                    ZipOp::Fun(name) => term::fun(name.clone(), acc),
                };

                Ok(ZipDoTotal::Upp { yielded })
            },
            |mut frame| {
                let nu_term = frame
                    .rgt_args
                    .next()
                    .expect("illegal call to `partial_op`: empty `rgt_args` (subst_custom)");
                Ok(ZipDo::Trm { nu_term, frame })
            },
        );

        if let Ok(term) = res {
            Some((term, changed))
        } else {
            None
        }
    }

    /// Variable substitution.
    ///
    /// Returns the new term and a boolean indicating whether any substitution occurred. Used for
    /// substitutions in the same clause / predicate scope.
    ///
    /// Equivalent to `self.subst_custom(map, false).unwrap()`. For examples see [`subst_custom`].
    ///
    /// [`subst_custom`]: #method.subst_custom (subst_custom function for RTerm)
    #[inline]
    pub fn subst<Map: VarIndexed<Term>>(&self, map: &Map) -> (Term, bool) {
        self.subst_custom(map, false)
            .expect("partial substitution can't fail")
    }

    /// Fixed-point (partial) variable substitution.
    ///
    /// Applies `term = term.subst(map)`, starting with `self`, until the substitution does not
    /// change the term anymore. Returns the new term and a boolean indicating whether any
    /// substitution occurred.
    ///
    /// This function will loop forever if no fixed-point exists (the map is circular).
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let three_v_0 = term::cmul( 3, term::int_var(0) );
    /// let t = term::ge(
    ///     term::add(vec![ three_v_0.clone(), term::int_var(2) ]),
    ///     term::mul(vec![ term::int(3), term::int_var(1) ])
    /// );
    /// # println!("{}", t);
    /// let map: VarMap<_> = vec![
    ///     // v_0 ->             vvvvvvvvvv~~~ v_0 maps to a term mentioning v_1
    ///     term::add( vec![term::int_var(1), term::int(2)] ),
    ///     // v_1 ->
    ///     term::int_var(8),
    ///     // v_2 ->
    ///     term::int_var(1), // v_2 maps to v_1
    /// ].into_iter().collect();
    ///
    /// let (res, at_least_one) = t.subst_fp(&map);
    /// assert! { at_least_one }
    /// assert_eq! {
    ///     &format!("{}", res), "(>= v_8 (- 6))"
    /// }
    /// ```
    ///
    /// [`subst`]: #method.subst (subst function for RTerm)
    pub fn subst_fp<Map: VarIndexed<Term>>(&self, map: &Map) -> (Term, bool) {
        let (mut term, changed) = self.subst(map);
        let mut fp = !changed;
        while !fp {
            let (new_term, changed) = term.subst(map);
            term = new_term;
            fp = !changed
        }
        (term, changed)
    }

    /// Total variable substitution.
    ///
    /// Returns the new term and a boolean indicating whether any substitution occurred. Used for
    /// substitutions between different same clause / predicate scopes.
    ///
    /// Equivalent to `self.subst_custom(map, true)`. For examples see [`subst_custom`].
    ///
    /// [`subst_custom`]: #method.subst_custom (subst_custom function for RTerm)
    pub fn subst_total<Map: VarIndexed<Term>>(&self, map: &Map) -> Option<(Term, bool)> {
        self.subst_custom(map, true)
    }
}

/// Fold/map/zip functions.
impl RTerm {
    /// Iterator over over all the leafs of a term.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let sum = term::add(vec![
    ///     term::int_var(0),
    ///     term::cmul(2, term::int_var(1))
    /// ]);
    /// let t = term::ge(sum, term::int(0));
    /// # println!("{}", t);
    ///
    /// let int = typ::int();
    /// let (zero, two) = (val::int(0), val::int(2));
    /// let mut leaves: Vec<Either<(&Typ, VarIdx), &Val>> = vec![
    ///     Either::Left((&int, 0.into())), // v_0: Int |
    ///     Either::Right(& two),           // 2        |- LHS of the `<=`
    ///     Either::Left((&int, 1.into())), // v_1: Int |
    ///     Either::Right(& zero),          // 0, RHS of the `<=`
    /// ];
    /// leaves.reverse(); // <- We're going to pop below, hence the reversal.
    /// for leaf in t.leaf_iter() {
    ///     assert_eq! { Some(leaf), leaves.pop() }
    /// }
    /// ```
    pub fn leaf_iter(&self) -> LeafIter {
        LeafIter::of_rterm(self)
    }

    /// Iterates over all the subterms of a term, including itself.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let v_0 = term::int_var(0);
    /// let v_1 = term::int_var(1);
    /// let two = term::int(2);
    /// let two_v_1 = term::mul(vec![ two.clone(), v_1.clone() ]);
    /// let sum = term::add(vec![ v_0.clone(), two_v_1.clone() ]);
    /// let zero = term::int(0);
    /// let t = term::ge(sum.clone(), zero.clone());
    /// # println!("{}", t);
    /// let mut all: TermSet = vec![
    ///     v_0, v_1, two, two_v_1, sum, zero, t.clone()
    /// ].into_iter().collect();
    ///
    /// t.iter(
    ///     |term| {
    ///         let term = term.to_hcons();
    ///         let was_there = all.remove(&term);
    ///         assert! { was_there }
    ///     }
    /// );
    /// assert! { all.is_empty() }
    /// ```
    pub fn iter<F>(&self, mut f: F)
    where
        F: FnMut(&RTerm),
    {
        use self::RTerm::*;
        let mut stack = vec![self];

        while let Some(term) = stack.pop() {
            f(term);
            match term {
                App { args, .. } | DTypNew { args, .. } | Fun { args, .. } => {
                    stack.extend(args.iter().map(|term| term.get()))
                }

                CArray { term, .. } | DTypSlc { term, .. } | DTypTst { term, .. } => {
                    stack.push(term.get())
                }

                Var(_, _) | Cst(_) => (),
            }
        }
    }

    /// Boolean a constant boolean term evaluates to.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::ge( term::int_var(0), term::int_var(0) );
    /// # println!("{}", t);
    /// assert_eq! { t.bool(), Some(true) }
    /// let t = term::not(t);
    /// # println!("{}", t);
    /// assert_eq! { t.bool(), Some(false) }
    /// let t = term::ge( term::int_var(0), term::int(2) );
    /// # println!("{}", t);
    /// assert_eq! { t.bool(), None }
    /// ```
    pub fn bool(&self) -> Option<bool> {
        match self.bool_eval(&()) {
            Ok(Some(b)) => Some(b),
            _ => None,
        }
    }

    /// Integer value the term evaluates to.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::add( vec![term::int_var(0), term::int(2)] );
    /// # println!("{}", t);
    /// assert_eq! { t.int(), None }
    /// let t = term::add( vec![term::int(5), term::int(2)] );
    /// # println!("{}", t);
    /// assert_eq! { t.int(), Some(7.into()) }
    /// ```
    pub fn int(&self) -> Option<Int> {
        if self.typ() != typ::int() {
            return None;
        }
        match self.int_eval(&()) {
            Ok(Some(i)) => Some(i),
            _ => None,
        }
    }

    /// Real value the term evaluates to.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::add( vec![term::real_var(0), term::real_of(2.)] );
    /// # println!("{}", t);
    /// assert_eq! { t.real(), None }
    /// let t = term::add( vec![term::real_of(5.), term::real_of(2.)] );
    /// # println!("{}", t);
    /// assert_eq! { t.real(), Some(rat_of_float(7.).into()) }
    /// ```
    pub fn real(&self) -> Option<Rat> {
        match self.real_eval(&()) {
            Ok(Some(r)) => Some(r),
            _ => None,
        }
    }

    /// Evaluates a term with an empty model.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::add( vec![term::int_var(0), term::int(2)] );
    /// # println!("{}", t);
    /// assert_eq! { t.as_val(), val::none(typ::int()) }
    /// let t = term::add( vec![term::int(5), term::int(2)] );
    /// # println!("{}", t);
    /// assert_eq! { t.as_val(), val::int(7) }
    /// ```
    pub fn as_val(&self) -> Val {
        if let Ok(res) = self.eval(&()) {
            res
        } else {
            val::none(self.typ().clone())
        }
    }

    /// Turns a constant term in a `Val`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::add( vec![term::int_var(0), term::int(2)] );
    /// # println!("{}", t);
    /// assert_eq! { t.val(), None }
    /// let t = term::add( vec![term::int(5), term::int(2)] );
    /// # println!("{}", t);
    /// assert_eq! { t.val(), Some(val::int(7)) }
    /// ```
    pub fn val(&self) -> Option<Val> {
        match *self {
            RTerm::Cst(ref val) => Some(val.clone()),
            _ => None,
        }
    }

    /// The highest variable index appearing in the term.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::ge(
    ///     term::add( vec![term::real_var(0), term::real_var(2), term::real_of(17.)] ),
    ///     term::real_var(666)
    /// );
    /// # println!("{}", t);
    /// assert_eq! { t.highest_var(), Some(666.into()) }
    /// ```
    pub fn highest_var(&self) -> Option<VarIdx> {
        let mut max = None;

        for var_or_cst in self.leaf_iter() {
            if let Either::Left((_, var_idx)) = var_or_cst {
                max = Some(::std::cmp::max(var_idx, max.unwrap_or_else(|| 0.into())))
            }
        }

        max
    }

    /// TOP-DOWN term substitution.
    ///
    /// Applies the term map provided to all matching terms while going down in the term. When it
    /// replaces a subterm with `trm` from `map`, this function will not go down `trm`.
    ///
    /// This is used by let-[`bindings`] in clauses for concise printing.
    ///
    /// This function is equivalent to [`self.top_down_map(|t| map.get(t).cloned())`].
    ///
    /// [`bindings`]: bindings/index.html (bindings module)
    /// [`self.top_down_map(|t| map.get(t).cloned())`]: #method.top_down_map
    /// (top_down_map function over RTerm)
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let three_v_0 = term::cmul( 3, term::int_var(0) );
    /// let t = term::ge(
    ///     term::add(vec![ three_v_0.clone(), term::int_var(2) ]),
    ///     term::int(3)
    /// );
    /// # println!("{}", t);
    /// let map: TermMap<Term> = vec![
    ///     (        three_v_0, term::int_var(7)  ),
    ///     // This mapping won't be used, as the mapping above will trigger first.
    ///     ( term::int_var(0), term::int_var(8)  ),
    ///     // Likewise, this mapping will only trigger in the LHS of the `>=`, not in the
    ///     // multiplication since the first binding will replace it.
    ///     (     term::int(3), term::int_var(9)  ),
    ///     // This last one will not be used at all since the function does not go down new terms.
    ///     ( term::int_var(7), term::int_var(42) ),
    /// ].into_iter().collect();
    ///
    /// assert_eq! { &format!("{}", t.term_subst(&map)), "(>= (+ v_2 v_7 (* (- 1) v_9)) 0)" }
    /// ```
    pub fn term_subst(&self, map: &TermMap<Term>) -> Term {
        self.top_down_map(|term| map.get(term).cloned())
    }

    /// TOP-DOWN map over terms.
    ///
    /// Applies the term map provided (as a function) to all matching terms while going down in the
    /// term. When it replaces a subterm with `trm` from `map`, this function will not go down
    /// `trm`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let three_v_0 = term::cmul( 3, term::int_var(0) );
    /// let t = term::ge(
    ///     term::add(vec![ three_v_0.clone(), term::int_var(2) ]),
    ///     term::int(3)
    /// );
    /// # println!("{}", t);
    /// let map: TermMap<Term> = vec![
    ///     (        three_v_0, term::int_var(7)  ),
    ///     // This mapping won't be used, as the mapping above will trigger first.
    ///     ( term::int_var(0), term::int_var(8)  ),
    ///     // Likewise, this mapping will only trigger in the LHS of the `>=`, not in the
    ///     // multiplication since the first binding will replace it.
    ///     (     term::int(3), term::int_var(9)  ),
    ///     // This last one will not be used at all since the function does not go down new terms.
    ///     ( term::int_var(7), term::int_var(42) ),
    /// ].into_iter().collect();
    ///
    /// assert_eq! {
    ///     &format!("{}", t.top_down_map(|t| map.get(t).cloned())),
    ///     "(>= (+ v_2 v_7 (* (- 1) v_9)) 0)"
    /// }
    /// ```
    pub fn top_down_map<Fun>(&self, mut f: Fun) -> Term
    where
        Fun: for<'a> FnMut(&'a Term) -> Option<Term>,
    {
        use self::zip::*;
        let res: Res<Term> = zip(
            &self.to_hcons(),
            |term| Ok(f(term)),
            |zip_null| match zip_null {
                ZipNullary::Cst(val) => Ok(cst(val.clone())),
                ZipNullary::Var(typ, var) => Ok(term::var(var, typ.clone())),
            },
            |zip_op, typ, mut acc| {
                let yielded = match zip_op {
                    ZipOp::Op(op) => term::app(op, acc),
                    ZipOp::New(name) => term::dtyp_new(typ.clone(), name.clone(), acc),

                    ZipOp::Slc(name) => {
                        if let Some(kid) = acc.pop() {
                            if !acc.is_empty() {
                                panic!(
                                    "illegal application of datatype selector {} to {} arguments",
                                    conf.bad(name),
                                    acc.len() + 1
                                )
                            }
                            term::dtyp_slc(typ.clone(), name.clone(), kid)
                        } else {
                            panic!(
                                "illegal application of datatype selector {} to 0 arguments",
                                conf.bad(name)
                            )
                        }
                    }

                    ZipOp::Tst(name) => {
                        if let Some(kid) = acc.pop() {
                            if !acc.is_empty() {
                                panic!(
                                    "illegal application of datatype tester {} to {} arguments",
                                    conf.bad(name),
                                    acc.len() + 1
                                )
                            }
                            term::dtyp_tst(name.clone(), kid)
                        } else {
                            panic!(
                                "illegal application of datatype tester {} to 0 arguments",
                                conf.bad(name)
                            )
                        }
                    }

                    ZipOp::CArray => {
                        if let Some(kid) = acc.pop() {
                            if !acc.is_empty() {
                                panic!(
                                    "illegal constant array application to {} arguments",
                                    acc.len() + 1
                                )
                            }
                            term::cst_array(typ.clone(), kid)
                        } else {
                            panic!("illegal constant array application to 0 arguments")
                        }
                    }
                    ZipOp::Fun(name) => term::fun(name.clone(), acc),
                };

                Ok(ZipDoTotal::Upp { yielded })
            },
            |mut frame| {
                let nu_term = frame.rgt_args.next().expect(
                    "illegal call to `partial_op`: \
                     empty `rgt_args` (has_fun_app_or_adt)",
                );
                Ok(ZipDo::Trm { nu_term, frame })
            },
        );

        res.expect("top down map can never fail")
    }

    /// Tries to turn a term into a substitution.
    ///
    /// Works only on equalities.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::term ;
    /// let bv0 = term::bool_var(0) ;
    /// let bv1 = term::bool_var(1) ;
    /// let bv2 = term::bool_var(2) ;
    /// let rhs = term::or(vec![bv1, bv2]) ;
    /// let term = term::eq(bv0, rhs.clone()) ;
    /// assert_eq! { term.as_subst(), Some((0.into(), rhs)) }
    /// ```
    pub fn as_subst(&self) -> Option<(VarIdx, Term)> {
        if let Some(kids) = self.eq_inspect() {
            debug_assert_eq! { kids.len(), 2 }
            let (lhs, rhs) = (&kids[0], &kids[1]);

            if let Some(var_idx) = lhs.var_idx() {
                return Some((var_idx, rhs.clone()));
            } else if let Some(var_idx) = rhs.var_idx() {
                return Some((var_idx, lhs.clone()));
            }

            if lhs.typ().is_arith() {
                debug_assert! { rhs.is_zero() }

                let lhs = if let Some((_, term)) = lhs.cmul_inspect() {
                    term
                } else {
                    lhs
                };

                let mut add = vec![];
                let mut var = None;
                let mut negated = false;

                if let Some(kids) = lhs.add_inspect() {
                    for kid in kids {
                        if var.is_some() {
                            add.push(kid.clone());
                            continue;
                        }
                        if let Some(var_index) = kid.var_idx() {
                            debug_assert! { var.is_none() }
                            var = Some(var_index);
                            continue;
                        } else if let Some((val, term)) = kid.cmul_inspect() {
                            if let Some(var_index) = term.var_idx() {
                                if val.is_one() {
                                    var = Some(var_index);
                                    continue;
                                } else if val.is_minus_one() {
                                    var = Some(var_index);
                                    negated = true;
                                    continue;
                                }
                            }
                        }
                        add.push(kid.clone())
                    }

                    if let Some(var) = var {
                        let mut sum = term::add(add);
                        if !negated {
                            sum = term::u_minus(sum)
                        }
                        Some((var, sum))
                    } else {
                        None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Attempts to invert a term from a variable.
    pub fn invert_var(&self, var: VarIdx, typ: Typ) -> Option<(VarIdx, Term)> {
        self.invert(term::var(var, typ))
    }

    /// Attempts to invert a term.
    ///
    /// More precisely, if the term only mentions one variable `v`, attempts to
    /// find a `f` that's a solution of `var = term <=> v = f(var)`.
    ///
    /// Currently, only works when `v` appears exactly once. That is, it will
    /// fail on `var = 3.v + 7.v` for instance. (This would be fine if
    /// normalization handled this kind cases though.)
    ///
    /// Also, only works when all operators are binary (expect for unary minus).
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::term ;
    /// let term = term::u_minus( term::int_var(0) ) ;
    /// println!("{}", term) ;
    /// assert_eq!{
    ///     term.invert( term::int_var(1) ),
    ///     Some( (0.into(), term::u_minus( term::int_var(1) ) ) )
    /// }
    /// let term = term::sub( vec![ term::int_var(0), term::int(7) ] ) ;
    /// println!("{}", term) ;
    /// assert_eq!{
    ///     term.invert( term::int_var(1) ),
    ///     Some( (0.into(), term::add( vec![ term::int_var(1), term::int(7) ] ) ) )
    /// }
    /// let term = term::add( vec![ term::int(7), term::int_var(0) ] ) ;
    /// println!("{}", term) ;
    /// assert_eq!{
    ///     term.invert( term::int_var(1) ),
    ///     Some(
    ///         (0.into(), term::sub( vec![ term::int_var(1), term::int(7) ] ) )
    ///     )
    /// }
    /// ```
    pub fn invert(&self, term: Term) -> Option<(VarIdx, Term)> {
        let mut solution = term;
        let mut term = self;

        loop {
            // println!("inverting {}", term) ;
            match *term {
                RTerm::App { op, ref args, .. } => {
                    let (po, symmetric) = match op {
                        Op::Add => (Op::Sub, true),
                        Op::Sub => {
                            if args.len() == 1 {
                                solution = term::u_minus(solution);
                                term = &args[0];
                                continue;
                            } else if args.len() == 2 {
                                if args[0].val().is_some() {
                                    solution = term::sub(vec![args[0].clone(), solution]);
                                    term = &args[1];
                                    continue;
                                } else if args[1].val().is_some() {
                                    solution = term::add(vec![args[1].clone(), solution]);
                                    term = &args[0];
                                    continue;
                                }
                            }
                            return None;
                        }
                        Op::IDiv => return None,
                        Op::CMul => {
                            if args.len() == 2 {
                                if let Some(val) = args[0].val() {
                                    if val
                                        .minus()
                                        .expect("illegal c_mul application found in `invert`")
                                        .is_one()
                                    {
                                        solution = term::u_minus(solution);
                                        term = &args[1];
                                        continue;
                                    } else {
                                        return None;
                                    }
                                }
                            }

                            panic!("illegal c_mul application found in `invert`")
                        }
                        // Op::Div => (Op::Mul, false),
                        // Op::Mul => (Op::Div, true),
                        Op::ToReal => {
                            solution = term::to_int(solution);
                            term = &args[0];
                            continue;
                        }
                        Op::ToInt => {
                            solution = term::to_real(solution);
                            term = &args[0];
                            continue;
                        }
                        _ => return None,
                    };
                    if args.len() != 2 {
                        return None;
                    }

                    if let Some(arith) = args[0].arith() {
                        if symmetric {
                            solution = term::app(po, vec![solution, arith])
                        } else {
                            solution = term::app(op, vec![arith, solution])
                        }
                        term = &args[1]
                    } else if let Some(arith) = args[1].arith() {
                        solution = term::app(po, vec![solution, arith]);
                        term = &args[0]
                    } else {
                        return None;
                    }
                }

                RTerm::Var(_, v) => return Some((v, solution)),

                RTerm::Cst(_)
                | RTerm::Fun { .. }
                | RTerm::CArray { .. }
                | RTerm::DTypNew { .. }
                | RTerm::DTypSlc { .. }
                | RTerm::DTypTst { .. } => return None,
            }
        }
    }
}

/// Term evaluation.
impl RTerm {
    /// Term evaluation.
    ///
    /// Fails when the model given does not type-check with respect to the model provided.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::add( vec![term::int_var(0), term::int_var(2), term::int(17)] );
    /// let values: VarMap<_> = vec![
    ///     val::int(7), // v_0
    ///     val::int(0), // v_1 (not used in `t`)
    ///     val::int(2), // v_2
    /// ].into();
    /// assert_eq! { t.eval(&values).unwrap(), val::int(7 + 2 + 17) }
    ///
    /// let ill_typed: VarMap<_> = vec![
    ///     val::int(7),      // v_0
    ///     val::int(0),      // v_1 (not used in `t`)
    ///     val::bool(false), // v_2 ILL-TYPED
    /// ].into();
    /// assert! { t.eval(&ill_typed).is_err() }
    /// ```
    pub fn eval<E: Evaluator>(&self, model: &E) -> Res<Val> {
        eval::eval(&factory::term(self.clone()), model)
    }

    /// Term evaluation (int).
    ///
    /// Fails whenever [`self.eval(model)`] would fail, or if the term evaluates to a value that's
    /// not of type `Int`. Returns `None` if the model is partial and evaluation resulted in a
    /// non-value.
    ///
    /// In fact, this is strictly equivalent to `self.eval(model).and_then(|val| val.to_int())`.
    ///
    /// [`self.eval(model)`]: #method.eval (eval function over RTerm)
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::add( vec![term::int_var(0), term::int_var(2), term::int(17)] );
    /// let values: VarMap<_> = vec![
    ///     val::int(7), // v_0
    ///     val::int(0), // v_1 (not used in `t`)
    ///     val::int(2), // v_2
    /// ].into();
    /// assert_eq! { t.int_eval(&values).unwrap(), Some( (7 + 2 + 17).into() ) }
    /// ```
    #[inline]
    pub fn int_eval<E: Evaluator>(&self, model: &E) -> Res<Option<Int>> {
        self.eval(model)?.to_int()
    }

    /// Term evaluation (real).
    ///
    /// Fails whenever [`self.eval(model)`] would fail, or if the term evaluates to a value that's
    /// not of type `Real`. Returns `None` if the model is partial and evaluation resulted in a
    /// non-value.
    ///
    /// In fact, this is strictly equivalent to `self.eval(model).and_then(|val| val.to_real())`.
    ///
    /// [`self.eval(model)`]: #method.eval (eval function over RTerm)
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::add(
    ///     vec![term::real_var(0), term::real_var(2), term::real_of(17.)]
    /// );
    /// let values: VarMap<_> = vec![
    ///     val::real_of(7.), // v_0
    ///     val::real_of(0.), // v_1 (not used in `t`)
    ///     val::real_of(2.), // v_2
    /// ].into();
    /// assert_eq! { t.real_eval(&values).unwrap(), Some( rat_of_float(7. + 2. + 17.).into() ) }
    /// ```
    #[inline]
    pub fn real_eval<E: Evaluator>(&self, model: &E) -> Res<Option<Rat>> {
        self.eval(model)?.to_real()
    }

    /// Term evaluation (bool).
    ///
    /// Fails whenever [`self.eval(model)`] would fail, or if the term evaluates to a value that's
    /// not of type `Bool`. Returns `None` if the model is partial and evaluation resulted in a
    /// non-value.
    ///
    /// In fact, this is strictly equivalent to `self.eval(model).and_then(|val| val.to_bool())`.
    ///
    /// [`self.eval(model)`]: #method.eval (eval function over RTerm)
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use hoice::common::*;
    /// let t = term::ge(
    ///     term::add( vec![term::real_var(0), term::real_var(2), term::real_of(17.)] ),
    ///     term::real_of(42.)
    /// );
    /// let values: VarMap<_> = vec![
    ///     val::real_of(7.), // v_0
    ///     val::real_of(0.), // v_1 (not used in `t`)
    ///     val::real_of(2.), // v_2
    /// ].into();
    /// assert_eq! { t.bool_eval(&values).unwrap(), Some( false.into() ) }
    /// ```
    #[inline]
    pub fn bool_eval<E: Evaluator>(&self, model: &E) -> Res<Option<bool>> {
        self.eval(model)?.to_bool()
    }
}

/// Term writing.
impl RTerm {
    /// Writes a term in a writer.
    pub fn write<W, WriteVar>(&self, w: &mut W, write_var: WriteVar) -> IoRes<()>
    where
        W: Write,
        WriteVar: Fn(&mut W, VarIdx) -> IoRes<()>,
    {
        self.write_with(w, write_var, None)
    }

    /// Writes a term in a writer using optional bindings.
    ///
    /// Also takes some optional bindings. This is used when printing the body of a clause to apply
    /// let-binding factoring on the fly, while printing to the solver.
    pub fn write_with<W, WriteVar>(
        &self,
        w: &mut W,
        write_var: WriteVar,
        bindings: Option<&bindings::Bindings>,
    ) -> IoRes<()>
    where
        W: Write,
        WriteVar: Fn(&mut W, VarIdx) -> IoRes<()>,
    {
        self.write_with_raw(w, write_var, bindings.map(|b| b.bindings()))
    }

    /// Write a term in a writer.
    ///
    /// Factors code for `write` and `write_with` by taking optional bindings.
    fn write_with_raw<W, WriteVar>(
        &self,
        w: &mut W,
        write_var: WriteVar,
        bindings: Option<&[TermMap<VarIdx>]>,
    ) -> IoRes<()>
    where
        W: Write,
        WriteVar: Fn(&mut W, VarIdx) -> IoRes<()>,
    {
        // Stores triplets of
        // - the elements to write,
        // - the prefix string, written before next element
        // - the suffix, written once there's no more elements to write
        let mut stack = vec![(vec![self], "", "")];

        'work: while let Some((mut to_do, sep, end)) = stack.pop() {
            use self::RTerm::*;

            if let Some(this_term) = to_do.pop() {
                stack.push((to_do, sep, end));
                write!(w, "{}", sep)?;

                // Is term in the bindings?
                if let Some(bindings) = bindings {
                    for map in bindings {
                        if let Some(var) = map.get(&this_term.to_hcons()) {
                            Bindings::write_var(w, *var)?;
                            continue 'work;
                        }
                    }
                }

                match this_term {
                    Var(_, v) => write_var(w, *v)?,

                    Cst(val) => write!(w, "{}", val)?,

                    CArray { term, .. } => {
                        write!(
                            w,
                            "(({} {} {})",
                            keywords::op::as_,
                            keywords::op::const_,
                            this_term.typ()
                        )?;
                        stack.push((vec![term], " ", ")"))
                    }

                    App { op, args, .. } => {
                        write!(w, "({}", op)?;
                        stack.push((args.iter().rev().map(|t| t.get()).collect(), " ", ")"))
                    }

                    DTypSlc { name, term, .. } => {
                        write!(w, "({}", name)?;
                        stack.push((vec![term], " ", ")"))
                    }

                    DTypTst { name, term, .. } => {
                        write!(w, "({}-{}", keywords::op::is_, name)?;
                        stack.push((vec![term], " ", ")"))
                    }

                    DTypNew { name, args, .. } => {
                        if args.is_empty() {
                            write!(w, "{}", name)?
                        } else {
                            write!(w, "({}", name)?;
                            stack.push((args.iter().rev().map(|t| t.get()).collect(), " ", ")"))
                        }
                    }

                    Fun { name, args, .. } => {
                        if args.is_empty() {
                            write!(w, "{}", name)?
                        } else {
                            write!(w, "({}", name)?;
                            stack.push((args.iter().rev().map(|t| t.get()).collect(), " ", ")"))
                        }
                    }
                }
            } else {
                w.write_all(end.as_bytes())?
            }
        }

        Ok(())
    }
}

mylib::impl_fmt! {
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
impl<'a> PebcakFmt<'a> for RTerm {
    type Info = &'a VarMap<crate::info::VarInfo>;
    fn pebcak_err(&self) -> ErrorKind {
        "during term pebcak formatting".into()
    }
    fn pebcak_io_fmt<W: Write>(
        &self,
        w: &mut W,
        vars: &'a VarMap<crate::info::VarInfo>,
    ) -> IoRes<()> {
        self.write(w, |w, var| w.write_all(vars[var].as_bytes()))
    }
}
