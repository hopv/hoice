//! Term simplification.
//!
//! # TODO
//!
//! - a lot of collection cloning could be avoided in this module

pub use std::cmp::Ordering;
use std::ops::Deref;

use term::factory::NormRes;

use common::*;

lazy_static! {
    static ref simpl_solver: RwLock<Option<::rsmt2::Solver<()>>> =
        RwLock::new(if conf.check_simpl {
            Some(
                conf.solver
                    .spawn("check_simpl", (), &Instance::new())
                    .unwrap(),
            )
        } else {
            None
        });
}

/// Result of a simplification check between two terms.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum SimplRes {
    /// Nothing.
    None,
    /// The two terms are directly related.
    Cmp(Ordering),
    /// The two terms are equivalent to another term.
    Yields(Term),
}
impl SimplRes {
    /// Inverts the result.
    pub fn invert(self) -> Self {
        use self::SimplRes::*;
        match self {
            None => None,
            Cmp(ord) => Cmp(ord.reverse()),
            Yields(term) => Yields(term),
        }
    }
    /// True if `self` is not `None`.
    #[inline]
    pub fn is_some(&self) -> bool {
        self != &SimplRes::None
    }
    /// True if `self` is `None`.
    #[inline]
    pub fn is_none(&self) -> bool {
        !self.is_some()
    }
}

impl_fmt! {
    SimplRes(self, fmt) {
        match self {
            SimplRes::None => write!(fmt, "none"),
            SimplRes::Cmp(ord) => write!(fmt, "{:?}", ord),
            SimplRes::Yields(trm) => write!(fmt, "yields({})", trm),
        }
    }
}

/// Adds a term to a set understood as a conjunction.
///
/// Returns `true` if the resulting set is false.
pub fn conj_term_insert(term: Term, set: &mut TermSet) -> bool {
    let mut next_term = Some(term);
    let mut fls = false;
    let mut add_term;

    macro_rules! helper {
        (add term) => {
            next_term.is_none() && add_term
        };

        (is false) => {
            fls
        };
        (term dropped) => {
            next_term.is_none() && !add_term
        };
        (is true) => {
            !fls && helper!(term dropped)
        };

        (drop term) => {{
            next_term = None;
            add_term = false
        }};

        (set false) => {{
            fls = true;
            helper!(drop term)
        }};

        (set true) => {{
            debug_assert! { ! fls }
            helper!(drop term)
        }};

        (update $old_term:expr, to $term:expr) => {{
            $old_term = $term.clone();
            next_term = Some($term);
        }};
    }

    while let Some(mut term) = ::std::mem::replace(&mut next_term, None) {
        add_term = true;

        set.retain(|set_term| {
            if helper!(is false) {
                return false;
            }
            if helper!(is true) {
                return true;
            }

            use std::cmp::Ordering::*;
            match conj_simpl(&term, set_term) {
                SimplRes::None => true,

                SimplRes::Cmp(Less) | SimplRes::Cmp(Equal) => {
                    helper!(drop term);
                    true
                }

                SimplRes::Cmp(Greater) => false,

                SimplRes::Yields(nu_term) => match nu_term.bool() {
                    Some(true) => {
                        helper!(set true);
                        false
                    }
                    Some(false) => {
                        helper!(set false);
                        false
                    }
                    None => {
                        helper!(update term, to nu_term);
                        false
                    }
                },
            }
        });

        if helper!(add term) {
            let is_new = set.insert(term);
            debug_assert! { is_new }
        }
    }

    if fls {
        set.clear();
        set.insert(term::fls());
    }
    fls
}

/// Simplifies a conjunction.
fn conj_vec_simpl(terms: &mut Vec<Term>) {
    let mut res = Vec::with_capacity(terms.len());

    'add_terms: while let Some(term) = terms.pop() {
        let mut cnt = 0;

        while cnt < res.len() {
            use self::SimplRes::*;
            use std::cmp::Ordering::*;

            match conj_simpl(&term, &res[cnt]) {
                None => cnt += 1,

                Cmp(Less) | Cmp(Equal) => continue 'add_terms,

                Cmp(Greater) => {
                    res.swap_remove(cnt);
                }

                Yields(term) => {
                    res.swap_remove(cnt);
                    terms.push(term);
                    continue 'add_terms;
                }
            }
        }

        res.push(term)
    }

    res.shrink_to_fit();
    res.sort_unstable();
    res.dedup();

    ::std::mem::swap(terms, &mut res)
}

/// Checks the conjunction of two terms for simplification.
///
/// Returns
///
/// - `None` if no conclusion was reached,
/// - `Cmp(Greater)` if `lhs => rhs`,
/// - `Cmp(Less)` if `lhs <= rhs`,
/// - `Cmp(Equal)` if `lhs` and `rhs` are equivalent.
/// - `Yields(term)` if `lhs and rhs` is equivalent to `term`.
///
/// So *greater* really means *stronger*.
///
/// # Examples
///
/// ```rust
/// use std::cmp::Ordering::* ;
/// use hoice::term::simplify::SimplRes::* ;
/// use hoice::term::simplify::conj_simpl ;
/// use hoice::term ;
///
/// let lhs = term::not(
///   term::lt(
///     term::int(0),
///     term::sub( vec![ term::int(3), term::int_var(0) ] )
///   )
/// ) ;
/// # println!("   {}", lhs) ;
/// let rhs = term::ge( term::int_var(0), term::int(3) ) ;
/// # println!("=> {}\n\n", rhs) ;
/// assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Equal) }
///
/// # println!("   {}", lhs) ;
/// let rhs = term::ge( term::int_var(0), term::int(7) ) ;
/// # println!("<= {}\n\n", rhs) ;
/// assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Less) }
///
/// # println!("   {}", rhs) ;
/// # println!("=> {}\n\n", lhs) ;
/// assert_eq! { conj_simpl(& rhs, & lhs), Cmp(Greater) }
///
/// let lhs = term::gt( term::int_var(0), term::int(7) ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Greater) }
///
// / let lhs = term::le( term::int_var(0), term::int(7) ) ;
// / # println!("   {}", lhs) ;
// / # println!("=> {}\n\n", rhs) ;
// / let expected = term::eq( term::int_var(0), term::int(7) ) ;
// / debug_assert_eq! { conj_simpl(& lhs, & rhs), Yields(expected) }
///
/// let lhs = term::le( term::int_var(1), term::int(7) ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// assert_eq! { conj_simpl(& lhs, & rhs), None }
///
/// let lhs = term::le( term::int_var(1), term::int(7) ) ;
/// let rhs = term::or(
///   vec![ lhs.clone(), term::eq( term::int_var(3), term::int(7) ) ]
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Greater) }
///
/// # println!("   {}", rhs) ;
/// # println!("=> {}\n\n", lhs) ;
/// assert_eq! { conj_simpl(& rhs, & lhs), Cmp(Less) }
///
/// let lhs = term::gt( term::real_var(1), term::real_zero() ) ;
/// let rhs = term::ge(
///   term::real_var(1), term::real_zero()
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// assert_eq! { conj_simpl(& lhs, & rhs), Cmp(Greater) }
///
/// # println!("   {}", rhs) ;
/// # println!("=> {}\n\n", lhs) ;
/// assert_eq! { conj_simpl(& rhs, & lhs), Cmp(Less) }
///
/// let lhs = term::or(
///   vec![
///     term::bool_var(0), term::gt( term::real_var(1), term::real_zero() )
///   ]
/// ) ;
/// let rhs = term::ge(
///   term::real_var(1), term::real_zero()
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// assert_eq! { conj_simpl(& lhs, & rhs), None }
///
/// let lhs = term::or(
///   vec![
///     term::bool_var(0), term::gt( term::real_var(1), term::real_zero() )
///   ]
/// ) ;
/// let rhs = term::eq(
///   term::real_var(1), term::real_zero()
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// assert_eq! { conj_simpl(& lhs, & rhs), None }
///
/// let rhs = term::or(
///   vec![
///     term::bool_var(0), term::gt( term::real_var(1), term::real_zero() )
///   ]
/// ) ;
/// let lhs = term::eq(
///   term::real_var(1), term::real_zero()
/// ) ;
/// # println!("   {}", lhs) ;
/// # println!("=> {}\n\n", rhs) ;
/// assert_eq! { conj_simpl(& lhs, & rhs), None }
/// ```
pub fn conj_simpl<T1, T2>(lhs: &T1, rhs: &T2) -> SimplRes
where
    T1: Deref<Target = RTerm>,
    T2: Deref<Target = RTerm>,
{
    if conf.term_simpl == 0 {
        return SimplRes::None;
    }
    let res = conj_simpl_2(lhs, rhs);

    if res.is_some() {
        if let Some(solver) = simpl_solver
            .write()
            .expect("could not retrieve term simplification solver")
            .as_mut()
        {
            solver
                .push(1)
                .expect("error on `push` during term simplification");
            let mut vars = VarSet::new();
            lhs.iter(|term| {
                if let Some(idx) = term.var_idx() {
                    let is_new = vars.insert(idx);
                    if is_new {
                        solver
                            .declare_const(&format!("{}", term), term.typ().get())
                            .expect("error on `declare_const` during term simplification (lhs)")
                    }
                }
            });
            rhs.iter(|term| {
                if let Some(idx) = term.var_idx() {
                    let is_new = vars.insert(idx);
                    if is_new {
                        solver
                            .declare_const(&format!("{}", term), term.typ().get())
                            .expect("error on `declare_const` during term simplification (rhs)")
                    }
                }
            });

            use std::cmp::Ordering::*;
            let check = match res {
                SimplRes::Cmp(Equal) => format!("(= {} {})", lhs.deref(), rhs.deref()),
                SimplRes::Cmp(Less) => format!("(=> {} {})", rhs.deref(), lhs.deref()),
                SimplRes::Cmp(Greater) => format!("(=> {} {})", lhs.deref(), rhs.deref()),
                SimplRes::Yields(ref term) => {
                    format!("(= (and {} {}) {})", lhs.deref(), rhs.deref(), term)
                }
                SimplRes::None => unreachable!(),
            };

            solver
                .assert(&format!("(not {})", check))
                .expect("error on `assert` during term simplification");

            if solver
                .check_sat()
                .expect("could not retrieve check-sat result in conjunction simplification")
            {
                log! { @0
                  " " ;
                  "{}", lhs.deref() ;
                  "{}", rhs.deref() ;
                  "{:?}", res ;
                  " "
                }
                panic! { "simplification failure" }
            }

            solver
                .pop(1)
                .expect("error on `pop` during term simplification")
        }
    }

    res
}

fn conj_simpl_2<T1, T2>(lhs: &T1, rhs: &T2) -> SimplRes
where
    T1: Deref<Target = RTerm>,
    T2: Deref<Target = RTerm>,
{
    use std::cmp::Ordering::*;

    // A term is equal to itself.
    if lhs.deref() == rhs.deref() {
        return SimplRes::Cmp(Equal);
    }

    // A term and its negation yield false.
    if let Some(sub_lhs) = lhs.neg_inspect() {
        if sub_lhs.get() == rhs.deref() { return SimplRes::Yields(term::fls()) }
    }
    if let Some(sub_rhs) = rhs.neg_inspect() {
        if sub_rhs.get() == lhs.deref() { return SimplRes::Yields(term::fls()) }
    }

    if let Some(args) = lhs.disj_inspect() {
        let mut greater_count = 0;
        let mut yields = vec![];
        for lhs in args {
            match int_conj_simpl(lhs, rhs) {
                SimplRes::Cmp(Equal) | SimplRes::Cmp(Less) => return SimplRes::Cmp(Less),
                SimplRes::Cmp(Greater) => greater_count += 1,

                SimplRes::Yields(term) => yields.push(term),
                SimplRes::None => (),
            }
        }
        if yields.len() == args.len() {
            return SimplRes::Yields(term::or(yields));
        } else if greater_count == args.len() {
            return SimplRes::Cmp(Greater);
        }
    } else if let Some(args) = rhs.disj_inspect() {
        let mut less_count = 0;
        let mut yields = vec![];
        for rhs in args {
            match int_conj_simpl(lhs, rhs) {
                SimplRes::Cmp(Equal) | SimplRes::Cmp(Greater) => return SimplRes::Cmp(Greater),
                SimplRes::Cmp(Less) => less_count += 1,

                SimplRes::Yields(term) => yields.push(term),
                SimplRes::None => (),
            }
        }
        if yields.len() == args.len() {
            return SimplRes::Yields(term::or(yields));
        } else if less_count == args.len() {
            return SimplRes::Cmp(Greater);
        }
    }

    int_conj_simpl(lhs, rhs)
}

/// Result of deconstructing a sum.
///
/// This is used in `int_deconstruct` below to deconstruct additions to compare relation over
/// arithmetic terms as a sum of non-constant terms (lhs), an operator and a constant (rhs). The
/// goal is to do without cloning anything.
struct Deconstructed<'a> {
    /// Terms of the sum.
    trms: Vec<&'a Term>,
}

impl<'a> From<&'a Term> for Deconstructed<'a> {
    fn from(trm: &'a Term) -> Deconstructed<'a> {
        Deconstructed { trms: vec![trm] }
    }
}
impl<'a> From<Vec<&'a Term>> for Deconstructed<'a> {
    fn from(mut trms: Vec<&'a Term>) -> Deconstructed<'a> {
        if trms.is_empty() {
            panic!("trying to create an empty deconstructed term")
        }
        trms.sort_unstable();
        Deconstructed { trms }
    }
}

impl<'a> Deconstructed<'a> {
    /// Turns a deconstructed sum in a term.
    fn into_term(self) -> Term {
        if self.trms.len() == 1 {
            self.trms[0].clone()
        } else {
            term::add(self.trms.into_iter().cloned().collect())
        }
    }
    /// True if the two deconstructed sum are the same.
    fn equal(&self, other: &Self) -> bool {
        if self.trms.len() == other.trms.len() {
            for (t_1, t_2) in self.trms.iter().zip(other.trms.iter()) {
                if t_1 != t_2 {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
    /// True if the two deconstructed terms add to zero.
    fn is_opposite(&self, other: &Self) -> bool {
        if self.trms.len() == other.trms.len() {
            for t_1 in &self.trms {
                let t_1 = &term::u_minus((*t_1).clone());
                if other.trms.iter().all(|t| *t != t_1) {
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
}

/// Deconstructs a relation between arithmetic subterms.
fn int_deconstruct<T>(term: &T) -> Option<(Op, Deconstructed, Val)>
where
    T: Deref<Target = RTerm>,
{
    if let Some((op, args)) = term.deref().app_inspect() {
        if args.len() != 2 && !args[0].typ().is_arith() {
            return None;
        }

        let mut val = if let Some(val) = args[1].val() {
            val
        } else {
            return None;
        };

        if let Some(subargs) = args[0].add_inspect() {
            let mut sum = Vec::with_capacity(subargs.len());

            for arg in subargs {
                if let Some(v) = arg.val() {
                    val = val
                        .add(&v.minus().expect("type inconsistency"))
                        .expect("type inconsistency")
                } else {
                    sum.push(arg)
                }
            }

            let res: Deconstructed = if sum.len() == 1 {
                sum.pop().expect("sum has length 1").into()
            } else if subargs.len() == sum.len() {
                (&args[0]).into()
            } else if sum.is_empty() {
                // This should be unreachable.
                return None;
            } else {
                sum.into()
            };

            Some((op, res, val))
        } else {
            Some((op, (&args[0]).into(), val))
        }
    } else {
        None
    }
}

fn int_conj_simpl<T1, T2>(lhs_term: &T1, rhs_term: &T2) -> SimplRes
where
    T1: Deref<Target = RTerm>,
    T2: Deref<Target = RTerm>,
{
    use std::cmp::Ordering::*;
    // Input boolean is true (false) for `lhs` => `rhs` (reversed).
    macro_rules! ord_of_bool {
        ($b:expr) => {
            if $b {
                SimplRes::Cmp(Greater)
            } else {
                SimplRes::Cmp(Less)
            }
        };
    }

    let (lhs, rhs) = (lhs_term.deref(), rhs_term.deref());

    // A term is equal to itself.
    if lhs == rhs {
        return SimplRes::Cmp(Equal);
    }

    match (lhs.bool(), rhs.bool()) {
        // True can only imply true.
        (Some(true), rhs) => return ord_of_bool!(rhs.unwrap_or(false)),
        // False implies anything.
        (Some(false), _) => return ord_of_bool!(true),
        // False can only be implied by false.
        (lhs, Some(false)) => return ord_of_bool!(!lhs.unwrap_or(true)),
        // True is implied by anything.
        (_, Some(true)) => return ord_of_bool!(true),
        // Otherwise we don't know (yet).
        (None, None) => (),
    }

    let (lhs_op, lhs_trm, lhs_cst) = if let Some(res) = int_deconstruct(lhs_term) {
        res
    } else {
        return SimplRes::None;
    };

    let (rhs_op, rhs_trm, rhs_cst) = if let Some(res) = int_deconstruct(rhs_term) {
        res
    } else {
        return SimplRes::None;
    };

    // println!();
    // println!("lhs:");
    // println!("  {} {} {}", lhs_trm.to_string(), lhs_op, lhs_cst);
    // println!("rhs:");
    // println!("  {} {} {}", rhs_trm.to_string(), rhs_op, rhs_cst);

    if lhs_trm.equal(&rhs_trm) {
        match (lhs_op, rhs_op) {
            (Op::Gt, Op::Gt) | (Op::Ge, Op::Ge) => {
                return SimplRes::Cmp(
                    lhs_cst.get().compare(&rhs_cst).expect(
                        "error during comparison unwrapping in term simplification (same op)",
                    ),
                )
            }

            (Op::Gt, Op::Ge) | (Op::Ge, Op::Gt) => {
                if lhs_cst == rhs_cst {
                    if lhs_op == Op::Gt {
                        return SimplRes::Cmp(Greater);
                    } else {
                        return SimplRes::Cmp(Less);
                    }
                } else {
                    return SimplRes::Cmp(lhs_cst.get().compare(&rhs_cst).expect(
                        "error during comparison unwrapping in term simplification (diff op)",
                    ));
                }
            }

            (Op::Eql, Op::Ge) | (Op::Eql, Op::Gt) => match lhs_cst.get().compare(&rhs_cst) {
                Some(Less) => return SimplRes::Yields(term::fls()),
                Some(Equal) if rhs_op == Op::Gt => return SimplRes::Yields(term::fls()),
                Some(Equal) | Some(Greater) => return SimplRes::Cmp(Greater),
                None => unreachable!(),
            },

            (Op::Ge, Op::Eql) | (Op::Gt, Op::Eql) => match rhs_cst.get().compare(&lhs_cst) {
                Some(Less) => return SimplRes::Yields(term::fls()),
                Some(Equal) if lhs_op == Op::Gt => return SimplRes::Yields(term::fls()),
                Some(Equal) | Some(Greater) => return SimplRes::Cmp(Less),
                None => unreachable!(),
            },

            (Op::Eql, Op::Eql) => if rhs_cst.equal(&lhs_cst) {
                return SimplRes::Cmp(Greater);
            } else {
                return SimplRes::Yields(term::fls());
            },

            _ => (),
        }
    } else if lhs_op == Op::Ge
        && rhs_op == Op::Ge
        && lhs_cst == rhs_cst
            .minus()
            .expect("error during rhs inversion in term simplification")
        && lhs_trm.is_opposite(&rhs_trm)
    {
        return SimplRes::Yields(term::eq(
            lhs_trm.into_term(),
            lhs_cst
                .to_term()
                .expect("error during lhs cst to term conversion in term simplification"),
        ));
    }

    SimplRes::None
}

/// Fails if the number of arguments is wrong.
macro_rules! arity {
    ($op:expr => $args:expr, $len:expr) => {
        if $args.len() != $len {
            panic!(
                "illegal application of `{}` to {} arguments",
                $op,
                $args.len()
            )
        }
    };
}
macro_rules! simpl_fun {
  ( $(fn $name:ident($args:pat) $body:expr);* $(;)* ) => (
    $(
      pub fn $name($args: & mut Vec<Term>) -> Option<NormRes> {
        $body
      }
    )*
  ) ;
  ( $(fn $name:ident($op:pat, $args:pat) $body:expr);* $(;)* ) => (
    $(
      pub fn $name($op: & mut Op, $args: & mut Vec<Term>) -> Option<NormRes> {
        $body
      }
    )*
  ) ;
}

// Polymorphic operations.

simpl_fun! {
  // Equal.
  fn eql(args) {
    if args.len() == 2 {

      if args[0] == args[1] {
        return Some(
          NormRes::Term( term::tru() )
      )

      } else if let Some(b) = args[0].bool() {

        return Some(
          NormRes::Term(
            if b {
              args[1].clone()
            } else {
              term::not( args[1].clone() )
            }
          )
        )

      } else if let Some(b) = args[1].bool() {

        return Some(
          NormRes::Term(
            if b {
              args[0].clone()
            } else {
              term::not( args[0].clone() )
            }
          )
        )

      } else if let (Some(r_1), Some(r_2)) = (
        args[0].real(), args[1].real()
      ) {

        return Some(
          NormRes::Term( term::bool( r_1 == r_2 ) )
        )

      } else if let (Some(i_1), Some(i_2)) = (
        args[0].int(), args[1].int()
      ) {

        return Some(
          NormRes::Term( term::bool( i_1 == i_2 ) )
        )

      } else if args[0].typ().is_arith() {

        // println!("  (= {} {})", args[0], args[1]) ;
        if ! args[1].is_zero() {
          let (rhs, lhs) = (args.pop().unwrap(), args.pop().unwrap()) ;
          let typ = rhs.typ() ;
          let lhs = if lhs.is_zero() { NormRes::Term(rhs) } else {
            NormRes::App(
              typ.clone(), Op::Sub, vec![
                NormRes::Term(lhs), NormRes::Term(rhs)
              ]
            )
          } ;
          return Some(
            NormRes::App(
              typ::bool(), Op::Eql, vec![
                lhs, NormRes::Term( typ.default_val().to_term().unwrap() )
              ]
            )
          )
        } else {
          // Rhs is zero, now normalize lhs. This is a bit ugly...
          let mut u_minus_lhs = term::u_minus(args[0].clone()) ;
          if u_minus_lhs.uid() < args[0].uid() {
            ::std::mem::swap(& mut args[0], & mut u_minus_lhs)
          }
        }

      // } else if let Some(val) = args[0].val() {
      //   if let Some( (_, constructor, dtyp_args) ) = val.dtyp_inspect() {
      //     if dtyp_args.is_empty() {
      //       return Some(
      //         NormRes::Term(
      //           term::dtyp_tst(
      //             constructor.into(), args[1].clone()
      //           )
      //         )
      //       )
      //     }
      //   }
      // } else if let Some(val) = args[1].val() {
      //   if let Some( (_, constructor, dtyp_args) ) = val.dtyp_inspect() {
      //     if dtyp_args.is_empty() {
      //       return Some(
      //         NormRes::Term(
      //           term::dtyp_tst(
      //             constructor.into(), args[0].clone()
      //           )
      //         )
      //       )
      //     }
      //   }
      }

    } else {

      args.sort_unstable() ;
      let len = args.len() ;
      let mut args = args.drain(0..) ;
      let mut conj = vec![] ;
      if let Some(first) = args.next() {
        for arg in args {
          conj.push(
            NormRes::App(
              typ::bool(), Op::Eql, vec![
                NormRes::Term( first.clone() ),
                NormRes::Term(arg)
              ]
            )
          )
        }
        if ! conj.is_empty() {
          return Some(
            NormRes::App(typ::bool(), Op::And, conj)
          )
        }
      }
      panic!(
        "illegal application of `=` to {} (< 2) argument", len
      )
    }

    None
  } ;

  // If-then-else.
  fn ite(args) {
    arity!("ite" => args, 3) ;

    if let Some(b) = args[0].bool() {
      let (e, t) = ( args.pop().unwrap(), args.pop().unwrap() ) ;
      Some(
        NormRes::Term(
          if b { t } else { e }
        )
      )
    } else if args[1] == args[2] {
      Some( // "else" term
        NormRes::Term( args.pop().unwrap() )
      )
    } else if args[1].typ().is_bool()
    && args[0].dtyp_tst_inspect().is_none() {
      let (e, t, c) = (
        args.pop().unwrap(), args.pop().unwrap(), args.pop().unwrap()
      ) ;
      Some(
        NormRes::App(
          typ::bool(), Op::Or, vec![
            NormRes::App(
              typ::bool(), Op::And, vec![
                NormRes::Term( c.clone() ),
                NormRes::Term( t ),
              ]
            ),
            NormRes::App(
              typ::bool(), Op::And, vec![
                NormRes::Term( term::not(c) ),
                NormRes::Term( e ),
              ]
            ),
          ]
        )
      )
    } else if let Some(eq_args) = args[0].eq_inspect().cloned() {

      if let Some(val) = eq_args[0].val() {
        if let Some( (_, constructor, dtyp_args) ) = val.dtyp_inspect() {
          if dtyp_args.is_empty() {
            args[0] = term::dtyp_tst(
              constructor, eq_args[1].clone()
            )
          }
        }
      } else if let Some(val) = eq_args[1].val() {
        if let Some( (_, constructor, dtyp_args) ) = val.dtyp_inspect() {
          if dtyp_args.is_empty() {
            args[0] = term::dtyp_tst(
              constructor, eq_args[0].clone()
            )
          }
        }
      }

      None
    } else {
      None
    }
  } ;

  // Distinct.
  fn distinct(args) {
    if args.len() == 2 {
      Some(
        NormRes::App(
          typ::bool(), Op::Not, vec![
            NormRes::App(
              typ::bool(), Op::Eql, args.drain(0..).map(
                NormRes::Term
              ).collect()
            ),
          ]
        )
      )
    } else {
      args.sort_unstable() ;
      None
    }
  }
}

// Boolean operations.

simpl_fun! {
  fn and(args) {
    args.sort_unstable() ;
    args.dedup() ;

    let mut cnt = 0 ;

    while cnt < args.len() {
      if let Some(b) = args[cnt].bool() {
        if b {
          args.swap_remove(cnt) ;
          ()
        } else {
          return Some(
            NormRes::Term( term::fls() )
          )
        }
      } else if let Some(conj) = args[cnt].conj_inspect().cloned() {
        for term in conj {
          args.push(term)
        }
        args.swap_remove(cnt) ;
        args.dedup() ;
        cnt = 0
      } else {
        cnt += 1
      }
    }

    // if conf.term_simpl >= 3 {
    conj_vec_simpl(args) ;
    // }

    if args.is_empty() {
      Some(
        NormRes::Term( term::tru() )
      )
    } else if args.len() == 1 {
      Some(
        NormRes::Term( args.pop().unwrap() )
      )
    } else {
      None
    }
  } ;

  // Disjunction.
  fn or(args) {
    args.sort_unstable() ;
    args.dedup() ;

    let mut cnt = 0 ;

    while cnt < args.len() {

      if let Some(b) = args[cnt].bool() {
        if ! b {
          args.swap_remove(cnt) ;
          ()
        } else {
          return Some(
            NormRes::Term( term::tru() )
          )
        }
      } else if let Some(disj) = args[cnt].disj_inspect().cloned() {
        for term in disj {
          args.push(term)
        }
        args.swap_remove(cnt) ;
      } else {
        cnt += 1
      }
    }

    if args.is_empty() {
      Some(
        NormRes::Term( term::fls() )
      )
    } else if args.len() == 1 {
      Some(
        NormRes::Term( args.pop().unwrap() )
      )
    } else {
      None
    }
  } ;

  // Negation.
  fn not(args) {
    arity!("not" => args, 1) ;

    if let Some(b) = args[0].bool() {
      return Some(
        NormRes::Term( term::bool(! b) )
      )
    }

    match args[0].get() {
      RTerm::App { op: Op::Not, ref args, .. } => Some(
        NormRes::Term( args[0].clone() )
      ),

      RTerm::App { op: Op::And, ref args, .. } => Some(
        NormRes::App(
          typ::bool(), Op::Or, args.iter().map(
            |arg| NormRes::App(
              typ::bool(), Op::Not, vec![ NormRes::Term( arg.clone() ) ]
            )
          ).collect()
        )
      ),
      RTerm::App { op: Op::Or, ref args, .. } => Some(
        NormRes::App(
          typ::bool(), Op::And, args.iter().map(
            |arg| NormRes::App(
              typ::bool(), Op::Not, vec![ NormRes::Term( arg.clone() ) ]
            )
          ).collect()
        )
      ),

      RTerm::App { op: Op::Gt, ref args, .. } => Some(
        NormRes::App(
          typ::bool(), Op::Ge, args.iter().map(
            |arg| NormRes::Term( arg.clone() )
          ).rev().collect()
          //^^^~~~~ IMPORTANT.
        )
      ),

      RTerm::App { op: Op::Ge, ref args, .. } => Some(
        NormRes::App(
          typ::bool(), Op::Gt, args.iter().map(
            |arg| NormRes::Term( arg.clone() )
          ).rev().collect()
          //^^^~~~~ IMPORTANT.
        )
      ),

      RTerm::App { op: Op::Lt, ref args, .. } => Some(
        NormRes::App(
          typ::bool(), Op::Ge, args.iter().map(
            |arg| NormRes::Term( arg.clone() )
          ).collect()
        )
      ),

      RTerm::App { op: Op::Le, ref args, .. } => Some(
        NormRes::App(
          typ::bool(), Op::Gt, args.iter().map(
            |arg| NormRes::Term( arg.clone() )
          ).collect()
        )
      ),

      _ => None,
    }
  } ;

  // Implication.
  fn implies(args) {
    arity!("=>" => args, 2) ;
    let (rgt, lft) = (
      args.pop().unwrap(), args.pop().unwrap()
    ) ;
    Some(
      NormRes::App(
        typ::bool(), Op::Or, vec![
          NormRes::App(typ::bool(), Op::Not, vec![ NormRes::Term(lft) ]),
          NormRes::Term(rgt)
        ]
      )
    )
  }
}

// Relation operators over arithmetic terms.

simpl_fun! {
  // Greater than, greater than or equal to.
  fn gt_ge(op, args) {
    arity!( format!("{}", op) => args, 2 ) ;

    if args[0] == args[1] {
      return Some(
        NormRes::Term( term::bool( * op == Op::Ge ) )
      )
    }

    let (mut rhs, lhs) = (
      args.pop().unwrap(), args.pop().unwrap()
    ) ;

    if let Some(rhs_val) = rhs.val() {

      // If lhs is also a constant, we done.
      if let Some(lhs_val) = lhs.val() {
        let res = if * op == Op::Ge {
          lhs_val.get().g_e(& rhs_val).unwrap()
        } else {
          lhs_val.get().g_t(& rhs_val).unwrap()
        } ;
        return Some(
          NormRes::Term(
            term::bool( res.to_bool().unwrap().unwrap() )
          )
        )
      }

      // Is lhs a sum with a constant in it?.
      let mut correction = None ;
      if let Some(kids) = lhs.add_inspect() {
        for kid in kids {
          if let Some(cst) = kid.val() {
            correction = if let Some(c) = correction {
              Some( cst.add(& c).unwrap() )
            } else {
              Some(cst)
            }
          }
        }
      }

      if let Some(correction) = correction {
        Some(
          NormRes::App(
            typ::bool(), * op, vec![
              NormRes::App(
                lhs.typ(), Op::Sub, vec![
                  NormRes::Term(lhs),
                  NormRes::Term( correction.clone().to_term().unwrap() ),
                ]
              ),
              NormRes::Term(
                rhs_val.sub(& correction).unwrap().to_term().unwrap()
              )
            ]
          )
        )
      } else {
        // Normalize Gt to Ge for integers.
        if * op == Op::Gt {
          if let val::RVal::I(ref i) = rhs_val.get() {
            rhs = term::int(i + 1) ;
            * op = Op::Ge
          }
        }

        args.push(lhs) ;
        args.push(rhs) ;

        None
      }

    } else {

      // Rhs is not a constant.
      let typ = rhs.typ() ;
      Some(
        NormRes::App(
          typ::bool(), * op, vec![
            NormRes::App(
              typ.clone(), Op::Sub, vec![
                NormRes::Term(lhs),
                NormRes::Term(rhs),
              ]
            ),
            NormRes::Term(
              if typ == typ::int() {
                term::int_zero()
              } else {
                term::real_zero()
              }
            )
          ]
        )
      )
    }
  } ;

  // Less than, less than or equal.
  fn lt_le(op, args) {
    if * op == Op::Le {
      * op = Op::Ge
    } else {
      * op = Op::Gt
    }

    Some(
      NormRes::App(
        typ::bool(), * op,
        args.drain(0..).map(
          NormRes::Term
        ).rev().collect()
      )// ^^^~~~~ Important.
    )
  } ;
}

// Arithmetic operations.

simpl_fun! {

  // Modulo.
  fn modulo(args) {
    arity!("mod" => args, 2) ;

    if let Some(rhs) = args[1].val() {
      if rhs.is_one() {
        return Some(
          NormRes::Term( term::int(0) )
        )
      } else if let Some(lhs) = args[0].val() {
        return Some(
          NormRes::Term(
            lhs.modulo(& rhs).expect(
              "illegal application of `mod`"
            ).to_term().unwrap()
          )
        )
      }
    }

    None
  } ;

  // Remainder.
  fn rem(args) {
    arity!("rem" => args, 2) ;

    if let Some(rhs) = args[1].val() {
      if rhs.is_one() {
        return Some(
          NormRes::Term( term::int(0) )
        )
      } else if let Some(lhs) = args[0].val() {
        return Some(
          NormRes::Term(
            lhs.modulo(& rhs).expect(
              "illegal application of `rem`"
            ).to_term().unwrap()
          )
        )
      }
    }

    None
  } ;

  // Division.
  fn div(args) {
    arity!("/" => args, 2) ;

    let (num, den) = (& args[0], & args[1]) ;

    if num.is_zero() {

      return Some(
        NormRes::Term( term::real_zero() )
      )

    } else if den.is_one() {

      if let Some(num) = num.int() {
        return Some(
          NormRes::Term(
            term::real( Rat::new(num, 1.into()) )
          )
        )
      } else {
        return Some(
          NormRes::Term( num.clone() )
        )
      }

    } else if let ( Some(num), Some(den) ) = ( num.val(), den.val() ) {

      return Some(
        NormRes::Term(
          term::real(
            num.div(& den).unwrap().to_real().unwrap().unwrap()
          )
        )
      )

    }

    None
  } ;


  // Addition.
  fn add(args) {
    let typ = args[0].typ() ;

    let (mut sum, one) = if typ.is_int() {
      ( val::int(0), val::int(1) )
    } else {
      (
        val::real( Rat::new(0.into(), 1.into())),
        val::real( Rat::new(1.into(), 1.into()))
      )
    } ;

    let mut c_args = TermMap::<Val>::new() ;
    let mut changed = false ;

    while let Some(arg) = args.pop() {
      if let Some(kids) = arg.add_inspect().cloned() {
        args.extend(kids)
      } else if let Some(v) = arg.val() {
        sum = sum.add(& v).expect(
          "during add simplification"
        )
      } else {
        let (val, term) = if let Some((val, term)) = arg.cmul_inspect() {
          (val, term)
        } else {
          (one.clone(), & arg)
        } ;

        if let Some(value) = c_args.get_mut(term) {
          * value = value.add(& val).expect(
            "during add simplification"
          ) ;
          changed = true ;
          continue
        }

        c_args.insert(term.clone(), val) ;
      }
    }

    if changed {
      let mut args = vec![
        NormRes::Term( sum.to_term().unwrap() )
      ] ;
      for (term, coef) in c_args {
        if coef.is_zero() {
          continue
        } else if coef.is_one() {
          args.push( NormRes::Term(term) )
        } else {
          args.push(
            NormRes::App(
              typ.clone(), Op::CMul, vec![
                NormRes::Term( coef.to_term().unwrap() ),
                NormRes::Term(term)
              ]
            )
          )
        }
      }

      return Some(
        NormRes::App(typ, Op::Add, args)
      )
    }

    for (term, coef) in c_args {
      if coef.is_zero() {
        continue
      } else if coef.is_one() {
        args.push(term)
      } else {
        args.push( term::cmul(coef.get().clone(), term) )
      }
    }

    if args.is_empty() {
      Some(
        NormRes::Term(
          sum.to_term().expect(
            "coefficient cannot be unknown"
          )
        )
      )
    } else if sum.is_zero() {
      if args.is_empty() {
        Some(
          NormRes::Term(
            sum.to_term().unwrap_or_else(
              || panic!(
                "failed to retrieve term from sum `{}`", sum
              )
            )
          )
        )
      } else if args.len() == 1 {
        Some(
          NormRes::Term( args.pop().unwrap() )
        )
      } else {
        args.sort_unstable() ;
        None
      }
    } else {
      let sum = sum.to_term().expect(
        "coefficient cannot be unknown"
      ) ;
      args.push(sum) ;
      args.sort_unstable() ;
      None
    }
  } ;

  // Subtraction.
  fn sub(args) {
    let mut args = args.drain(0 ..) ;

    if let Some(first) = args.next() {

      if args.len() == 0 {
        if let Some(i) = first.int_val().cloned() {
          Some(
            NormRes::Term( term::int(- i) )
          )
        } else if let Some(r) = first.real_val().cloned() {
          Some(
            NormRes::Term( term::real( -r ) )
          )
        } else {
          let minus_one = if first.typ() == typ::int() {
            term::int( - Int::one() )
          } else {
            term::real( - Rat::one() )
          } ;

          Some(
            NormRes::App(
              first.typ(), Op::CMul, vec![
                NormRes::Term(minus_one),
                NormRes::Term(first),
              ]
            )
          )
        }

      } else {
        let minus_one = if first.typ() == typ::int() {
          term::int( - Int::one() )
        } else {
          term::real( - Rat::one() )
        } ;
        let typ = first.typ() ;

        let mut to_do = Vec::with_capacity( args.len() + 1 ) ;
        to_do.push( NormRes::Term(first) ) ;
        for arg in args {
          to_do.push(
            NormRes::App(
              typ.clone(), Op::CMul, vec![
                NormRes::Term( minus_one.clone() ),
                NormRes::Term(arg),
              ]
            )
          )
        }

        Some(
          NormRes::App(typ, Op::Add, to_do)
        )
      }

    } else {
      panic!("illegal nullary application of `Sub`")
    }
  } ;

  // Integer division.
  fn idiv(args) {
    arity!("div" => args, 2) ;

    if args[1].is_zero() {
      panic!("division by zero, aborting...")

    } else if args[0].is_zero() {
      Some(
        NormRes::Term( term::int(0) )
      )

    } else if ! args[0].typ().is_arith() || ! args[1].typ().is_arith() {
      panic!(
        "illegal integer division application to {} ({}) and {} ({})",
        args[0], args[0].typ(), args[1], args[1].typ()
      )

    } else if let Ok(val) = Op::IDiv.eval(
      vec![args[0].as_val(), args[1].as_val()]
    ) {
      if val.typ().is_int() {
        if let Some(val) = val.to_term() {
          Some(
            NormRes::Term(val)
          )
        } else {
          None
        }
      } else {
        panic!(
          "unexpected result while evaluating `(div {} {})`",
          args[0], args[1]
        )
      }
    } else {
      None
    }
  } ;

  // Multiplication by a constant.
  fn cmul(args) {
    arity!("cmul" => args, 2) ;

    let (term, cst) = (
      args.pop().unwrap(), args.pop().unwrap()
    ) ;
    let typ = term.typ() ;

    let cst_val = if let Some(val) = cst.val() {
      val
    } else {
      return Some(
        NormRes::App(typ.clone(), Op::Mul, vec![ NormRes::Term(cst), NormRes::Term(term) ])
      )
      // panic!("illegal `cmul` application to {} {}", cst, term)
    } ;

    if let Some(val) = term.val() {
      let res = cst_val.mul(& val).unwrap_or_else(
        |_| panic!("illegal c_mul application: {} {}", cst, term)
      ).to_term().expect(
        "cannot be unknown"
      ) ;
      return Some( NormRes::Term(res) )
    } else if cst.is_one() {
      return Some( NormRes::Term(term) )
    } else if cst.is_zero() {
      return Some( NormRes::Term(cst) )
    }

    if let Some((op, args)) = term.app_inspect() {

      match op {

        Op::Add | Op::Mul | Op::Sub => return Some(
          NormRes::App(
            typ.clone(), op, args.iter().map(
              |arg| {
                NormRes::App(
                  typ.clone(), Op::CMul, vec![
                    NormRes::Term( cst.clone() ),
                    NormRes::Term( arg.clone() )
                  ]
                )
              }
            ).collect()
          )
        ),

        Op::CMul => if args.len() != 2 {
          panic!("illegal c_mul application to {} != 2 terms", args.len())
        } else {
          let cst_2 = args[0].val().expect(
            "illegal `cmul` application"
          ) ;
          let term = args[1].clone() ;

          let cst = cst_val.mul(& cst_2).expect(
            "illegal `cmul` application"
          ).to_term().expect("can't be unknown") ;

          return Some(
            NormRes::App(
              typ, op, vec![ NormRes::Term(cst), NormRes::Term(term) ]
            )
          )
        },

        Op::Ite => if args.len() != 3 {
          panic!("illegal ite application: {}", term)
        } else if args[0].dtyp_tst_inspect().is_none() {
          let (c, t, e) = (
            args[0].clone(),
            args[1].clone(),
            args[2].clone(),
          ) ;
          return Some(
            NormRes::App(
              typ.clone(), op, vec![
                NormRes::Term(c),
                NormRes::App(
                  typ.clone(), Op::CMul, vec![
                    NormRes::Term(cst.clone()),
                    NormRes::Term(t),
                  ]
                ),
                NormRes::App(
                  typ, Op::CMul, vec![
                    NormRes::Term(cst),
                    NormRes::Term(e),
                  ]
                )
              ]
            )
          )
        },

        Op::IDiv | Op::Div | Op::Rem | Op::Mod |
        Op::ToInt | Op::ToReal | Op::Store | Op::Select => (),

        Op::Gt | Op::Ge | Op::Le | Op::Lt | Op::Eql | Op::Distinct |
        Op::Impl | Op::Not | Op::And | Op::Or => panic!(
          "illegal c_mul application {}", term
        ),
      }
    }

    debug_assert! { args.is_empty() }
    args.push(cst) ;
    args.push(term) ;
    None
  } ;

  // Multiplication.
  fn mul(args) {
    let typ = args[0].typ() ;
    let mut coef: Val = if typ.is_int() {
      val::int(1)
    } else {
      val::real( Rat::new(1.into(), 1.into()) )
    } ;

    let mut cnt = 0 ;
    while cnt < args.len() {
      if let Some(kids) = args[cnt].mul_inspect().cloned() {
        args.swap_remove(cnt) ;
        args.extend(kids)
      } else if let Some(i) = args[cnt].int_val().cloned() {
        args.swap_remove(cnt) ;
        coef = coef.mul( & val::int(i) ).expect(
          "during multiplication simplification"
        )
      } else if let Some(r) = args[cnt].real_val().cloned() {
        args.swap_remove(cnt) ;
        coef = coef.mul( & val::real(r) ).expect(
          "during multiplication simplification"
        )
      } else {
        cnt += 1
      }
    }

    if args.is_empty() {
      Some(
        NormRes::Term(
          coef.to_term().expect(
            "coefficient cannot be unknown"
          )
        )
      )

    } else if coef.is_one() {
      if args.len() == 1 {
        Some(
          NormRes::Term( args.pop().expect("mul1") )
        )
      } else {
        args.sort_unstable() ;
        None
      }

    } else {
      let coef = coef.to_term().expect(
        "coefficient cannot be unknown"
      ) ;
      if args.len() == 1 {
        Some(
          NormRes::App(
            typ, Op::CMul, vec![
              NormRes::Term(coef),
              NormRes::Term( args.pop().expect("mul2") )
            ]
          )
        )
      } else {
        Some(
          NormRes::App(
            typ.clone(), Op::Mul, args.drain(0 ..).map(
              |arg| NormRes::App(
                typ.clone(), Op::CMul, vec![
                  NormRes::Term( coef.clone() ),
                  NormRes::Term( arg )
                ]
              )
            ).collect()
          )
        )
      }
    }
  } ;

}

// Casting operations.

simpl_fun! {

  // Real to int.
  fn to_int(args) {
    arity!("to-int" => args, 1) ;

    if let Some(r) = args[0].real() {
      let i = r.to_integer() ;
      Some(
        NormRes::Term( term::int(i) )
      )
    } else {
      None
    }
  } ;

  // Int to real.
  fn to_real(args) {
    arity!("to-real" => args, 1) ;

    if let Some(i) = args[0].int() {
      Some(
        NormRes::Term(
          term::real( Rat::new(i, 1.into()) )
        )
      )
    } else {
      None
    }
  } ;

}

// Array operations.

simpl_fun! {

  // Store.
  fn store(args) {
    arity!("store" => args, 3) ;

    match (
      args[0].val(), args[1].val(), args[2].val()
    ) {
      (
        Some(array), Some(index), Some(value)
      ) => {
        let result = array.store(index, value).to_term().unwrap_or_else(
          || panic!(
            "illegal store application (store {} {} {})",
            args[0], args[1], args[0]
          )
        ) ;
        Some( NormRes::Term(result) )
      },
      _ => None,
    }
  } ;

  // Select.
  fn select(args) {
    arity!("select" => args, 2) ;

    match (
      args[0].val(), args[1].val()
    ) {
      ( Some(array), Some(index) ) => {
        let result = array.select(index).to_term().unwrap_or_else(
          || panic!(
            "illegal select application (select {} {})", args[0], args[1]
          )
        ) ;
        Some( NormRes::Term(result) )
      },
      _ => None,
    }
  } ;

}

/// Tries to create a constant datatype constructor.
fn cst_dtyp_new<S>(typ: Typ, name: S, args: Vec<Term>) -> Either<Val, (Typ, String, Vec<Term>)>
where
    S: Into<String>,
{
    let name = name.into();
    if args.is_empty() {
        return Either::Left(val::dtyp_new(typ, name, vec![]));
    }

    let mut nu_args = None;

    for arg in &args {
        if let Some(val) = arg.val() {
            nu_args
                .get_or_insert_with(|| Vec::with_capacity(args.len()))
                .push(val)
        } else {
            nu_args = None;
            break;
        }
    }

    if let Some(args) = nu_args {
        Either::Left(val::dtyp_new(typ, name, args))
    } else {
        Either::Right((typ, name, args))
    }
}

/// Simplifies a datatype constructor.
pub fn dtyp_new<S>(typ: Typ, name: S, args: Vec<Term>) -> RTerm
where
    S: Into<String>,
{
    let (typ, name, mut args) = match cst_dtyp_new(typ, name, args) {
        Either::Left(val) => return RTerm::Cst(val),
        Either::Right(stuff) => stuff,
    };

    if let Some((dtyp, prms)) = typ.dtyp_inspect() {
        if let Some(fargs) = dtyp.news.get(&name) {
            if args.len() != fargs.len() {
                panic!(
                    "constructor `{}` for `{}` expects {} arguments, found {}",
                    conf.emph(&name),
                    conf.emph(&dtyp.name),
                    fargs.len(),
                    args.len()
                )
            }

            for (arg, param) in args.iter_mut().zip(fargs.iter()) {
                let typ = param
                    .1
                    .to_type(prms)
                    .unwrap_or_else(|_| panic!("ill-formed datatype constructor: {}", typ));
                if let Some(typ) = typ.merge(&arg.typ()) {
                    if let Some(nu_arg) = arg.force_dtyp(typ) {
                        *arg = nu_arg
                    }
                }
            }
        } else {
            panic!(
                "datatype `{}` has no constructor named `{}`",
                conf.emph(&dtyp.name),
                conf.bad(&name)
            )
        }
    } else {
        panic!("ill-typed datatype constructor: {}", typ)
    }

    let mut vals = if args.is_empty() { Some(vec![]) } else { None };

    for arg in &args {
        if let Some(val) = arg.val() {
            vals.get_or_insert_with(|| Vec::with_capacity(args.len()))
                .push(val)
        } else {
            vals = None;
            break;
        }
    }

    if let Some(vals) = vals {
        debug_assert_eq! { vals.len(), args.len() }
        RTerm::Cst(val::dtyp_new(typ, name, vals))
    } else {
        debug_assert!(!args.is_empty());
        RTerm::new_dtyp_new(typ, name, args)
    }
}

/// Simplifies a datatype selector.
pub fn dtyp_slc<S>(typ: Typ, field: S, term: Term) -> Either<RTerm, Term>
where
    S: Into<String>,
{
    let field = field.into();
    if let Some(val) = term.val() {
        if let Some(res) = val.dtyp_slc(&field) {
            return Either::Left(RTerm::Cst(res));
        }
    }

    if let Some((typ, constructor, args)) = term.dtyp_new_inspect() {
        if let Some((dtyp, _)) = typ.dtyp_inspect() {
            if let Some(params) = dtyp.news.get(constructor) {
                debug_assert_eq! { args.len(), params.len() }
                for ((fld, _), arg) in params.iter().zip(args.iter()) {
                    if fld == &field {
                        return Either::Right(arg.clone());
                    }
                }
            } else {
                panic!("inconsistent internal datatype term")
            }
        } else {
            panic!("inconsistent application of datatype selector")
        }
    }

    Either::Left(RTerm::new_dtyp_slc(typ, field, term))
}

/// Simplifies a datatype tester.
///
/// The boolean flag returned indicates the polarity of the result. That is, if
/// it is `false` then the term should be negated.
pub fn dtyp_tst<S>(constructor: S, term: Term) -> (RTerm, bool)
where
    S: Into<String>,
{
    let constructor = constructor.into();
    if let Some(val) = term.val() {
        if let val::RVal::DTypNew { name, .. } = val.get() {
            return (RTerm::Cst(val::bool(&constructor == name)), true);
        } else {
            panic!("illegal datatype tester (ill-typed)")
        }
    } else if let Some((_, name, _)) = term.dtyp_new_inspect() {
        return (RTerm::Cst(val::bool(constructor == name)), true);
    }

    // The following tries to find a constructor that's more complex than the
    // current one. The reason is that so far, it seems to work better that way.
    if let Some(dtyp) = dtyp::of_constructor(&constructor) {
        if let Some(args) = dtyp.news.get(&constructor) {
            if args.is_empty() {
                if let Some(constructor) = dtyp.rec_constructor() {
                    return (RTerm::new_dtyp_tst(typ::bool(), constructor, term), false);
                }
            }
        } else {
            panic!("inconsistent maps for datatypes")
        }
    } else {
        panic!(
            "trying to construct a tester for unknown constructor {}",
            constructor
        )
    }

    (RTerm::new_dtyp_tst(typ::bool(), constructor, term), true)
}
