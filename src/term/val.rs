//! Values used in evaluation.
//!
//! Values can be automatically created (using `into`) to
//!
//! - `Val::B` from `bool`
//! - `Val::I` from `Int`, `usize`, `isize`, `u32`, `i32`, `u64`, `i64`
//! - `Val::N` from `()`

use errors::* ;
use common::{ Int, Rat, Signed } ;


/// Values.
///
/// Not that the `PartialEq` implementation is syntactic equality. In
/// particular, `Val::N == Val::N` which is not true semantically.
///
/// See [`equal`][equal] for semantic equality.
///
/// # TODO
///
/// - document partial eq and same_as
///
/// [equal]: #method.equal (equal method)
#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub enum Val {
  /// Boolean value.
  B(bool),
  /// Integer value.
  I(Int),
  /// Real value (actually a rational).
  R(Rat),
  /// No value (context was incomplete).
  N,
}

/// Applies a binary operation on two compatible values.
///
/// The first token specifies the mode:
/// 
/// - `arith`: only works if
///     - the two values are the same arithmetic kind of `Val`, or
///     - both are `Val::N`, or
///     - one is arithmetic and another one is `Val::N`.
/// - `bool`: only works if
///     - the two values are the same arithmetic kind `Val`, or
///     - both are `Val::N`, or
///     - one is arithmetic and another one is `Val::N`.
macro_rules! bin_op {
  (arith $lft:tt $op:tt $rgt:expr) => ({
    use num::One ;
    match $lft {
      Val::N => match $rgt {
        Val::N | Val::I(_) | Val::R(_) => Ok(Val::N),
        ref rgt => bail!(
          "expected compatible arith values, found {} and {}", "_", rgt
        ),
      },
      Val::I(lft) => match $rgt {
        Val::N => Ok(Val::N),
        Val::I(ref rgt) => Ok( Val::I(lft $op rgt) ),
        Val::R(ref rgt) => Ok(
          Val::R(Rat::new(lft, Int::one()) $op rgt)
        ),
        ref rgt => bail!(
          "expected compatible arith values, found {} and {}", lft, rgt
        ),
      }
      Val::R(lft) => match $rgt {
        Val::N => Ok(Val::N),
        Val::R(ref rgt) => Ok( Val::R(lft $op rgt) ),
        Val::I(rgt) => Ok(
          Val::R(lft $op Rat::new(rgt, Int::one()))
        ),
        ref rgt => bail!(
          "expected compatible arith values, found {} and {}", lft, rgt
        ),
      }
      lft => bail!(
        "expected compatible arith values, found {} and {}", lft, $rgt
      ),
    }
  }) ;
  (bool $lft:tt $op:tt $rgt:expr) => (
    match ($lft, $rgt) {
      (Val::N, & Val::B(_)) |
      (Val::B(_), & Val::N) |
      (Val::N, & Val::N) => Ok(Val::N),

      (Val::B(b_1), & Val::B(b_2)) => Ok(
        Val::B(b_1 $op b_2)
      ),

      (lft, rgt) => bail!(
        "expected boolean values, found {} and {}", lft, rgt
      )
    }
  ) ;
}
/// Applies a binary relation on two arithmetic, compatible values.
///
/// Only works if the two values are either the same arithmetic kind of
/// `Val`, or both are `Val::N`, or one is arithmetic and another one is
/// `Val::N`.
macro_rules! arith_bin_rel {
  ($lft:tt $op:tt $rgt:expr) => ({
    use num::One ;
    match $lft {
      Val::N => match $rgt {
        Val::N | Val::I(_) | Val::R(_) => Ok(Val::N),
        ref rgt => bail!(
          "expected arith values, found {} and {}", "_", rgt
        ),
      },
      Val::I(lft) => match $rgt {
        Val::N => Ok(Val::N),
        Val::I(ref rgt) => Ok( Val::B(lft.$op(rgt)) ),
        Val::R(ref rgt) => Ok(
          Val::B( Rat::new(lft, Int::one()).$op(rgt) )
        ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      }
      Val::R(lft) => match $rgt {
        Val::N => Ok(Val::N),
        Val::R(ref rgt) => Ok( Val::B(lft.$op(rgt)) ),
        Val::I(rgt) => Ok(
          Val::B( lft.$op( & Rat::new(rgt, Int::one()) ) )
        ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      }
      lft => bail!(
        "expected arith values, found {} and {}", lft, $rgt
      ),
    }
  }) ;
}
impl Val {
  /// Returns true iff the value is not `Val::N`.
  #[inline]
  pub fn is_known(& self) -> bool {
    match * self {
      Val::N => false,
      _ => true,
    }
  }

  /// Attempts to cast a value.
  pub fn cast(self, typ: ::term::Typ) -> Res<Self> {
    use num::One ;
    use term::Typ ;
    match (self, typ) {
      (Val::I(i), Typ::Int) => Ok(
        Val::I(i)
      ),
      (Val::I(num), Typ::Real) => Ok(
        Val::R( (num, Int::one()).into() )
      ),

      (Val::R(r), Typ::Real) => Ok(
        Val::R(r)
      ),

      (Val::B(b), Typ::Bool) => Ok(
        Val::B(b)
      ),

      (Val::N, _) => Ok(Val::N),

      (val, typ) => bail!(
        "Cannot cast value {} to type {}", val, typ
      ),
    }
  }

  /// Checks if two values are the semantically equal.
  ///
  /// Different from partial eq! Here, `N` is not equal to `N`.
  pub fn equal(& self, other: & Self) -> bool {
    if self.is_known() && other.is_known() {
      self == other
    } else {
      false
    }
  }

  /// Extracts a boolean value.
  pub fn to_bool(self) -> Res<Option<bool>> {
    match self {
      Val::B(b) => Ok( Some(b) ),
      Val::I(_) => bail!("expected boolean value, found integer"),
      Val::R(_) => bail!("expected boolean value, found real"),
      Val::N => Ok(None),
    }
  }
  /// Extracts an integer value.
  pub fn to_int(self) -> Res<Option<Int>> {
    use num::One ;
    match self {
      Val::I(i) => Ok( Some(i) ),
      Val::R(r) => if r.denom().abs() == Int::one() {
        Ok(
          Some(
            if r.denom().is_negative() {
              - r.numer()
            } else {
              r.numer().clone()
            }
          )
        )
      } else {
        bail!("expected integer value, found rational {}", r)
      },
      Val::B(_) => bail!("expected integer value, found boolean"),
      Val::N => Ok(None),
    }
  }
  /// Extracts a real value.
  pub fn to_real(self) -> Res<Option<Rat>> {
    use num::One ;
    match self {
      Val::R(r) => Ok( Some(r) ),
      Val::I(i) => Ok( Some( Rat::new(i.clone(), Int::one()) ) ),
      Val::B(_) => bail!("expected rational value, found boolean"),
      Val::N => Ok(None),
    }
  }
  /// True if the two values have the same type, or if one of them is unknown.
  pub fn same_type(& self, other: & Self) -> bool {
    match (self, other) {
      (& Val::B(_), & Val::B(_)) |
      (& Val::I(_), & Val::I(_)) |
      (& Val::R(_), & Val::R(_)) |
      (& Val::R(_), & Val::I(_)) |
      (& Val::I(_), & Val::R(_)) => true,
      _ => false,
    }
  }

  /// Checks if the value is zero (integer or rational).
  pub fn is_zero(& self) -> bool {
    use num::Zero ;
    match * self {
      Val::I(ref i) => i.is_zero(),
      Val::R(ref r) => r.is_zero(),
      Val::B(_) |
      Val::N => false,
    }
  }

  /// Checks if the value is one (integer or rational).
  pub fn is_one(& self) -> bool {
    use num::One ;
    match * self {
      Val::I(ref i) => i == & Int::one(),
      Val::R(ref r) => r == & Rat::one(),
      Val::B(_) |
      Val::N => false,
    }
  }

  /// Checks if the value is minus one (integer or rational).
  pub fn is_minus_one(& self) -> bool {
    use num::One ;
    match * self {
      Val::I(ref i) => i == & - Int::one(),
      Val::R(ref r) => r == & - Rat::one(),
      Val::B(_) |
      Val::N => false,
    }
  }

  /// Transforms a value into a term.
  pub fn to_term(self) -> Option<::term::Term> {
    match self {
      Val::I(i) => Some( ::term::int(i) ),
      Val::R(r) => Some( ::term::real(r) ),
      Val::B(b) => Some( ::term::bool(b) ),
      Val::N => None,
    }
  }

  /// Conjunction.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let (mut lft, mut rgt): (Val, Val) = (true.into(), false.into()) ;
  /// # println!("{} && {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().and( rgt.clone() ).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} && {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().and( rgt.clone() ).unwrap(), false.into() }
  /// rgt = true.into() ;
  /// # println!("{} && {}", lft, rgt) ;
  /// assert!{ ! lft.clone().and( rgt.clone() ).unwrap().is_known() }
  /// lft = true.into() ;
  /// # println!("{} && {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().and( rgt.clone() ).unwrap(), true.into() }
  /// rgt = Val::I( 7.into() ) ;
  /// # println!("{} && {}", lft, rgt) ;
  /// assert!{ lft.clone().and( rgt.clone() ).is_err() }
  /// ```
  pub fn and(self, other: Self) -> Res<Self> {
    match (self, other) {
      (Val::B(false), _) |
      (_, Val::B(false)) => Ok(Val::B(false)),
      (Val::B(b_1), Val::B(b_2)) => Ok(
        Val::B(b_1 &b_2)
      ),

      (Val::N, Val::B(_)) |
      (Val::B(_), Val::N) |
      (Val::N, Val::N) => Ok(Val::N),

      (lft, rgt) => bail!(
        "expected boolean values, found {} and {}", lft, rgt
      )
    }
  }
  /// Disjunction.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let (mut lft, mut rgt): (Val, Val) = (false.into(), true.into()) ;
  /// # println!("{} || {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().or( rgt.clone() ).unwrap(), true.into() }
  /// lft = ().into() ;
  /// # println!("{} || {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().or( rgt.clone() ).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} || {}", lft, rgt) ;
  /// assert!{ ! lft.clone().or( rgt.clone() ).unwrap().is_known() }
  /// lft = false.into() ;
  /// # println!("{} || {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().or( rgt.clone() ).unwrap(), false.into() }
  /// rgt = Val::I( 7.into() ) ;
  /// # println!("{} || {}", lft, rgt) ;
  /// assert!{ lft.or( rgt.clone() ).is_err() }
  /// ```
  pub fn or(self, other: Self) -> Res<Self> {
    match (self, other) {
      (Val::B(true), _) |
      (_, Val::B(true)) => Ok(Val::B(true)),
      (Val::B(b_1), Val::B(b_2)) => Ok(
        Val::B(b_1 || b_2)
      ),

      (Val::N, Val::B(_)) |
      (Val::B(_), Val::N) |
      (Val::N, Val::N) => Ok(Val::N),

      (lft, rgt) => bail!(
        "expected boolean values, found {} and {}", lft, rgt
      )
    }
  }
  /// Negation.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let mut buru: Val = true.into() ;
  /// # println!("not {}", buru) ;
  /// assert_eq!{ buru.clone().not().unwrap(), false.into() }
  /// buru = false.into() ;
  /// # println!("not {}", buru) ;
  /// assert_eq!{ buru.clone().not().unwrap(), true.into() }
  /// buru = ().into() ;
  /// # println!("not {}", buru) ;
  /// assert!{ ! buru.clone().not().unwrap().is_known() }
  /// buru = 7.into() ;
  /// # println!("not {}", buru) ;
  /// assert!{ buru.not().is_err() }
  /// ```
  pub fn not(self) -> Res<Self> {
    match self {
      Val::B(b) => Ok( Val::B(! b) ),
      Val::N    => Ok(self),
      Val::I(_) => bail!("expected boolean value, found integer"),
      Val::R(_) => bail!("expected boolean value, found real"),
    }
  }

  /// Adds two values.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let (mut lft, mut rgt): (Val, Val) = (35.into(), 7.into()) ;
  /// let res = lft.clone().add( rgt.clone() ).unwrap() ;
  /// # println!("{} + {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, 42.into() }
  /// lft = ().into() ;
  /// let res = lft.clone().add( rgt.clone() ).unwrap() ;
  /// # println!("{} + {} = {}", lft, rgt, res) ;
  /// assert!{ ! res.is_known() }
  /// rgt = false.into() ;
  /// # println!("{} + {}", lft, rgt) ;
  /// assert!{ lft.add( rgt.clone() ).is_err() }
  /// ```
  pub fn add(self, other: Self) -> Res<Self> {
    bin_op! { arith self + other }
  }
  /// Subtracts two values.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let (mut lft, mut rgt): (Val, Val) = (49.into(), 7.into()) ;
  /// # println!("{} - {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().sub( rgt.clone() ).unwrap(), 42.into() }
  /// lft = ().into() ;
  /// # println!("{} - {}", lft, rgt) ;
  /// assert!{ ! lft.clone().sub( rgt.clone() ).unwrap().is_known() }
  /// rgt = false.into() ;
  /// # println!("{} - {}", lft, rgt) ;
  /// assert!{ lft.sub( rgt.clone() ).is_err() }
  /// ```
  pub fn sub(self, other: Self) -> Res<Self> {
    bin_op! { arith self - other }
  }
  /// Multiplies two values.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let (mut lft, mut rgt): (Val, Val) = (6.into(), 7.into()) ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().mul( rgt.clone() ).unwrap(), 42.into() }
  /// lft = ().into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert!{ ! lft.clone().mul( rgt.clone() ).unwrap().is_known() }
  /// rgt = 0.into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().mul( rgt.clone() ).unwrap(), 0.into() }
  /// rgt = (0, 1).into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().mul( rgt.clone() ).unwrap(), (0, 1).into() }
  /// lft = 7.into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().mul( rgt.clone() ).unwrap(), (0, 1).into() }
  /// lft = false.into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert!{ lft.mul( rgt.clone() ).is_err() }
  /// ```
  pub fn mul(self, other: Self) -> Res<Self> {
    use num::Zero ;
    match self {
      Val::N => match other {
        Val::I(ref i) if i.is_zero() => Ok( 0.into() ),
        Val::R(ref r) if r.is_zero() => Ok( (0, 1).into() ),
        Val::I(_) | Val::R(_) | Val::N => Ok(Val::N),
        ref rgt => bail!(
          "expected arith values, found {} and {}", "_", rgt
        ),
      },
      Val::I(lft) => match other {
        Val::N => if lft.is_zero() {
          Ok( 0.into() )
        } else {
          Ok(Val::N)
        },
        Val::I(ref rgt) => Ok( Val::I(lft * rgt) ),
        Val::R(ref rgt) => Ok(
          Val::R( Rat::new(lft * rgt.numer(), rgt.denom().clone()) )
        ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      }
      Val::R(lft) => match other.to_real() ? {
        None => if lft.is_zero() {
          Ok( (0, 1).into() )
        } else {
          Ok(Val::N)
        },
        Some(rgt) => Ok( Val::R(lft * rgt) ),
      }
      lft => bail!(
        "expected arith values, found {} and {}", lft, other
      ),
    }
  }
  /// Unary minus.
  pub fn minus(self) -> Res<Self> {
    match self {
      Val::I(i) => Ok( Val::I(- i) ),
      Val::R(r) => Ok( Val::R(- r) ),
      Val::N    => Ok(self),
      Val::B(_) => bail!("expected arith value, found boolean"),
    }
  }

  /// Greater than.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let (mut lft, mut rgt): (Val, Val) = (3.into(), 42.into()) ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().gt( rgt.clone() ).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert!{ ! lft.clone().gt( rgt.clone() ).unwrap().is_known() }
  /// lft = 103.into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().gt( rgt.clone() ).unwrap(), true.into() }
  /// lft = (103,1).into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().gt( rgt.clone() ).unwrap(), true.into() }
  /// rgt = (42,1).into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().gt( rgt.clone() ).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert!{ lft.gt( rgt.clone() ).is_err() }
  /// ```
  pub fn gt(self, other: Self) -> Res<Self> {
    arith_bin_rel! { self gt other }
  }
  /// Greater than or equal to.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let (mut lft, mut rgt): (Val, Val) = (3.into(), 42.into()) ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().ge( rgt.clone() ).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert!{ ! lft.clone().ge( rgt.clone() ).unwrap().is_known() }
  /// lft = 42.into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().ge( rgt.clone() ).unwrap(), true.into() }
  /// lft = (42,1).into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().ge( rgt.clone() ).unwrap(), true.into() }
  /// rgt = (42,1).into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().ge( rgt.clone() ).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert!{ lft.ge( rgt.clone() ).is_err() }
  /// ```
  pub fn ge(self, other: Self) -> Res<Self> {
    arith_bin_rel! { self ge other }
  }
  /// Greater than or equal to.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let (mut lft, mut rgt): (Val, Val) = (42.into(), 3.into()) ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le( rgt.clone() ).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert!{ ! lft.clone().le( rgt.clone() ).unwrap().is_known() }
  /// lft = 3.into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le( rgt.clone() ).unwrap(), true.into() }
  /// lft = (3,1).into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le( rgt.clone() ).unwrap(), true.into() }
  /// rgt = (3,1).into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le( rgt.clone() ).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert!{ lft.le( rgt.clone() ).is_err() }
  /// ```
  /// Less than or equal to.
  pub fn le(self, other: Self) -> Res<Self> {
    arith_bin_rel! { self le other }
  }
  /// Less than.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::Val ;
  /// let (mut lft, mut rgt): (Val, Val) = (42.into(), 3.into()) ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le( rgt.clone() ).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert!{ ! lft.clone().le( rgt.clone() ).unwrap().is_known() }
  /// lft = 2.into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le( rgt.clone() ).unwrap(), true.into() }
  /// lft = (2,1).into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le( rgt.clone() ).unwrap(), true.into() }
  /// rgt = (42,1).into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le( rgt.clone() ).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert!{ lft.le( rgt.clone() ).is_err() }
  /// ```
  pub fn lt(self, other: Self) -> Res<Self> {
    arith_bin_rel! { self lt other }
  }
}
impl_fmt!{
  Val(self, fmt) {
    match * self {
      Val::I(ref i) => int_to_smt!(fmt, i),
      Val::R(ref r) => rat_to_smt!(fmt, r),
      Val::B(b) => write!(fmt, "{}", b),
      Val::N => fmt.write_str("_"),
    }
  }
}
impl From<bool> for Val {
  fn from(b: bool) -> Val {
    Val::B(b)
  }
}
impl From<Int> for Val {
  fn from(i: Int) -> Val {
    Val::I(i)
  }
}
impl From<Rat> for Val {
  fn from(r: Rat) -> Val {
    Val::R(r)
  }
}
impl From<usize> for Val {
  fn from(i: usize) -> Val {
    Val::I( i.into() )
  }
}
impl From<isize> for Val {
  fn from(i: isize) -> Val {
    Val::I( i.into() )
  }
}
impl From<u32> for Val {
  fn from(i: u32) -> Val {
    Val::I( i.into() )
  }
}
impl From<i32> for Val {
  fn from(i: i32) -> Val {
    Val::I( i.into() )
  }
}
impl From<u64> for Val {
  fn from(i: u64) -> Val {
    Val::I( i.into() )
  }
}
impl From<i64> for Val {
  fn from(i: i64) -> Val {
    Val::I( i.into() )
  }
}
impl<Num, Den> From<(Num, Den)> for Val
where Num: Into<Int>, Den: Into<Int> {
  fn from(rat: (Num, Den)) -> Val {
    Val::R( Rat::new( rat.0.into(), rat.1.into() ) )
  }
}
impl From<()> for Val {
  fn from(_: ()) -> Val {
    Val::N
  }
}
impl ::rsmt2::print::Expr2Smt<()> for Val {
  fn expr_to_smt2<Writer: ::std::io::Write>(
    & self, w: & mut Writer, _: ()
  ) -> ::rsmt2::SmtRes<()> {
    write!(w, "{}", self) ? ;
    Ok(())
  }
}
