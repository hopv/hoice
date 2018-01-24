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
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
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
  (arith $lft:tt $op:tt $rgt:expr) => (
    match $lft {
      Val::N => match * $rgt {
        Val::N | Val::I(_) | Val::R(_) => Ok(Val::N),
        ref rgt => bail!(
          "expected compatible arith values, found {} and {}", "?", rgt
        ),
      },
      Val::I(lft) => match * $rgt {
        Val::N => Ok(Val::N),
        Val::I(ref rgt) => Ok( Val::I(lft $op rgt) ),
        ref rgt => bail!(
          "expected compatible arith values, found {} and {}", lft, rgt
        ),
      }
      Val::R(lft) => match * $rgt {
        Val::N => Ok(Val::N),
        Val::R(ref rgt) => Ok( Val::R(lft $op rgt) ),
        ref rgt => bail!(
          "expected compatible arith values, found {} and {}", lft, rgt
        ),
      }
      lft => bail!(
        "expected compatible arith values, found {} and {}", lft, $rgt
      ),
    }
  ) ;
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
  ($lft:tt $op:tt $rgt:expr) => (
    match $lft {
      Val::N => match * $rgt {
        Val::N | Val::I(_) | Val::R(_) => Ok(Val::N),
        ref rgt => bail!(
          "expected arith values, found {} and {}", "?", rgt
        ),
      },
      Val::I(lft) => match * $rgt {
        Val::N => Ok(Val::N),
        Val::I(ref rgt) => Ok( Val::B(lft.$op(rgt)) ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      }
      Val::R(lft) => match * $rgt {
        Val::N => Ok(Val::N),
        Val::R(ref rgt) => Ok( Val::B(lft.$op(rgt)) ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      }
      lft => bail!(
        "expected arith values, found {} and {}", lft, $rgt
      ),
    }
  ) ;
}
impl Val {
  /// Returns true iff the value is not `Val::N`.
  pub fn is_known(& self) -> bool {
    match * self {
      Val::N => true,
      _ => false,
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
    match self {
      Val::I(i) => Ok( Some(i) ),
      Val::B(_) => bail!("expected integer value, found boolean"),
      Val::R(_) => bail!("expected integer value, found rational"),
      Val::N => Ok(None),
    }
  }
  /// Extracts a real value.
  pub fn to_real(self) -> Res<Option<Rat>> {
    match self {
      Val::R(r) => Ok( Some(r) ),
      Val::B(_) => bail!("expected rational value, found boolean"),
      Val::I(_) => bail!("expected rational value, found integer"),
      Val::N => Ok(None),
    }
  }
  /// True if the two values have the same type, or if one of them is unknown.
  pub fn same_type(& self, other: & Self) -> bool {
    match (self, other) {
      (& Val::N, _) | (_, & Val::N) |
      (& Val::B(_), & Val::B(_)) | (& Val::I(_), & Val::I(_)) => true,
      _ => false,
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
  /// assert_eq!{ lft.clone().and(& rgt).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} && {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().and(& rgt).unwrap(), false.into() }
  /// rgt = true.into() ;
  /// # println!("{} && {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().and(& rgt).unwrap(), ().into() }
  /// lft = true.into() ;
  /// # println!("{} && {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().and(& rgt).unwrap(), true.into() }
  /// rgt = Val::I( 7.into() ) ;
  /// # println!("{} && {}", lft, rgt) ;
  /// assert!{ lft.clone().and(& rgt).is_err() }
  /// ```
  pub fn and(self, other: & Self) -> Res<Self> {
    match (self, other) {
      (Val::B(false), _) |
      (_, & Val::B(false)) => Ok(Val::B(false)),
      (Val::B(b_1), & Val::B(b_2)) => Ok(
        Val::B(b_1 && b_2)
      ),

      (Val::N, & Val::B(_)) |
      (Val::B(_), & Val::N) |
      (Val::N, & Val::N) => Ok(Val::N),

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
  /// assert_eq!{ lft.clone().or(& rgt).unwrap(), true.into() }
  /// lft = ().into() ;
  /// # println!("{} || {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().or(& rgt).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} || {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().or(& rgt).unwrap(), ().into() }
  /// lft = false.into() ;
  /// # println!("{} || {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().or(& rgt).unwrap(), false.into() }
  /// rgt = Val::I( 7.into() ) ;
  /// # println!("{} || {}", lft, rgt) ;
  /// assert!{ lft.or(& rgt).is_err() }
  /// ```
  pub fn or(self, other: & Self) -> Res<Self> {
    match (self, other) {
      (Val::B(true), _) |
      (_, & Val::B(true)) => Ok(Val::B(true)),
      (Val::B(b_1), & Val::B(b_2)) => Ok(
        Val::B(b_1 || b_2)
      ),

      (Val::N, & Val::B(_)) |
      (Val::B(_), & Val::N) |
      (Val::N, & Val::N) => Ok(Val::N),

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
  /// assert_eq!{ buru.clone().not().unwrap(), ().into() }
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
  /// # println!("{} + {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().add(& rgt).unwrap(), 42.into() }
  /// lft = ().into() ;
  /// # println!("{} + {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().add(& rgt).unwrap(), ().into() }
  /// rgt = false.into() ;
  /// # println!("{} + {}", lft, rgt) ;
  /// assert!{ lft.add(& rgt).is_err() }
  /// ```
  pub fn add(self, other: & Self) -> Res<Self> {
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
  /// assert_eq!{ lft.clone().sub(& rgt).unwrap(), 42.into() }
  /// lft = ().into() ;
  /// # println!("{} - {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().sub(& rgt).unwrap(), ().into() }
  /// rgt = false.into() ;
  /// # println!("{} - {}", lft, rgt) ;
  /// assert!{ lft.sub(& rgt).is_err() }
  /// ```
  pub fn sub(self, other: & Self) -> Res<Self> {
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
  /// assert_eq!{ lft.clone().mul(& rgt).unwrap(), 42.into() }
  /// lft = ().into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().mul(& rgt).unwrap(), ().into() }
  /// rgt = 0.into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().mul(& rgt).unwrap(), 0.into() }
  /// rgt = (0, 1).into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().mul(& rgt).unwrap(), (0, 1).into() }
  /// lft = 7.into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert!{ lft.clone().mul(& rgt).is_err() }
  /// lft = false.into() ;
  /// # println!("{} * {}", lft, rgt) ;
  /// assert!{ lft.mul(& rgt).is_err() }
  /// ```
  pub fn mul(self, other: & Self) -> Res<Self> {
    use num::Zero ;
    match self {
      Val::N => match * other {
        Val::I(ref i) if i.is_zero() => Ok( 0.into() ),
        Val::R(ref r) if r.is_zero() => Ok( (0, 1).into() ),
        Val::I(_) | Val::R(_) | Val::N => Ok(Val::N),
        ref rgt => bail!(
          "expected arith values, found {} and {}", "?", rgt
        ),
      },
      Val::I(lft) => match * other {
        Val::N => if lft.is_zero() {
          Ok( 0.into() )
        } else {
          Ok(Val::N)
        },
        Val::I(ref rgt) => Ok( Val::I(lft * rgt) ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      }
      Val::R(lft) => match * other {
        Val::N => if lft.is_zero() {
          Ok( (0, 1).into() )
        } else {
          Ok(Val::N)
        },
        Val::R(ref rgt) => Ok( Val::R(lft * rgt) ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
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
  /// assert_eq!{ lft.clone().gt(& rgt).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().gt(& rgt).unwrap(), ().into() }
  /// lft = 103.into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().gt(& rgt).unwrap(), true.into() }
  /// lft = (103,1).into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert!{ lft.clone().gt(& rgt).is_err() }
  /// rgt = (42,1).into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().gt(& rgt).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} > {}", lft, rgt) ;
  /// assert!{ lft.gt(& rgt).is_err() }
  /// ```
  pub fn gt(self, other: & Self) -> Res<Self> {
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
  /// assert_eq!{ lft.clone().ge(& rgt).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().ge(& rgt).unwrap(), ().into() }
  /// lft = 42.into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().ge(& rgt).unwrap(), true.into() }
  /// lft = (42,1).into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert!{ lft.clone().ge(& rgt).is_err() }
  /// rgt = (42,1).into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().ge(& rgt).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} >= {}", lft, rgt) ;
  /// assert!{ lft.ge(& rgt).is_err() }
  /// ```
  pub fn ge(self, other: & Self) -> Res<Self> {
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
  /// assert_eq!{ lft.clone().le(& rgt).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le(& rgt).unwrap(), ().into() }
  /// lft = 3.into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le(& rgt).unwrap(), true.into() }
  /// lft = (3,1).into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert!{ lft.clone().le(& rgt).is_err() }
  /// rgt = (3,1).into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le(& rgt).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert!{ lft.le(& rgt).is_err() }
  /// ```
  /// Less than or equal to.
  pub fn le(self, other: & Self) -> Res<Self> {
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
  /// assert_eq!{ lft.clone().le(& rgt).unwrap(), false.into() }
  /// lft = ().into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le(& rgt).unwrap(), ().into() }
  /// lft = 2.into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le(& rgt).unwrap(), true.into() }
  /// lft = (2,1).into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert!{ lft.clone().le(& rgt).is_err() }
  /// rgt = (42,1).into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert_eq!{ lft.clone().le(& rgt).unwrap(), true.into() }
  /// rgt = false.into() ;
  /// # println!("{} <= {}", lft, rgt) ;
  /// assert!{ lft.le(& rgt).is_err() }
  /// ```
  pub fn lt(self, other: & Self) -> Res<Self> {
    arith_bin_rel! { self lt other }
  }
}
impl_fmt!{
  Val(self, fmt) {
    match * self {
      Val::I(ref i) => int_to_smt!(fmt, i),
      Val::R(ref r) => rat_to_smt!(fmt, r),
      Val::B(b) => write!(fmt, "{}", b),
      Val::N => fmt.write_str("?"),
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
    Val::I( i.into() )
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