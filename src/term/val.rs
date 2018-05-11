//! Values used in evaluation.
//!
//! Values can be automatically created (using `into`) to
//!
//! - `Val::B` from `bool`
//! - `Val::I` from `Int`, `usize`, `isize`, `u32`, `i32`, `u64`, `i64`
//! - `Val::N` from `()`

use hashconsing::{ HashConsign, HConser, HConsed } ;

use common::{ Int, Rat, Signed } ;

use common::* ;

/// Type of the term factory.
type Factory = RwLock< HashConsign<RVal> > ;

lazy_static! {
  /// Term factory.
  static ref factory: Factory = RwLock::new(
    HashConsign::with_capacity( conf.instance.term_capa )
  ) ;
}

/// A hash-consed type.
pub type Val = HConsed<RVal> ;

/// Creates a value.
pub fn mk<V: Into<RVal>>(val: V) -> Val {
  factory.mk(val.into())
}

/// Creates a boolean value.
pub fn bool(b: bool) -> Val {
  factory.mk(RVal::B(b))
}
/// Creates an integer value.
pub fn int<I: Into<Int>>(i: I) -> Val {
  factory.mk(RVal::I(i.into()))
}
/// Creates a rational value.
pub fn rat<R: Into<Rat>>(r: R) -> Val {
  factory.mk(RVal::R(r.into()))
}
/// Creates a non-value for a type.
pub fn none(typ: Typ) -> Val {
  factory.mk(RVal::N(typ))
}



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
pub enum RVal {
  /// Boolean value.
  B(bool),
  /// Integer value.
  I(Int),
  /// Real value (actually a rational).
  R(Rat),
  // /// An array.
  // Array(Vec<Val>),
  /// No value (context was incomplete).
  N(Typ),
}

lazy_static! {
  /// Bool type.
  static ref bool_ty: Typ = typ::bool() ;
  /// Int type.
  static ref int_ty: Typ = typ::int() ;
  /// Real type.
  static ref real_ty: Typ = typ::real() ;
}

impl RVal {
  /// Returns the type of the value.
  pub fn typ(& self) -> & Typ {
    use self::RVal::* ;
    match * self {
      B(_) => & * bool_ty,
      I(_) => & * int_ty,
      R(_) => & * real_ty,
      N(ref typ) => typ
    }
  }
}

impl Into<Val> for RVal {
  fn into(self) -> Val {
    factory.mk(self)
  }
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
///     - one is boolean and another one is `Val::N`.
macro_rules! bin_op {
  (arith $lft:expr, $op:tt, $rgt:expr) => ({
    use num::One ;
    match $lft {

      RVal::N(ref typ) if typ.is_int() => match $rgt {

        RVal::I(_) => Ok(none(typ::int())),
        RVal::R(_) => Ok(none(typ::real())),

        RVal::N(ref t_2) if t_2.is_arith() => Ok(none(t_2.clone())),

        ref rgt => bail!(
          "expected arith value ({}), found {} of type {}", typ, rgt, rgt.typ()
        ),
      },

      RVal::N(ref typ) if typ.is_real() => match $rgt {

        RVal::I(_) => Ok(none(typ::real())),

        RVal::R(_) => Ok(none(typ::real())),

        RVal::N(ref t_2) if t_2.is_arith() => Ok(none(typ.clone())),

        ref rgt => bail!(
          "expected arith value, found {} of type {}", rgt, rgt.typ()
        ),
      },

      RVal::I(ref lft) => match $rgt {
        RVal::N(ref typ) if typ.is_arith() => Ok(none(typ.clone())),
        RVal::I(ref rgt) => Ok( int(lft $op rgt) ),
        RVal::R(ref rgt) => Ok(
          rat(Rat::new(lft.clone(), Int::one()) $op rgt)
        ),
        ref rgt => bail!(
          "expected compatible arith values, \
          found {} (Int) and {}", lft, rgt
        ),
      }

      RVal::R(ref lft) => match $rgt {
        RVal::N(ref typ) if typ.is_arith() => Ok(none(typ::real())),
        RVal::R(ref rgt) => Ok( rat(lft $op rgt) ),
        RVal::I(ref rgt) => Ok(
          rat(lft $op Rat::new(rgt.clone(), Int::one()))
        ),
        ref rgt => bail!(
          "expected compatible arith values, \
          found {} (Real) and {} ({})",
          lft, rgt, rgt.typ()
        ),
      }
      ref lft => bail!(
        "expected compatible arith values, found {} and {}", lft, $rgt
      ),
    }
  }) ;
  (bool $lft:tt $op:tt $rgt:expr) => (
    match ($lft, $rgt) {
      (RVal::N(ref typ), _) |
      (_, RVal::N(ref typ))
      if typ.is_bool() => Ok(none(typ.clone())),

      (RVal::B(b_1), & RVal::B(b_2)) => Ok(
        RVal::B(b_1 $op b_2)
      ),

      (lft, rgt) => bail!(
        "expected boolean values, found {} ({}) and {} ({})",
        lft, lft.typ(), rgt, rgt.typ()
      )
    }
  ) ;
}
/// Applies a binary relation on two arithmetic, compatible values.
///
/// Only works if the two values are either the same arithmetic kind of
/// `Val`, or both are `RVal::N`, or one is arithmetic and another one is
/// `RVal::N`.
macro_rules! arith_bin_rel {
  ($lft:expr, $op:tt, $rgt:expr) => ({
    use num::One ;
    match $lft {

      RVal::N(ref typ) if typ.is_arith() => Ok(none(typ::bool())),

      RVal::I(ref lft) => match $rgt {
        RVal::N(ref typ) if typ.is_arith() => Ok(none(typ::bool())),
        RVal::I(ref rgt) => Ok( bool(lft.$op(rgt)) ),
        RVal::R(ref rgt) => Ok(
          bool( Rat::new(lft.clone(), Int::one()).$op(rgt) )
        ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      },

      RVal::R(ref lft) => match $rgt {
        RVal::N(ref typ) if typ.is_arith() => Ok(none(typ::bool())),
        RVal::R(ref rgt) => Ok( bool(lft.$op(rgt)) ),
        RVal::I(ref rgt) => Ok(
          bool( lft.$op( & Rat::new(rgt.clone(), Int::one()) ) )
        ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      },

      ref lft => bail!(
        "expected arith values, found {} and {}", lft, $rgt
      ),
    }
  }) ;
}

impl RVal {
  /// Returns true iff the value is not `RVal::N`.
  #[inline]
  pub fn is_known(& self) -> bool {
    match * self {
      RVal::N(_) => false,
      _ => true,
    }
  }

  /// Attempts to cast a value.
  pub fn cast(& self, typ: & ::term::Typ) -> Res<Val> {
    use num::One ;
    use term::typ::RTyp ;
    match (self, typ.get()) {
      (& RVal::I(ref i), & RTyp::Int) => Ok( int(i.clone()) ),
      (& RVal::I(ref num), & RTyp::Real) => Ok(
        rat( Rat::new(num.clone(), Int::one()) )
      ),

      (& RVal::R(ref r), & RTyp::Real) => Ok( rat(r.clone()) ),

      (& RVal::B(b), & RTyp::Bool) => Ok(
        bool(b)
      ),

      // This is a bit lax as it allows to cast a non-value of any type to a
      // non-value of any other type...
      (& RVal::N(_), _) => Ok(none(typ.clone())),

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

  /// Checks if two values are the semantically equal.
  ///
  /// Different from partial eq! Here, `N` is not equal to `N`.
  pub fn equal_int(& self, other: & Int) -> bool {
    if self.is_known() {
      if let RVal::I(ref i) = * self {
        i == other
      } else {
        false
      }
    } else {
      false
    }
  }

  /// Checks if two values are the semantically equal.
  ///
  /// Different from partial eq! Here, `N` is not equal to `N`.
  pub fn equal_rat(& self, other: & Rat) -> bool {
    if self.is_known() {
      if let RVal::R(ref r) = * self {
        r == other
      } else {
        false
      }
    } else {
      false
    }
  }

  /// Checks if two values are the semantically equal.
  ///
  /// Different from partial eq! Here, `N` is not equal to `N`.
  pub fn equal_val(& self, other: & Val) -> bool {
    if self.is_known() && other.get().is_known() {
      self == other.get()
    } else {
      false
    }
  }

  /// Extracts a boolean value.
  pub fn to_bool(& self) -> Res<Option<bool>> {
    match self {
      & RVal::B(b) => Ok( Some(b) ),
      & RVal::I(_) => bail!("expected boolean value, found integer"),
      & RVal::R(_) => bail!("expected boolean value, found real"),
      & RVal::N(ref typ) if typ.is_bool() => Ok(None),
      & RVal::N(ref typ) => bail!(
        "expected boolean value, got non-value of type {}", typ
      ),
    }
  }

  /// Extracts an integer value.
  pub fn to_int(& self) -> Res<Option<Int>> {
    use num::One ;
    match self {
      & RVal::I(ref i) => Ok( Some(i.clone()) ),
      & RVal::R(ref r) => if r.denom().abs() == Int::one() {
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
      & RVal::B(_) => bail!("expected integer value, found boolean"),
      & RVal::N(ref typ) if typ == & typ::int() => Ok(None),
      & RVal::N(ref typ) => bail!(
        "expected integer value, got no-value of type {}", typ
      ),
    }
  }
  /// Extracts a real value.
  pub fn to_real(& self) -> Res<Option<Rat>> {
    use num::One ;
    match self {
      & RVal::R(ref r) => Ok( Some(r.clone()) ),
      & RVal::I(ref i) => Ok( Some( Rat::new(i.clone(), Int::one()) ) ),
      & RVal::B(_) => bail!("expected rational value, found boolean"),
      & RVal::N(ref typ) if typ == & typ::real() => Ok(None),
      & RVal::N(ref typ) => bail!(
        "expected real value, got no-value of type {}", typ
      ),
    }
  }

  /// True if the two values have the same type, or if one of them is unknown.
  pub fn same_type(& self, other: & Self) -> bool {
    match (self, other) {
      (& RVal::B(_), & RVal::B(_)) |
      (& RVal::I(_), & RVal::I(_)) |
      (& RVal::R(_), & RVal::R(_)) |
      (& RVal::R(_), & RVal::I(_)) |
      (& RVal::I(_), & RVal::R(_)) => true,
      (& RVal::N(ref t_1), & RVal::N(ref t_2)) if t_1 == t_2 => true,
      _ => false,
    }
  }

  /// Checks if the value is zero (integer or rational).
  pub fn is_zero(& self) -> bool {
    use num::Zero ;
    match * self {
      RVal::I(ref i) => i.is_zero(),
      RVal::R(ref r) => r.is_zero(),
      RVal::B(_) |
      RVal::N(_) => false,
    }
  }

  /// Checks if the value is one (integer or rational).
  pub fn is_one(& self) -> bool {
    use num::One ;
    match * self {
      RVal::I(ref i) => i == & Int::one(),
      RVal::R(ref r) => r == & Rat::one(),
      RVal::B(_) |
      RVal::N(_) => false,
    }
  }

  /// Checks if the value is minus one (integer or rational).
  pub fn is_minus_one(& self) -> bool {
    use num::One ;
    match * self {
      RVal::I(ref i) => i == & - Int::one(),
      RVal::R(ref r) => r == & - Rat::one(),
      RVal::B(_) |
      RVal::N(_) => false,
    }
  }

  /// Transforms a value into a term.
  pub fn to_term(& self) -> Option<::term::Term> {
    match * self {
      RVal::I(ref i) => Some( ::term::int(i.clone()) ),
      RVal::R(ref r) => Some( ::term::real(r.clone()) ),
      RVal::B(b) => Some( ::term::bool(b) ),
      RVal::N(_) => None,
    }
  }

  /// Conjunction.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::{ val, typ } ;
  /// let (mut lft, mut rgt) = (val::mk(true), val::mk(false)) ;
  /// let res = lft.and(& rgt).unwrap() ;
  /// # println!("{} && {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(false) }
  /// lft = val::none( typ::bool() ) ;
  /// let res = lft.and(& rgt).unwrap() ;
  /// # println!("{} && {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(false) }
  /// rgt = val::mk(true) ;
  /// let res = lft.and(& rgt).unwrap() ;
  /// # println!("{} && {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::none( typ::bool() ) }
  /// lft = val::mk(true) ;
  /// let res = lft.and(& rgt).unwrap() ;
  /// # println!("{} && {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk(7) ;
  /// let res = lft.and(& rgt) ;
  /// # println!("{} && {} = {:?}", lft, rgt, res) ;
  /// assert!{ res.is_err() }
  /// ```
  pub fn and(& self, other: & Val) -> Res<Val> {
    match (self, other.get()) {
      (& RVal::B(false), _) |
      (_, & RVal::B(false)) => Ok(bool(false)),
      (& RVal::B(b_1), & RVal::B(b_2)) => Ok(
        bool(b_1 && b_2)
      ),

      (& RVal::N(_), & RVal::B(_)) |
      (& RVal::B(_), & RVal::N(_)) |
      (& RVal::N(_), & RVal::N(_)) => Ok(none(typ::bool())),

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
  /// use hoice::term::{ val, typ } ;
  /// let (mut lft, mut rgt) = (val::mk(false), val::mk(true)) ;
  /// let res = lft.or(& rgt).unwrap() ;
  /// # println!("{} || {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// lft = val::none( typ::bool() ) ;
  /// let res = lft.or(& rgt).unwrap() ;
  /// # println!("{} || {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk(false) ;
  /// let res = lft.or(& rgt).unwrap() ;
  /// # println!("{} || {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::none( typ::bool() ) }
  /// lft = val::mk(false) ;
  /// let res = lft.or(& rgt).unwrap() ;
  /// # println!("{} || {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(false) }
  /// rgt = val::mk(7) ;
  /// let res = lft.or(& rgt) ;
  /// # println!("{} || {} = {:?}", lft, rgt, res) ;
  /// assert!{ res.is_err() }
  /// ```
  pub fn or(& self, other: & Val) -> Res<Val> {
    match (self, other.get()) {
      (& RVal::B(true), _) |
      (_, & RVal::B(true)) => Ok(bool(true)),
      (& RVal::B(b_1), & RVal::B(b_2)) => Ok(
        bool(b_1 || b_2)
      ),

      (& RVal::N(_), & RVal::B(_)) |
      (& RVal::B(_), & RVal::N(_)) |
      (& RVal::N(_), & RVal::N(_)) => Ok(none(typ::bool())),

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
  /// use hoice::term::{ val, typ } ;
  /// let mut buru = val::mk(true) ;
  /// let res = buru.not().unwrap() ;
  /// # println!("not {} = {}", buru, res) ;
  /// assert_eq!{ res, val::mk(false) }
  /// buru = val::mk(false) ;
  /// let res = buru.not().unwrap() ;
  /// # println!("not {} = {}", buru, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// buru = val::none( typ::bool() ) ;
  /// let res = buru.not().unwrap() ;
  /// # println!("not {} = {}", buru, res) ;
  /// assert_eq!{ res, buru }
  /// buru = val::mk(7) ;
  /// let res = buru.not() ;
  /// # println!("not {} = {:?}", buru, res) ;
  /// assert!{ res.is_err() }
  /// ```
  pub fn not(& self) -> Res<Val> {
    match * self {
      RVal::B(b) => Ok( bool(! b) ),
      RVal::N(ref typ) if typ.is_bool() => Ok(none(typ.clone())),
      RVal::N(ref typ) => bail!(
        "expected boolean value, found non-value of type {}", typ
      ),
      RVal::I(_) => bail!("expected boolean value, found integer"),
      RVal::R(_) => bail!("expected boolean value, found real"),
    }
  }

  /// Adds two values.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::{ val, typ } ;
  /// let (mut lft, mut rgt) = (val::mk(35), val::mk(7)) ;
  /// let res = lft.add(& rgt).unwrap() ;
  /// # println!("{} + {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(42) }
  /// lft = val::none( typ::int() ) ;
  /// let res = lft.add(& rgt).unwrap() ;
  /// # println!("{} + {} = {}", lft, rgt, res) ;
  /// assert!{ ! res.is_known() }
  /// rgt = val::mk(false) ;
  /// let res = lft.add(& rgt) ;
  /// # println!("{} + {} = {:?}", lft, rgt, res) ;
  /// assert!{ res.is_err() }
  /// ```
  pub fn add(& self, other: & Val) -> Res<Val> {
    bin_op! { arith * self, +, * other.get() }
  }
  /// Subtracts two values.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::{ val, typ } ;
  /// let (mut lft, mut rgt) = (val::mk(49), val::mk(7)) ;
  /// # println!("{} - {} = {}", lft, rgt, lft.sub(& rgt).unwrap()) ;
  /// assert_eq!{ lft.sub(& rgt).unwrap(), val::mk(42) }
  /// lft = val::none( typ::int() ) ;
  /// # println!("{} - {} = {}", lft, rgt, lft.sub(& rgt).unwrap()) ;
  /// assert_eq!{ lft.sub(& rgt).unwrap(), val::none( typ::int() ) }
  /// rgt = val::mk(false) ;
  /// # println!("{} - {} = {:?}", lft, rgt, lft.sub(& rgt)) ;
  /// assert!{ lft.sub(& rgt).is_err() }
  /// ```
  pub fn sub(& self, other: & Val) -> Res<Val> {
    bin_op! { arith * self, -, * other.get() }
  }
  /// Multiplies two values.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::{ val, typ } ;
  /// let (mut lft, mut rgt) = (val::mk(6), val::mk(7)) ;
  /// let res = lft.mul(& rgt).unwrap() ;
  /// # println!("{} * {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(42) }
  /// lft = val::none(typ::int()) ;
  /// let res = lft.mul(& rgt).unwrap() ;
  /// # println!("{} * {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, lft }
  /// rgt = val::mk(0) ;
  /// let res = lft.mul(& rgt).unwrap() ;
  /// # println!("{} * {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(0) }
  /// rgt = val::mk((0, 1)) ;
  /// let res = lft.mul(& rgt).unwrap() ;
  /// # println!("{} * {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk((0, 1)) }
  /// lft = val::mk(7) ;
  /// let res = lft.mul(& rgt).unwrap() ;
  /// # println!("{} * {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk((0, 1)) }
  /// lft = val::mk(false) ;
  /// let res = lft.mul(& rgt) ;
  /// # println!("{} * {} = {:?}", lft, rgt, res) ;
  /// assert!{ res.is_err() }
  /// ```
  pub fn mul(& self, other: & Val) -> Res<Val> {
    use num::Zero ;
    match * self {

      RVal::N(ref typ) if typ.is_int() => match * other.get() {
        RVal::I(ref i) if i.is_zero() => Ok( int(0) ),
        RVal::R(ref r) if r.is_zero() => Ok( mk((0, 1)) ),
        RVal::N(ref t_2) if t_2.is_arith() => Ok(none(t_2.clone())),
        RVal::I(_) => Ok(none(typ.clone())),
        RVal::R(_) => Ok(none(typ::real())),
        ref rgt => bail!(
          "expected arith values, found {} and {}", "_", rgt
        ),
      },

      RVal::N(ref typ) if typ.is_real() => match * other.get() {
        RVal::I(ref i) if i.is_zero() => Ok( mk((0, 1)) ),
        RVal::R(ref r) if r.is_zero() => Ok( mk((0, 1)) ),
        RVal::N(ref t_2) if t_2.is_arith() => Ok(none(t_2.clone())),
        RVal::I(_) => Ok(none(typ.clone())),
        RVal::R(_) => Ok(none(typ::real())),
        ref rgt => bail!(
          "expected arith values, found {} and {}", "_", rgt
        ),
      },

      RVal::I(ref lft) => match * other.get() {
        RVal::N(ref typ) if typ.is_arith() => match (
          typ.is_int(), lft.is_zero()
        ) {
          (_, false) => Ok( none(typ.clone()) ),
          (true, true) => Ok( int(0) ),
          (false, true) => Ok( rat( Rat::new(0.into(), 0.into())) ),
        },
        RVal::I(ref rgt) => Ok( int(lft * rgt) ),
        RVal::R(ref rgt) => Ok(
          rat( Rat::new(lft * rgt.numer(), rgt.denom().clone()) )
        ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      }

      RVal::R(ref lft) => match other.to_real() ? {
        None => if lft.is_zero() {
          Ok( rat( Rat::new(0.into(), 1.into()) ) )
        } else {
          Ok( none(typ::real()) )
        },
        Some(rgt) => Ok( rat(lft * rgt) ),
      }
      ref lft => bail!(
        "expected arith values, found {} and {}", lft, other
      ),
    }
  }

  /// Unary minus.
  pub fn minus(& self) -> Res<Val> {
    match * self {
      RVal::I(ref i) => Ok( int(- i) ),
      RVal::R(ref r) => Ok( rat(- r) ),
      RVal::N(ref typ) if typ.is_arith() => Ok( none(typ.clone()) ),
      _ => bail!(
        "expected arith value, found {} ({})", self, self.typ()
      ),
    }
  }

  /// Greater than.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::{ val, typ } ;
  /// let (mut lft, mut rgt) = (val::mk(3), val::mk(42)) ;
  /// let res = lft.g_t(& rgt).unwrap() ;
  /// # println!("{} > {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(false) }
  /// lft = val::none( typ::int() ) ;
  /// let res = lft.g_t(& rgt).unwrap() ;
  /// # println!("{} > {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::none( typ::bool() ) }
  /// lft = val::mk(103) ;
  /// let res = lft.g_t(& rgt).unwrap() ;
  /// # println!("{} > {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// lft = val::mk((103,1)) ;
  /// let res = lft.g_t(& rgt).unwrap() ;
  /// # println!("{} > {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk((42,1)) ;
  /// let res = lft.g_t(& rgt).unwrap() ;
  /// # println!("{} > {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk(false) ;
  /// let res = lft.g_t(& rgt) ;
  /// # println!("{} > {} = {:?}", lft, rgt, res) ;
  /// assert!{ res.is_err() }
  /// ```
  pub fn g_t(& self, other: & Val) -> Res<Val> {
    #[allow(unused_parens)]
    arith_bin_rel! { * self, gt, * other.get() }
  }

  /// Greater than or equal to.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::{ val, typ } ;
  /// let (mut lft, mut rgt) = (val::mk(3), val::mk(42)) ;
  /// let res = lft.g_e(& rgt).unwrap() ;
  /// # println!("{} >= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(false) }
  /// lft = val::none( typ::int() ) ;
  /// let res = lft.g_e(& rgt).unwrap() ;
  /// # println!("{} >= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::none( typ::bool() ) }
  /// lft = val::mk(42) ;
  /// let res = lft.g_e(& rgt).unwrap() ;
  /// # println!("{} >= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// lft = val::mk((42,1)) ;
  /// let res = lft.g_e(& rgt).unwrap() ;
  /// # println!("{} >= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk((42,1)) ;
  /// let res = lft.g_e(& rgt).unwrap() ;
  /// # println!("{} >= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk(false) ;
  /// let res = lft.g_e(& rgt) ;
  /// # println!("{} >= {} = {:?}", lft, rgt, res) ;
  /// assert!{ res.is_err() }
  /// ```
  pub fn g_e(& self, other: & Val) -> Res<Val> {
    arith_bin_rel! { * self, ge, * other.get() }
  }

  /// Less than or equal to.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::{ val, typ } ;
  /// let (mut lft, mut rgt) = (val::mk(42), val::mk(3)) ;
  /// let res = lft.l_e(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(false) }
  /// lft = val::none( typ::int() ) ;
  /// let res = lft.l_e(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::none( typ::bool() ) }
  /// lft = val::mk(3) ;
  /// let res = lft.l_e(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// lft = val::mk((3,1)) ;
  /// let res = lft.l_e(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk((3,1)) ;
  /// let res = lft.l_e(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk(false) ;
  /// let res = lft.l_e(& rgt) ;
  /// # println!("{} <= {} = {:?}", lft, rgt, res) ;
  /// assert!{ res.is_err() }
  /// ```
  /// Less than or equal to.
  pub fn l_e(& self, other: & Val) -> Res<Val> {
    arith_bin_rel! { * self, le, * other.get() }
  }

  /// Less than.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::{ val, typ } ;
  /// let (mut lft, mut rgt) = (val::mk(42), val::mk(3)) ;
  /// let res = lft.l_t(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(false) }
  /// lft = val::none( typ::int() ) ;
  /// let res = lft.l_t(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::none( typ::bool() ) }
  /// lft = val::mk(2) ;
  /// let res = lft.l_t(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// lft = val::mk((2,1)) ;
  /// let res = lft.l_t(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk((42,1)) ;
  /// let res = lft.l_t(& rgt).unwrap() ;
  /// # println!("{} <= {} = {}", lft, rgt, res) ;
  /// assert_eq!{ res, val::mk(true) }
  /// rgt = val::mk(false) ;
  /// let res = lft.l_t(& rgt) ;
  /// # println!("{} <= {} = {:?}", lft, rgt, res) ;
  /// assert!{ res.is_err() }
  /// ```
  pub fn l_t(& self, other: & Val) -> Res<Val> {
    arith_bin_rel! { * self, lt, * other.get() }
  }

  /// Compares two values.
  pub fn cmp(& self, other: & Self) -> Option<::std::cmp::Ordering> {
    match (self, other) {
      (& RVal::I(ref l), & RVal::I(ref r)) => Some( l.cmp(r) ),
      (& RVal::R(ref l), & RVal::R(ref r)) => Some( l.cmp(r) ),
      (& RVal::B(ref l), & RVal::B(ref r)) => Some( l.cmp(r) ),
      _ => None,
    }
  }
}
impl_fmt!{
  RVal(self, fmt) {
    match * self {
      RVal::I(ref i) => int_to_smt!(fmt, i),
      RVal::R(ref r) => rat_to_smt!(fmt, r),
      RVal::B(b) => write!(fmt, "{}", b),
      RVal::N(ref t) => write!(fmt, "_[{}]", t),
    }
  }
}

impl From<bool> for RVal {
  fn from(b: bool) -> RVal {
    RVal::B(b)
  }
}
impl From<Int> for RVal {
  fn from(i: Int) -> RVal {
    RVal::I(i)
  }
}
impl From<Rat> for RVal {
  fn from(r: Rat) -> RVal {
    RVal::R(r)
  }
}
impl From<usize> for RVal {
  fn from(i: usize) -> RVal {
    RVal::I( i.into() )
  }
}
impl From<isize> for RVal {
  fn from(i: isize) -> RVal {
    RVal::I( i.into() )
  }
}
impl From<u32> for RVal {
  fn from(i: u32) -> RVal {
    RVal::I( i.into() )
  }
}
impl From<i32> for RVal {
  fn from(i: i32) -> RVal {
    RVal::I( i.into() )
  }
}
impl From<u64> for RVal {
  fn from(i: u64) -> RVal {
    RVal::I( i.into() )
  }
}
impl From<i64> for RVal {
  fn from(i: i64) -> RVal {
    RVal::I( i.into() )
  }
}
impl<Num, Den> From<(Num, Den)> for RVal
where Num: Into<Int>, Den: Into<Int> {
  fn from(rat: (Num, Den)) -> RVal {
    RVal::R( Rat::new( rat.0.into(), rat.1.into() ) )
  }
}
impl ::rsmt2::print::Expr2Smt<()> for RVal {
  fn expr_to_smt2<Writer: ::std::io::Write>(
    & self, w: & mut Writer, _: ()
  ) -> ::rsmt2::SmtRes<()> {
    write!(w, "{}", self) ? ;
    Ok(())
  }
}
