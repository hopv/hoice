//! Hashconsed concrete values.
//!
//! Values can be automatically created (using `into`) to
//!
//! - `Val::B` from `bool`
//! - `Val::I` from `Int`, `usize`, `isize`, `u32`, `i32`, `u64`, `i64`
//! - `Val::N` from `()`

use hashconsing::{ HashConsign, HConser, HConsed } ;

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

/// Creates an array with a default value.
///
/// - `idx_typ` is the type of **the indices** of the array.
pub fn array<Tgt: Into<Val>>(
  idx_typ: Typ, default: Tgt
) -> Val {
  let default = default.into() ;
  let default = if ! default.is_known() {
    default.typ().default_val()
  } else {
    default
  } ;
  factory.mk(
    RVal::Array {
      idx_typ,
      default: default,
      vals: Vec::new(),
    }
  )
}

/// Constructs an array from a function definition.
pub fn array_of_fun(idx_typ: Typ, term: & Term) -> Res<Val> {
  let mut vals: Vec<(Val, Val)> = vec![] ;

  let mut current = term ;

  loop {
    debug_assert_eq! { term.typ(), current.typ() }

    if let Some(val) = current.val() {
      debug_assert! {
        vals.iter().all(
          |(c, v)| c.typ() == idx_typ && v.typ() == val.typ()
        )
      }
      return Ok(
        mk( RVal::Array { idx_typ, default: val, vals } )
      )
    } else if let Some((c, t, e)) = current.ite_inspect() {
      if let Some(args) = c.eq_inspect() {
        debug_assert_eq! { args.len(), 2 }
        let cond = if let Some(var) = args[0].var_idx() {
          debug_assert_eq! { * var, 0 }
          args[1].clone()
        } else if let Some(var) = args[1].var_idx() {
          debug_assert_eq! { * var, 0 }
          args[0].clone()
        } else {
          if let Some((var, term)) = if term::vars(& args[1]).is_empty() {
            args[0].invert( args[1].clone() )
          } else if term::vars(& args[0]).is_empty() {
            args[1].invert( args[0].clone() )
          } else {
            break
          } {
            debug_assert_eq! { * var, 0 }
            term
          } else {
            break
          }
        } ;
        let cond = if let Some(val) = cond.val() {
          val
        } else {
          break
        } ;

        let val = if let Some(val) = t.val() {
          val
        } else {
          break
        } ;

        current = e ;
        vals.push((cond, val))

      } else {
        break
      }
    } else {
      break
    }
  }
  bail!("cannot extract array from term {}", term)
}

/// Creates an integer value.
pub fn int<I: Into<Int>>(i: I) -> Val {
  factory.mk(RVal::I(i.into()))
}
/// Creates a rational value.
pub fn real<R: Into<Rat>>(r: R) -> Val {
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
  /// No value.
  N(Typ),
  /// Boolean value.
  B(bool),
  /// Integer value.
  I(Int),
  /// Real value (actually a rational).
  R(Rat),
  /// An array is a total function.
  ///
  /// The `vals` field encodes a sequence of if-then-else's.
  Array {
    /// The type of **the indices** of the array.
    ///
    /// The actual type of the array is `array(idx_typ, default.typ())`.
    ///
    /// # Examples
    ///
    /// ```
    /// use hoice::common::* ;
    /// let array = val::array(
    ///   typ::int(), val::real( Rat::new(9.into(), 7.into()) )
    /// ) ;
    /// assert_eq! { array.typ(), typ::array( typ::int(), typ::real() ) }
    /// ```
    idx_typ: Typ,
    /// Default target value.
    default: Val,
    /// The values of the array.
    vals: Vec<(Val, Val)>
  },
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
          real(Rat::new(lft.clone(), Int::one()) $op rgt)
        ),
        ref rgt => bail!(
          "expected compatible arith values, \
          found {} (Int) and {}", lft, rgt
        ),
      }

      RVal::R(ref lft) => match $rgt {
        RVal::N(ref typ) if typ.is_arith() => Ok(none(typ::real())),
        RVal::R(ref rgt) => Ok( real(lft $op rgt) ),
        RVal::I(ref rgt) => Ok(
          real(lft $op Rat::new(rgt.clone(), Int::one()))
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

/// Operations legal for all values.
impl RVal {
  /// Returns true iff the value is not `RVal::N`.
  #[inline]
  pub fn is_known(& self) -> bool {
    match * self {
      RVal::N(_) => false,
      RVal::Array { ref default, ref vals, .. } => {
        default.is_known() && vals.iter().all(
          |(cond, val)| cond.is_known() && val.is_known()
        )
      },
      _ => true,
    }
  }

  /// Returns the type of the value.
  pub fn typ(& self) -> Typ {
    use self::RVal::* ;
    match * self {
      B(_) => typ::bool(),
      I(_) => typ::int(),
      R(_) => typ::real(),
      Array { ref idx_typ, ref default, .. } => typ::array(
        idx_typ.clone(), default.typ()
      ),
      N(ref typ) => typ.clone()
    }
  }

  /// Attempts to cast a value.
  pub fn cast(& self, typ: & ::term::Typ) -> Res<Val> {
    use num::One ;
    use term::typ::RTyp ;
    if & self.typ() == typ {
      return Ok( mk(self.clone()) )
    }

    match (self, typ.get()) {
      (& RVal::I(ref i), & RTyp::Int) => Ok( int(i.clone()) ),
      (& RVal::I(ref num), & RTyp::Real) => Ok(
        real( Rat::new(num.clone(), Int::one()) )
      ),

      (& RVal::R(ref r), & RTyp::Real) => Ok( real(r.clone()) ),

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
  pub fn equal_real(& self, other: & Rat) -> bool {
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
      & RVal::N(ref typ) if typ.is_bool() => Ok(None),
      & RVal::N(ref typ) => bail!(
        "expected boolean value, got non-value of type {}", typ
      ),
      _ => bail!(
        "expected boolean value, found value of type {}", self.typ()
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
      & RVal::N(ref typ) if typ == & typ::int() => Ok(None),
      & RVal::N(ref typ) => bail!(
        "expected integer value, got no-value of type {}", typ
      ),
      _ => bail!(
        "expected integer value, found value of type {}", self.typ()
      ),
    }
  }
  /// Extracts a real value.
  pub fn to_real(& self) -> Res<Option<Rat>> {
    use num::One ;
    match self {
      & RVal::R(ref r) => Ok( Some(r.clone()) ),
      & RVal::I(ref i) => Ok( Some( Rat::new(i.clone(), Int::one()) ) ),
      & RVal::N(ref typ) if typ == & typ::real() => Ok(None),
      & RVal::N(ref typ) => bail!(
        "expected real value, got no-value of type {}", typ
      ),
      _ => bail!(
        "expected rational value, found value of type {}", self.typ()
      ),
    }
  }

  /// True if the two values have the same type.
  pub fn same_type(& self, other: & Self) -> bool {
    self.typ() == other.typ()
  }

  /// Transforms a value into a term.
  pub fn to_term(& self) -> Option<::term::Term> {
    match * self {
      RVal::I(ref i) => Some( ::term::int(i.clone()) ),
      RVal::R(ref r) => Some( ::term::real(r.clone()) ),
      RVal::B(b) => Some( ::term::bool(b) ),
      RVal::N(_) => None,
      RVal::Array { ref idx_typ, ref default, ref vals } => {
        let default = default.to_term().expect(
          "default of array cannot be non-value"
        ) ;
        let mut res = term::cst_array(idx_typ.clone(), default) ;
        for (idx, val) in vals {
          let (idx, val) = (
            idx.to_term().expect("index of arrays cannot be non-value"),
            val.to_term().expect("value of arrays cannot be non-value"),
          ) ;
          res = term::store(res, idx, val) ;
        }
        Some(res)
      },
    }
  }

  /// Equal operator.
  pub fn eql(& self, other: & Val) -> Val {
    if ! self.is_known() || ! other.is_known() {
      none(typ::bool())
    } else {
      bool(self == other.get())
    }
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


/// Arithmetic operations.
impl RVal {
  /// Checks if the value is zero (integer or rational).
  pub fn is_zero(& self) -> bool {
    use num::Zero ;
    match * self {
      RVal::I(ref i) => i.is_zero(),
      RVal::R(ref r) => r.is_zero(),
      _ => false,
    }
  }

  /// Checks if the value is one (integer or rational).
  pub fn is_one(& self) -> bool {
    use num::One ;
    match * self {
      RVal::I(ref i) => i == & Int::one(),
      RVal::R(ref r) => r == & Rat::one(),
      _ => false,
    }
  }

  /// Checks if the value is minus one (integer or rational).
  pub fn is_minus_one(& self) -> bool {
    use num::One ;
    match * self {
      RVal::I(ref i) => i == & - Int::one(),
      RVal::R(ref r) => r == & - Rat::one(),
      _ => false,
    }
  }

  /// Adds two values.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
          (false, true) => Ok( real( Rat::new(0.into(), 0.into())) ),
        },
        RVal::I(ref rgt) => Ok( int(lft * rgt) ),
        RVal::R(ref rgt) => Ok(
          real( Rat::new(lft * rgt.numer(), rgt.denom().clone()) )
        ),
        ref rgt => bail!(
          "expected arith values, found {} and {}", lft, rgt
        ),
      }

      RVal::R(ref lft) => match other.to_real() ? {
        None => if lft.is_zero() {
          Ok( real( Rat::new(0.into(), 1.into()) ) )
        } else {
          Ok( none(typ::real()) )
        },
        Some(rgt) => Ok( real(lft * rgt) ),
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
      RVal::R(ref r) => Ok( real(- r) ),
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
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
}



/// Operations over booleans.
impl RVal {

  /// Conjunction.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
        "expected boolean values, found values of type {} and {}",
        lft.typ(), rgt.typ()
      )
    }
  }

  /// Disjunction.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
        "expected boolean values, found values of type {} and {}",
        lft.typ(), rgt.typ()
      )
    }
  }
  /// Negation.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::typ ;
  /// use hoice::val ;
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
      _ => bail!(
        "expected boolean value, found value of type {}", self.typ()
      ),
    }
  }

  /// True iff the value is true.
  pub fn is_true(& self) -> bool {
    self == & RVal::B(true)
  }

  /// True iff the value is false.
  pub fn is_false(& self) -> bool {
    self == & RVal::B(false)
  }
}



/** Operations over arrays.

# Examples

```
use hoice::term::typ ;
use hoice::val::* ;

let first_array = array( typ::int(), int(0) ) ;
# println!("{}", first_array) ;

assert_eq! { first_array.select( int(7) ), int(0) }
// Following works because `first_array` is constant.
assert_eq! { first_array.select( none(typ::int()) ), int(0) }

let array = first_array.store(int(7), int(0)) ;
# println!("{}", array) ;
assert_eq! { array, first_array }

let array = first_array.store(int(7), int(1)) ;
# println!("{}", array) ;

# println!("array[{}] = {}", 7, 1) ;
assert_eq! { array.select( int(7) ), int(1) }
# println!("array[{}] = {}", 5, 0) ;
assert_eq! { array.select( int(5) ), int(0) }
# println!("array[{}] = {}", 0, 0) ;
assert_eq! { array.select( int(0) ), int(0) }
# println!("array[_] = {}", 1) ;
// Select on `none` does not work anymore, array is not constant.
assert_eq! { array.select( none(typ::int()) ), none(typ::int()) }
```
*/
impl RVal { 
  /// Store over arrays, creates a `RVal`.
  ///
  /// Does not actually create a `Val`.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::typ ;
  /// use hoice::val::* ;
  ///
  /// let arr: RVal = array( typ::int(), int(0) ).raw_store(int(7), int(0)) ;
  /// assert_eq! {
  ///   & format!("{}", arr), "((as const (Array Int Int)) 0)"
  /// }
  ///
  /// let arr: RVal = array( typ::int(), int(0) ).raw_store(int(7), int(1)) ;
  /// assert_eq! {
  ///   & format!("{}", arr), "(store ((as const (Array Int Int)) 0) 7 1)"
  /// }
  /// ```
  pub fn raw_store<V: Into<Val>>(& self, idx: V, val: V) -> Self {
    let (idx, val) = ( idx.into(), val.into() ) ;
    let idx = if ! idx.is_known() {
      idx.typ().default_val()
    } else {
      idx
    } ;
    let val = if ! val.is_known() {
      val.typ().default_val()
    } else {
      val
    } ;
    match * self {
      RVal::Array { ref idx_typ, ref default, ref vals } => {
        debug_assert_eq! { idx_typ, & idx.typ() }
        debug_assert_eq! { default.typ(), val.typ() }
        debug_assert! { idx.is_known() }
        debug_assert! { val.is_known() }

        let mut nu_vals: Vec<_> = vals.iter().filter_map(
          |(i, v)| if i != & idx {
            Some( (i.clone(), v.clone()) )
          } else {
            None
          }
        ).collect() ;

        let (idx_typ, default) = (
          idx_typ.clone(), default.clone()
        ) ;
        if default != val {
          nu_vals.push( (idx, val) )
        }

        nu_vals.sort_unstable() ;

        return RVal::Array { idx_typ, default, vals: nu_vals }
      },

      RVal::N(ref typ) => if let Some((i, v)) = typ.array_inspect() {
        debug_assert_eq! { & idx.typ(), i }
        debug_assert_eq! { & val.typ(), v }
        let vals = vec![ (idx, val) ] ;
        return RVal::Array {
          idx_typ: i.clone(), default: v.default_val(), vals
        }
      } else {
        ()
      },

      _ => (),
    }

    panic!(
      "trying to store value {}: {} at {}: {} in non-array value {}: {}",
      idx, idx.typ(), val, val.typ(), self, self.typ()
    )
  }

  /// Store over arrays.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::typ ;
  /// use hoice::val::* ;
  ///
  /// let arr: RVal = array( typ::int(), int(0) ).raw_store(int(7), int(0)) ;
  /// assert_eq! {
  ///   & format!("{}", arr), "((as const (Array Int Int)) 0)"
  /// }
  ///
  /// let arr = array( typ::int(), int(0) ).store(int(7), int(1)) ;
  /// assert_eq! {
  ///   & format!("{}", arr), "(store ((as const (Array Int Int)) 0) 7 1)"
  /// }
  /// ```
  pub fn store<V: Into<Val>>(& self, idx: V, val: V) -> Val {
    factory.mk( self.raw_store(idx, val) )
  }

  /// Select over arrays.
  ///
  /// # Examples
  ///
  /// ```
  /// use hoice::term::typ ;
  /// use hoice::val::* ;
  ///
  /// let array = array( typ::int(), int(0) ).store(int(7), int(1)) ;
  /// assert_eq! {
  ///   & format!("{}", array), "(store ((as const (Array Int Int)) 0) 7 1)"
  /// }
  /// assert_eq! { array.select( int(7) ), int(1) }
  /// assert_eq! { array.select( int(5) ), int(0) }
  /// assert_eq! { array.select( int(0) ), int(0) }
  /// assert_eq! { array.select( none(typ::int()) ), none(typ::int()) }
  /// ```
  pub fn select<V: Into<Val>>(& self, idx: V) -> Val {
    let idx = idx.into() ;
    match * self {
      RVal::Array { ref idx_typ, ref default, ref vals } => {
        debug_assert_eq! { idx_typ, & idx.typ() }

        // If the index is a non-value...
        if ! idx.is_known() {
          // and the array is constant, return that value.
          if vals.is_empty() {
            return default.clone()
          } else {
            return none( default.typ().clone() )
          }
        }

        for (cond, val) in vals {
          match Op::Eql.eval(vec![idx.clone(), cond.clone()]).and_then(
            |res| res.to_bool()
          ) {
            Ok( Some(true) ) => return val.clone(),
            Ok( Some(false) ) => (),
            Ok(None) => panic!(
              "non-value array condition (= {} {})", idx, cond
            ),
            Err(e) => {
              print_err(e) ;
              panic!(
                "while evaluating array condition (= {} {})", idx, cond
              )
            }
          }
        }

        return default.clone()
      },

      RVal::N(ref typ) => if let Some((i, v)) = typ.array_inspect() {
        debug_assert_eq! { i, & idx.typ() }
        return none( v.clone() )
      } else {
        ()
      },

      _ => (),
    }
    panic!(
      "trying to select at {}: {} in non-array value {}: {}",
      idx, idx.typ(), self, self.typ()
    )
  }
}




impl_fmt!{
  RVal(self, fmt) {
    match * self {
      RVal::N(ref t) => write!(fmt, "_[{}]", t),
      RVal::I(ref i) => int_to_smt!(fmt, i),
      RVal::R(ref r) => rat_to_smt!(fmt, r),
      RVal::B(b) => write!(fmt, "{}", b),
      RVal::Array { ref default, ref vals, .. } => {
        for _ in vals {
          write!(fmt, "(store ") ?
        }
        write!(fmt, "((as const {}) {})", self.typ(), default) ? ;
        for (cond, val) in vals.iter().rev() {
          write!(fmt, " {} {})", cond, val) ?
        }
        Ok(())
      },
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
