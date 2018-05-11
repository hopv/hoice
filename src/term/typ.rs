//! Everything type-related.

use hashconsing::{ HashConsign, HConser, HConsed } ;

use common::* ;

/// Type of the term factory.
type Factory = RwLock< HashConsign<RTyp> > ;

lazy_static! {
  /// Term factory.
  static ref factory: Factory = RwLock::new(
    HashConsign::with_capacity( conf.instance.term_capa )
  ) ;
}


/// Generates the `Int` type.
pub fn int() -> Typ {
  factory.mk(RTyp::Int)
}
/// Generates the `Real` type.
pub fn real() -> Typ {
  factory.mk(RTyp::Real)
}
/// Generates the `Bool` type.
pub fn bool() -> Typ {
  factory.mk(RTyp::Bool)
}
/// Generates an Array type.
pub fn array(typ: Typ) -> Typ {
  factory.mk(RTyp::Array(typ))
}

/// A hash-consed type.
pub type Typ = HConsed<RTyp> ;


/// Types.
#[
  derive(
    Debug, Clone,
    PartialEq, Eq, Hash,
    PartialOrd, Ord
  )
]
pub enum RTyp {
  /// Integers.
  Int,
  /// Reals.
  Real,
  /// Booleans.
  Bool,
  /// Arrays.
  Array(Typ)
}
impl RTyp {
  /// True if the type is bool.
  pub fn is_bool(& self) -> bool {
    * self == RTyp::Bool
  }
  /// True if the type is integer.
  pub fn is_int(& self) -> bool {
    * self == RTyp::Int
  }
  /// True if the type is real.
  pub fn is_real(& self) -> bool {
    * self == RTyp::Real
  }

  /// True if the type is arithmetic.
  pub fn is_arith(& self) -> bool {
    match * self {
      RTyp::Int | RTyp::Real => true,
      _ => false,
    }
  }

  /// Given two arithmetic types, returns `Real` if one of them is `Real`.
  pub fn arith_join(self, other: Self) -> Self {
    debug_assert! { self.is_arith() }
    debug_assert! { other.is_arith() }
    if self == RTyp::Real || other == RTyp::Real {
      RTyp::Real
    } else {
      RTyp::Int
    }
  }

  /// Default value of a type.
  pub fn default_val(& self) -> Val {
    match * self {
      RTyp::Real => val::rat( Rat::zero() ),
      RTyp::Int => val::int( Int::zero() ),
      RTyp::Bool => val::bool( true ),
      RTyp::Array(_) => unimplemented!(),
    }
  }

  /// Default term of a type.
  pub fn default_term(& self) -> Term {
    match * self {
      RTyp::Real => term::real( Rat::zero() ),
      RTyp::Int => term::int( Int::zero() ),
      RTyp::Bool => term::bool( true ),
      RTyp::Array(_) => unimplemented!(),
    }
  }
}
impl ::rsmt2::print::Sort2Smt for RTyp {
  fn sort_to_smt2<Writer>(
    & self, w: &mut Writer
  ) -> SmtRes<()> where Writer: Write {
    write!(w, "{}", self) ? ;
    Ok(())
  }
}

/// Display implementation.
///
/// # Examples
///
/// ```
/// # use rsmt2::term::typ::* ;
/// debug_assert_eq! {
///   format!("{}", array(array(int()))),
///   "(Array (Array Int))"
/// }
/// ```
impl_fmt!{
  RTyp(self, fmt) {
    let mut stack = vec![ (vec![self], "", "") ] ;

    'stack: while let Some( (mut typs, sep, end) ) = stack.pop() {
      while let Some(typ) = typs.pop() {
        match * typ {
          RTyp::Int => write!(fmt, "{}Int", sep) ?,
          RTyp::Real => write!(fmt, "{}Real", sep) ?,
          RTyp::Bool => write!(fmt, "{}Bool", sep) ?,

          RTyp::Array(ref typ) => {
            stack.push((typs, sep, end)) ;
            fmt.write_str("(Array") ? ;
            stack.push((vec![& * typ], " ", ")")) ;
            continue 'stack
          },
        }
      }
    }

    Ok(())
  }
}