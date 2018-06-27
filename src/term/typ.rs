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
pub fn array(src: Typ, tgt: Typ) -> Typ {
  factory.mk(RTyp::Array { src, tgt })
}

/// A hash-consed type.
pub type Typ = HConsed<RTyp> ;


/// Types.
///
/// # Examples
///
/// ```rust
/// use hoice::term::typ::* ;
/// debug_assert_eq! {
///   format!("{}", array(int(), array(int(), int()))),
///   "(Array Int (Array Int Int))"
/// }
/// ```
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
  Array {
    /// Type of indices.
    src: Typ,
    /// Type of values
    tgt: Typ,
  }
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

  /// True if the type is an array.
  pub fn is_array(& self) -> bool {
    match * self {
      RTyp::Array { .. } => true,
      _ => false,
    }
  }

  /// Inspects an array type.
  pub fn array_inspect(& self) -> Option<(& Typ, & Typ)> {
    match * self {
      RTyp::Array { ref src, ref tgt } => Some((src, tgt)),
      _ => None,
    }
  }

  /// Default value of a type.
  pub fn default_val(& self) -> Val {
    match * self {
      RTyp::Real => val::real( Rat::zero() ),
      RTyp::Int => val::int( Int::zero() ),
      RTyp::Bool => val::bool( true ),
      RTyp::Array { ref src, ref tgt } => val::array(
        src.clone(), tgt.default_val(),
      ),
    }
  }

  /// Default term of a type.
  pub fn default_term(& self) -> Term {
    match * self {
      RTyp::Real => term::real( Rat::zero() ),
      RTyp::Int => term::int( Int::zero() ),
      RTyp::Bool => term::bool( true ),
      RTyp::Array { ref src, ref tgt } => term::cst_array(
        src.clone(), tgt.default_term()
      ),
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

impl_fmt!{
  RTyp(self, fmt) {
    let mut stack = vec![ (vec![self].into_iter(), "", "") ] ;

    'stack: while let Some( (mut typs, sep, end) ) = stack.pop() {
      while let Some(typ) = typs.next() {
        fmt.write_str(sep) ? ;
        match * typ {
          RTyp::Int => fmt.write_str("Int") ?,
          RTyp::Real => fmt.write_str("Real") ?,
          RTyp::Bool => fmt.write_str("Bool") ?,

          RTyp::Array { ref src, ref tgt } => {
            stack.push((typs, sep, end)) ;
            fmt.write_str("(Array") ? ;
            stack.push(
              (vec![& * src as & RTyp, & * tgt].into_iter(), " ", ")")
            ) ;
            continue 'stack
          },
        }
      }
      fmt.write_str(end) ?
    }

    Ok(())
  }
}