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
impl Val {
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
impl From<()> for Val {
  fn from(_: ()) -> Val {
    Val::N
  }
}