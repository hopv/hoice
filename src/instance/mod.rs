//! The instance stores the predicates, the clauses, and a lot of information.

use common::* ;
use self::info::* ;

pub mod info ;
#[cfg_attr(feature = "cargo-clippy", allow(module_inception))]
mod instance ;
pub mod parse ;
pub mod preproc ;

pub use self::instance::{ Clause, Instance, PreInstance } ;