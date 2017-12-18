//! The instance stores the predicates, the clauses, and a lot of information.

use common::* ;
use self::info::* ;

pub mod info ;
mod instance ;
pub mod parse ;
pub mod preproc ;

pub use self::instance::{ Clause, Instance, PreInstance } ;