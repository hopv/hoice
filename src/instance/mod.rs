//! The instance stores the predicates, the clauses, and a lot of information.

use common::*;

pub mod info;
#[cfg_attr(feature = "cargo-clippy", allow(module_inception))]
mod instance;

pub mod preproc;

pub use self::instance::{Clause, Instance, PreInstance};
