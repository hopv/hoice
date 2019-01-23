//! Hashconsed maps from variables to other things.
//!
//! Submodule [`var_to::vals`] handles variable to value maps. This is used to represent samples in
//! the context of learning data. Submodule [`var_to::terms`] maps variables to terms. It is used
//! to store the arguments of predicate applications.
//!
//! [`var_to::vals`]: vals/index.html (var_to::vals module)
//! [`var_to::terms`]: terms/index.html (var_to::terms module)

pub mod terms;
pub mod vals;

pub use self::terms::VarTerms;
pub use self::vals::VarVals;
