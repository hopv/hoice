//! Constants of the crate.

lazy_static::lazy_static! {
    /// The constant `10` as an [`Int`].
    ///
    /// [`Int`]: ../type.Int.html (Int type)
    pub static ref ten: crate::common::Int = 10.into() ;
}

/// Error-related constants.
pub mod err {
    /// Description for unsat error(s).
    pub static unsat_desc: &'static str = "unsat";
    /// Description for unknown error(s).
    pub static unknown_desc: &'static str = "unknown";
    /// Description for timeout error(s).
    pub static timeout_desc: &'static str = "timeout";
    /// Description for exit error(s).
    pub static exit_desc: &'static str = "exit";
}

/// Use this macro to declare keywords.
///
/// Declares everything and creates a function testing if a string is a keyword.
macro_rules! keys {
    // Create one keyword.
    (|internal def|
        $id:ident $def:expr, $doc:meta $(,$meta:meta)* $(,)*
    ) => (
        #[$doc]
        $(#[$meta])*
        pub const $id: &str = $def ;
    );

    // Creates some keywords and some functions, if any.
    (
        funs {
            $( $fn_kind:tt ( $($fn_stuff:tt)* ) )*
        }
        keys {
            $( $id:ident ( $($stuff:tt)* ) )*
        }
        $(
            $doc:meta mod $mod:ident { $($mod_stuff:tt)* }
        )*
    ) => (
        #[doc = "
            True if input is one of the keywords defined in this module and its
            submodules.
        "]
        pub fn is_keyword(s: & str) -> bool {
            $(
                if $id == s { return true }
            )*
            $(
                if $mod::is_keyword(s) { return true }
            )*
            false
        }
        $( keys! { |internal def| $id $($stuff)* } )*
        $(
            #[$doc]
            pub mod $mod { keys! { $($mod_stuff)* } }
        )*
    );

    (|internal lockstep|
        $( ($($left:tt)*) )*, $mid:tt, $right:tt
    ) => (
        keys!{ $($($left)* $mid $right)* }
    );
}

/// Values used in hoice.
pub mod values {
    /// Default values.
    pub mod default {
        /// Generate unsat cores?
        pub const unsat_cores: bool = false;
        /// Generate proofs?
        pub const proofs: bool = false;
        /// Print success?
        pub const print_success: bool = false;
    }
}

/// Error messages.
pub mod errors {
    /// Unsat core asked but not active.
    pub const no_unsat_cores: &str = "\
        unsat core production is not active:\n\
        consider adding `(set-option :produce-unsat-core true)`\n\
        at the start of your script
    ";
}

/// Language keywords.
pub mod keywords {

    keys! {

        funs {
            is_keyword ()
        }

        keys {
            forall ("forall", doc = "Universal quantifier.")
            exists ("exists", doc = "Existential quantifier")
            let_ ("let", doc = "Let-binding keyword")
        }

        doc = "Operator-related keywords."
        mod op {
            funs {
                is_keyword ()
            }

            keys {
                distinct_ ("distinct", doc = "Distinct.")

                eq_   ("=", doc = "Equal.")
                not_  ("not", doc = "Not.")
                and_  ("and", doc = "And.")
                or_   ("or", doc = "Or.")
                impl_ ("=>", doc = "Implication.")
                ite_  ("ite", doc = "If-then-else.")

                gt_ (">", doc = "Greater than.")
                ge_ (">=", doc = "Greater than or equal to.")
                lt_ ("<", doc = "Less than.")
                le_ ("<=", doc = "Less than or equal to.")

                add_  ("+", doc = "Addition.")
                sub_  ("-", doc = "Subtraction.")
                mul_  ("*", doc = "Multiplication.")
                div_  ("/", doc = "Division.")
                idiv_ ("div", doc = "Integer division.")
                mod_  ("mod", doc = "Modulo.")
                rem_  ("rem", doc = "Remainder.")

                to_int_ ("to_int", doc = "Conversion from `Real` to `Int`.")
                to_real_ ("to_real", doc = "Conversion from `Int` to `Real`.")

                as_ ("as", doc = "Cast operator.")
                is_ ("is", doc = "Datatype tester.")
                const_ ("const", doc = "Constant cast.")

                store_ ("store", doc = "Updater for arrays.")
                select_ ("select", doc = "Accessor for arrays.")

                match_ ("match", doc = "Match operator.")

                lambda_ ("_", doc = "Lambda abstraction.")
            }
        }

        doc = "Command-related keywords."
        mod cmd {
            funs {
                is_keyword ()
            }

            keys {
                dec_dtyp ("declare-datatype", doc = "Datatype declaration keyword.")
                dec_dtyps (
                    "declare-datatypes", doc = "Multiple datatype declaration keyword."
                )
                dec_fun ("declare-fun", doc = "Predicate declaration keyword.")
                def_fun ("define-fun", doc = "Function definition keyword.")
                def_fun_rec (
                    "define-fun-rec",
                    doc = "Recursive function definition keyword."
                )
                def_funs_rec (
                    "define-funs-rec",
                    doc = "Multiple recursive functions definition keyword."
                )

                assert ("assert", doc = "Assertion keyword.")

                check_sat ("check-sat", doc = "Check-sat keyword.")
                get_model ("get-model", doc = "Get-model keyword.")
                get_unsat_core ("get-unsat-core", doc = "Get-unsat-core keyword.")
                get_proof ("get-proof", doc = "Get-proof keyword.")

                reset ("reset", doc = "Reset keyword.")
                exit  ("exit", doc = "Exit keyword.")
            }
        }
    }
}
