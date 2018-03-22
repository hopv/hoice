//! Constants of the crate.

lazy_static! {
  /// The constant `10` as an [`Int`][int].
  ///
  /// [int]: ../type.Int.html
  /// (Int type)
  pub static ref ten: ::common::Int = 10.into() ;
}


/// Use this macro to declare keywords.
///
/// Declares everything and creates a function testing if a string is a
/// keyword.
macro_rules! keys {
  // Create one keyword.
  (|internal def|
    $id:ident $def:expr, $doc:meta $(,$meta:meta)* $(,)*
  ) => (
    #[$doc]
    $(#[$meta])*
    pub const $id: & str = $def ;
  ) ;

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
  ) ;

  (|internal lockstep|
    $( ($($left:tt)*) )*, $mid:tt, $right:tt
  ) => (
    keys!{ $($($left)* $mid $right)* }
  ) ;
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

        as_ ("as", doc = "As.")
      }
    }

    doc = "Command-related keywords."
    mod cmd {
      funs {
        is_keyword ()
      }

      keys {
        dec_fun ("declare-fun", doc = "Predicate declaration keyword.")
        def_fun ("define-fun", doc = "Predicate definition keyword.")
        def_funs (
          "define-funs-rec", doc = "Multiple predicate declaration keyword."
        )

        assert ("assert", doc = "Assertion keyword.")

        check_sat ("check-sat", doc = "Check-sat keyword.")
        get_model ("get-model", doc = "Get-model keyword.")

        reset ("reset", doc = "Reset keyword.")
        exit  ("exit", doc = "Exit keyword.")
      }
    }

  }


}