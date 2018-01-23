//! Macros factoring code for the synthesis process.


/// Applies `$f` to `$term`.
///
/// Early returns if the application is an error. Early returns `Ok(true)` if
/// the application yields true.
macro_rules! apply {
  ($f:ident to $term:expr) => (
    if $f($term)? { return Ok(true) }
  ) ;
}

/// Simple arithmetic synthesis.
#[macro_export]
macro_rules! simple_arith_synth {
  ($previous:tt, $f:tt, $constructor:tt | $term:tt = $val:expr) => ({

    let val_term = term::$constructor( $val.clone() ) ;
    let term = term::app(
      Op::Ge, vec![ $term.clone(), val_term.clone() ]
    ) ;
    apply! { $f to term }
    let term = term::app(
      Op::Le, vec![ $term.clone(), val_term.clone() ]
    ) ;
    apply! { $f to term }
    let term = term::app(
      Op::Eql, vec![ $term.clone(), val_term ]
    ) ;
    apply! { $f to term }

    for & (ref other_term, ref other_val) in & $previous {
      if & $val == other_val {
        let term = term::eq(
          $term.clone(), other_term.clone()
        ) ;
        apply! { $f to term }
      }
      if - (& $val) == * other_val {
        let term = term::eq(
          $term.clone(), term::sub( vec![ other_term.clone() ] )
        ) ;
        apply! { $f to term }
      }

      let add = term::app(
        Op::Add, vec![ $term.clone(), other_term.clone() ]
      ) ;
      let add_val = term::$constructor( & $val + other_val ) ;
      let term = term::app(
        Op::Ge, vec![ add.clone(), add_val.clone() ]
      ) ;
      apply! { $f to term }
      let term = term::app(
        Op::Le, vec![ add, add_val ]
      ) ;
      apply! { $f to term }

      let sub = term::app(
        Op::Sub, vec![ $term.clone(), other_term.clone() ]
      ) ;
      let sub_val = term::$constructor( & $val - other_val ) ;
      let term = term::app(
        Op::Ge, vec![ sub.clone(), sub_val.clone() ]
      ) ;
      apply! { $f to term }
      let term = term::app(
        Op::Le, vec![ sub, sub_val ]
      ) ;
      apply! { $f to term }
    }

    $previous.push( ($term, $val.clone()) )
  }) ;
}