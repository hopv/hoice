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
///
/// All `t*` are terms. Synthesizes qualifiers of the form
///
/// - `t = n`, `t <= n`, `t >= n`,
/// - `t_1 = t_2`, `t_1 = - t_2`,
/// - `t_1 + t_2 >= n`, `t_1 + t_2 <= n`,
/// - `t_1 - t_2 >= n`, `t_1 - t_2 <= n`,
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

/// Level 1 arithmetic synthesis.
///
/// All `t*` are terms, `<op>` is `=`, `ge` or `le. Synthesizes qualifiers
/// of the form
///
/// - `+ t_1 + t_2 + t_3 <op> n`
/// - `+ t_1 + t_2 - t_3 <op> n`
/// - `+ t_1 - t_2 + t_3 <op> n`
/// - `+ t_1 - t_2 - t_3 <op> n`
/// - `- t_1 + t_2 + t_3 <op> n`
/// - `- t_1 + t_2 - t_3 <op> n`
/// - `- t_1 - t_2 + t_3 <op> n`
/// - `- t_1 - t_2 - t_3 <op> n`
#[macro_export]
macro_rules! arith_synth_1 {
  ($previous:tt, $f:tt, $constructor:tt | $term:tt = $val:expr) => ({
    {
      let mut previous = $previous.iter() ;

      while let Some(
        & (ref other_term, ref other_val)
      ) = previous.next() {
        for & (ref another_term, ref another_val) in previous.clone() {

          arith_synth_1! { @internal
            $f(
              term::add(
                vec![ $term.clone(), other_term.clone(), another_term.clone() ]
              ),
              term::$constructor( & $val + other_val + another_val )
            )
          }

          arith_synth_1! { @internal
            $f(
              term::add(
                vec![
                  $term.clone(),
                  other_term.clone(),
                  term::sub( vec![ another_term.clone() ] ),
                ]
              ),
              term::$constructor( & $val + other_val - another_val )
            )
          }

          arith_synth_1! { @internal
            $f(
              term::add(
                vec![
                  $term.clone(),
                  term::sub( vec![ other_term.clone() ] ),
                  another_term.clone(),
                ]
              ),
              term::$constructor( & $val - other_val + another_val )
            )
          }

          arith_synth_1! { @internal
            $f(
              term::sub(
                vec![
                  $term.clone(), other_term.clone(), another_term.clone()
                ]
              ),
              term::$constructor( & $val - other_val - another_val )
            )
          }

          arith_synth_1! { @internal
            $f(
              term::add(
                vec![
                  term::sub( vec![ $term.clone() ] ),
                  other_term.clone(),
                  another_term.clone()
                ]
              ),
              term::$constructor( (- & $val) + other_val + another_val )
            )
          }

          arith_synth_1! { @internal
            $f(
              term::sub(
                vec![
                  other_term.clone(),
                  $term.clone(),
                  another_term.clone()
                ]
              ),
              term::$constructor( (- & $val) + other_val - another_val )
            )
          }

          arith_synth_1! { @internal
            $f(
              term::sub(
                vec![
                  another_term.clone(),
                  $term.clone(),
                  other_term.clone(),
                ]
              ),
              term::$constructor( (- & $val) - other_val + another_val )
            )
          }

          arith_synth_1! { @internal
            $f(
              term::sub(
                vec![
                  term::add(
                    vec![
                      $term.clone(),
                      other_term.clone(),
                      another_term.clone()
                    ]
                  )
                ]
              ),
              term::$constructor( (- & $val) - other_val - another_val )
            )
          }

        }
      }
    }
    $previous.push( ($term, $val.clone()) )
  }) ;
  (@internal $f:tt($lhs:expr, $rhs:expr)) => ({
    let term = term::app(
      Op::Ge, vec![ $lhs.clone(), $rhs.clone() ]
    ) ;
    // println!() ;
    // println!("> {}", term) ;
    apply! { $f to term }
    let term = term::app(
      Op::Le, vec![ $lhs.clone(), $rhs.clone() ]
    ) ;
    // println!() ;
    // println!("> {}", term) ;
    apply! { $f to term }
    let term = term::app(
      Op::Eql, vec![ $lhs.clone(), $rhs.clone() ]
    ) ;
    // println!() ;
    // println!("> {}", term) ;
    apply! { $f to term }
  }) ;
}