//! Macros.

/// If the input is an error, prints it SMT-LIB-style and panics.
#[macro_export]
macro_rules! expect {
  ($e:expr => |$err:pat| $($action:tt)*) => (
    match $e {
      Ok(res) => res,
      Err($err) => {
        $crate::errors::print_err(
          & { $($action)* }.into()
        ) ;
        panic!("Fatal internal error, please contact the developper")
      }
    }
  ) ;
  ($e:expr) => (
    expect! {
      $e => |e| e
    }
  ) ;
}

/// Fails with some message, SMT-LIB-style.
#[macro_export]
macro_rules! fail_with {
  ( $($head:expr),* $(,)* $( ; $($blah:expr),* $(,)* )* $(;)* ) => ({
    let err: Res<()> = Err(
      format!($($head),*).into()
    ) ;
    $(
      let err = err.chain_err(
        || format!( $($blah),* )
      ) ;
    )*
    expect!(err) ;
    unreachable!()
  }) ;
}

/// Bails with unsat.
///
/// Logs unsat (`@info`) and the input message if any (`@debug`).
#[macro_export]
macro_rules! unsat {
  ($($stuff:tt)*) => ({
    log! { @info "unsat" } ;
    log! { @debug $($stuff)* } ;
    bail!($crate::errors::ErrorKind::Unsat)
  }) ;
}

/// Bails with unknown.
#[macro_export]
macro_rules! unknown {
  ($($stuff:tt)*) => ({
    log! { @debug $($stuff)* } ;
    bail!($crate::errors::ErrorKind::Unknown)
  }) ;
}

/// Wraps stuff in a block, usually to please borrow-checking.
#[macro_export]
macro_rules! scoped {
  ($($tokens:tt)*) => ({
    $($tokens)*
  })
}

/// Chains some errors and bails.
#[macro_export]
macro_rules! err_chain {
  ($head:expr $(=> $tail:expr)*) => ({
    let mut err: Error = $head.into() ;
    $(
      err = err.chain_err(|| $tail) ;
    )*
    bail!(err)
  })
}

/// Guards something by a log level, inactive in bench mode.
#[cfg(not(feature = "bench"))]
#[macro_export]
macro_rules! if_log {
  ( @$flag:tt then { $($then:tt)* } else { $($else:tt)* } ) => (
    if log!(|cond_of| $flag) { $($then)* } else { $($else)* }
  ) ;

  (@$flag:tt $($stuff:tt)*) => (
    if_log! { @$flag then { $($stuff)* } else { () } }
  ) ;
}
#[cfg(feature = "bench")]
#[macro_export]
macro_rules! if_log {
  ( @$flag:tt then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($else)*
  ) ;
  (@$flag:tt $($stuff:tt)*) => (()) ;
}

/** Logging macro, inactive in bench mode.

| Log level | active when...     | prefix (`_` are spaces)             |
|-----------|--------------------|:------------------------------------|
| `@0`      | `true`             | `";_"`                              |
| `@warn`   | `true`             | `";_Warning_|_"`                    |
| `@info`   | `conf.verb ≥ 1`    | `";_"`                              |
| `@verb`   | `conf.verb ≥ 2`    | `";___"`                            |
| `@debug`  | `conf.verb ≥ 3`    | `";_____"`                          |
| `@<i>`    | `conf.verb ≥ <i>`  | `";_"` followed by `<i> * 2` spaces |

*/
#[macro_export]
#[cfg(not(feature = "bench"))]
macro_rules! log {

  (|pref_of| debug) => ( log!(|pref_of| 2) ) ;
  (|pref_of| verb)  => ( log!(|pref_of| 1) ) ;
  (|pref_of| info)  => ( log!(|pref_of| 0) ) ;
  (|pref_of| warn)  => ( format!("{}Warning | ", log!(|pref_of| 0)) ) ;
  (|pref_of| 0) => ( format!("; ") ) ;
  (|pref_of| $int:expr) => (
    format!("; {:width$}", "", width = ($int - 1) * 2)
  ) ;

  (|cond_of| debug) => ( log!(|cond_of| 3) ) ;
  (|cond_of| verb)  => ( log!(|cond_of| 2) ) ;
  (|cond_of| info)  => ( log!(|cond_of| 1) ) ;
  (|cond_of| warn) => ( true ) ;
  (|cond_of| 0) => (true) ;
  (|cond_of| $int:expr) => (conf.verb >= $int) ;

  ( $cond:expr, $op:tt @$flag:tt $($tail:tt)* ) => (
    if $cond $op log!(|cond_of| $flag) {
      log! { log!(|pref_of| $flag) => $($tail)* }
    }
  ) ;

  ( @$flag:tt |=> $($tail:tt)* ) => (
    log! { > log!(|pref_of| $flag) => $($tail)* }
  ) ;
  ( @$flag:tt | $($tail:tt)* ) => (
    if log!(|cond_of| $flag) {
      log! { > log!(|pref_of| $flag) => $($tail)* }
    }
  ) ;

  ( @$flag:tt => $($tail:tt)* ) => (
    log! { log!(|pref_of| $flag) => $($tail)* }
  ) ;
  ( @$flag:tt $($tail:tt)* ) => (
    if log!(|cond_of| $flag) {
      log! { log!(|pref_of| $flag) => $($tail)* }
    }
  ) ;

  ( > $pref:expr => $( $str:expr $(, $args:expr)* $(,)* );* ) => ({
    $(
        println!("{}{}", $pref, format!($str $(, $args)*)) ;
    )*
    ()
  }) ;
  ( > $( $str:expr $(, $args:expr)* $(,)* );* ) => ({
    $(
      println!("; {}", format!($str $(, $args)*))
    )*
    ()
  }) ;

  ( $pref:expr => $( $str:expr $(, $args:expr)* $(,)* );* ) => ({
    $(
      for line in format!($str $(, $args)*).lines() {
        if line != "" {
          println!("{}{}", $pref, line)
        } else {
          println!()
        }
      }
    )*
    ()
  }) ;
  ( $( $str:expr $(, $args:expr)* $(,)* );* ) => ({
    $(
      for line in format!($str $(, $args)*).lines() {
        if line != "" {
          println!("; {}", line)
        } else {
          println!()
        }
      }
    )*
    ()
  }) ;
}
#[cfg(feature = "bench")]
macro_rules! log {
    (|pref_of| $($stuff:tt)*) => {
        ""
    };
    (|cond_of| $($stuff:tt)*) => {
        false
    };
    ($($stuff:tt)*) => {
        ()
    };
}

/// Same as `log! { @verb ... }`.
#[macro_export]
macro_rules! log_verb {
  ( $($stuff:tt)* ) => (
    log! { @verb $($stuff)* }
  ) ;
}
/// Same as `log! { @info ... }`.
#[macro_export]
macro_rules! log_info {
  ( $($stuff:tt)* ) => (
    log! { @info $($stuff)* }
  ) ;
}
/// Same as `log! { @debug ... }`.
#[macro_export]
#[allow(unused_macros)]
macro_rules! log_debug {
  ( $($stuff:tt)* ) => (
    log! { @debug $($stuff)* }
  ) ;
}

/// Prints a warning SMT-LIB-style.
///
/// **Active in bench mode.**
#[macro_export]
macro_rules! warn {
  ( $( $str:expr $(, $args:expr)* $(,)* );* ) => ({
    println!(
      "; {}", $crate::common::conf.sad("|===| Warning:")
    ) ;
    $(
      print!("; {} ", $crate::common::conf.sad("|")) ;
      println!( $str $(, $args)* ) ;
    )*
    println!("; {}", $crate::common::conf.sad("|===|"))
  }) ;
}

/// Does something if not in bench mode.
#[macro_export]
#[cfg(not(feature = "bench"))]
macro_rules! if_not_bench {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($then)*
  ) ;
  ($($stuff:tt)*) => (
    if_not_bench! {
      then { $($stuff)* } else { () }
    }
  ) ;
}
/// Does something if not in bench mode.
#[cfg(feature = "bench")]
macro_rules! if_not_bench {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($else)*
  ) ;
  ($($stuff:tt)*) => (()) ;
}

/// Same as `if_log! { @verb ... }`.
#[macro_export]
macro_rules! if_verb {
  ($($stuff:tt)*) => ( if_log! { @verb $($stuff)* } ) ;
}

/// Same as `if_log! { @debug ... }` .
#[macro_export]
macro_rules! if_debug {
  ($($stuff:tt)*) => ( if_log! { @debug $($stuff)* } ) ;
}

/// Profiling macro, inactive in  bench mode.
///
/// If passed `self`, assumes `self` has a `_profiler` field.
#[macro_export]
#[cfg(not(feature = "bench"))]
macro_rules! profile {
  ( | $stuff:ident $(. $prof:ident)* |
    wrap $b:block $( $scope:expr ),+ $(,)*
  ) => ({
    profile! { | $stuff $(. $prof)* | tick $($scope),+ }
    let res = $b ;
    profile! { | $stuff $(. $prof)* | mark $($scope),+ }
    res
  }) ;
  ( | $stuff:ident $(. $prof:ident)* | $stat:expr => add $e:expr ) => (
    if conf.stats {
      $stuff$(.$prof)*.stat_do( $stat, |val| val + $e )
    }
  ) ;
  ( | $stuff:ident $(. $prof:ident)* | $stat:expr => set $e:expr ) => (
    if conf.stats {
      $stuff$(.$prof)*.stat_do( $stat, |val| val + $e )
    }
  ) ;
  ( | $stuff:ident $(. $prof:ident)* |
    $meth:ident $( $scope:expr ),+ $(,)*
  ) => (
    if conf.stats {
      $stuff$(.$prof)*.$meth(
        vec![ $($scope),+ ]
      )
    }
  ) ;
  ( $slf:ident wrap $b:block $( $scope:expr ),+ $(,)* ) => (
    profile! { |$slf._profiler| wrap $b $($scope),+ }
  ) ;
  ( $slf:ident $stat:expr => add $e:expr ) => (
    profile!{ |$slf._profiler| $stat => add $e }
  ) ;
  ( $slf:ident $meth:ident $( $scope:expr ),+ $(,)* ) => (
    profile!{ |$slf._profiler| $meth $($scope),+ }
  ) ;
}
#[cfg(feature = "bench")]
macro_rules! profile {
    ( | $stuff:ident $(. $prof:ident)* |
    wrap $b:block $( $scope:expr ),+ $(,)*
  ) => {
        $b
    };
    ( $slf:ident
    wrap $b:block $( $scope:expr ),+ $(,)*
  ) => {
        $b
    };
    ( $($stuff:tt)* ) => {
        ()
    };
}

/// Messaging macro, compiled to nothing in bench mode.
#[cfg(not(feature = "bench"))]
#[macro_export]
macro_rules! msg {
  ( @$flag:tt $slf:expr => $($tt:tt)* ) => (
    if log!(|cond_of| $flag) {
      msg!( force $slf => $($tt)* )
    }
  ) ;
  ( debug $slf:expr => $($tt:tt)* ) => (
    if conf.verb >= 3 {
      msg!( force $slf => $($tt)* )
    }
  ) ;
  ( force $slf:expr => $e:tt ) => (
    $slf.msg($e) ? ;
  ) ;
  ( force $slf:expr => $($tt:tt)* ) => (
    $slf.msg( format!( $($tt)* ) ) ? ;
  ) ;
  ( $core:expr => $e:expr ) => (
    if_debug!( $core.msg($e) ? )
  ) ;
  ( $slf:expr => $($tt:tt)* ) => (
    msg!{ $slf => format!( $($tt)* ) }
  ) ;
}
#[macro_export]
#[cfg(feature = "bench")]
macro_rules! msg {
    ( $($tt:tt)* ) => {
        ()
    };
}

/// Yields the value if the type (int or bool) matches, otherwise
/// `return`s `Ok(Val::N)`.
///
/// ```rust
/// use hoice::term::Val ;
/// use hoice::errors ;
///
/// fn int(val: Val) -> Res<Val> {
///   Ok( try_val!{ int val } )
/// }
/// fn bool(val: Val) -> Res<Val> {
///   Ok( try_val!{ bool val } )
/// }
///
/// let none = Val::N ;
///
/// let val: Val = 7.into() ;
/// assert_eq!{ int( val.clone() ), val }
/// assert_eq!{ bool( val.clone() ), none }
///
/// let val: Val = false.into() ;
/// assert_eq!{ int( val.clone() ), none }
/// assert_eq!{ bool( val.clone() ), val }
///
/// assert_eq!{ int( none.clone() ), none }
/// assert_eq!{ bool( none.clone() ), none }
/// ```
macro_rules! try_val {
    (int $e:expr) => {
        if let Some(i) = $e.to_int()? {
            i
        } else {
            return Ok($crate::val::none($crate::term::typ::int()));
        }
    };
    (real $e:expr) => {
        if let Some(r) = $e.to_real()? {
            r
        } else {
            return Ok($crate::val::none($crate::term::typ::real()));
        }
    };
    (bool $e:expr) => {
        if let Some(b) = $e.to_bool()? {
            b
        } else {
            return Ok($crate::val::none($crate::term::typ::bool()));
        }
    };
}

/// Dumps an instance if the `PreprocConf` flag says so.
macro_rules! preproc_dump {
    ($instance:expr => $file:expr, $blah:expr) => {
        if let Some(mut file) = conf.preproc.instance_log_file($file, &$instance)? {
            $instance.dump_as_smt2(&mut file, $blah)
        } else {
            Ok(())
        }
    };
}

/// `Int` writer.
#[macro_export]
macro_rules! int_to_smt {
    ($writer:expr, $i:expr) => {
        if $i.is_negative() {
            write!($writer, "(- {})", -$i)
        } else {
            write!($writer, "{}", $i)
        }
    };
}

/// `Rat` writer.
#[macro_export]
macro_rules! rat_to_smt {
    ($writer:expr, $r:expr) => {{
        let (num, den) = ($r.numer(), $r.denom());
        debug_assert!(!den.is_negative());
        if num.is_zero() {
            write!($writer, "0.0")
        } else if !num.is_negative() {
            if den.is_one() {
                write!($writer, "{}.0", num)
            } else {
                write!($writer, "(/ {} {})", num, den)
            }
        } else {
            if den.is_one() {
                write!($writer, "(- {}.0)", -num)
            } else {
                write!($writer, "(- (/ {} {}))", -num, den)
            }
        }
    }};
}

/// Test macros
#[cfg(test)]
#[macro_use]
mod test {

    /// Turns a sequence of values into a `Cex` (`VarMap<Val>`).
    #[macro_export]
    macro_rules! model {
    ( $($values:expr),* ) => (
      $crate::common::VarMap::of(
        vec![ $( $values ),* ]
      )
    ) ;
  }

    /// Checks that the result of an evaluation yields the correct value.
    ///
    /// Prints information before the check.
    #[macro_export]
    macro_rules! assert_eval {
        ( int $model:expr => $expr:expr, $value:expr ) => {{
            let res = $expr.eval(&$model).unwrap().to_int().unwrap().unwrap();
            println!(
                "{} evaluated with {} is {}, expecting {}",
                $expr, $model, res, $value
            );
            assert_eq!(res, $value.into())
        }};

        ( real $model:expr => $expr:expr, $value:expr ) => {{
            let res = $expr.eval(&$model).unwrap().to_real().unwrap().unwrap();
            println!(
                "{} evaluated with {} is {}, expecting {}",
                $expr, $model, res, $value
            );
            assert_eq!(res, rat_of_float($value))
        }};

        ( bool not $model:expr => $expr:expr ) => {{
            let res = $expr.eval(&$model).unwrap().to_bool().unwrap().unwrap();
            println!(
                "{} evaluated with {} is {}, expecting false",
                $expr, $model, res
            );
            assert!(!res)
        }};

        ( bool $model:expr => $expr:expr ) => {{
            let res = $expr.eval(&$model).unwrap().to_bool().unwrap().unwrap();
            println!(
                "{} evaluated with {} is {}, expecting true",
                $expr, $model, res
            );
            assert!(res)
        }};
    }
}

/// Creates some values for some variables.
///
/// Used in tests.
#[macro_export]
macro_rules! r_var_vals {
    (@make($vec:expr) (int $e:expr) $($tail:tt)*) => ({
        $vec.push( $crate::val::int($e) );
        r_var_vals!(@make($vec) $($tail)*)
    });
    (@make($vec:expr) (real $e:expr) $($tail:tt)*) => ({
        $vec.push( $crate::val::real_of($e as f64) );
        r_var_vals!(@make($vec) $($tail)*)
    });
    (@make($vec:expr) (bool $e:expr) $($tail:tt)*) => ({
        $vec.push( $crate::val::bool($e) );
        r_var_vals!(@make($vec) $($tail)*)
    });
    (@make($vec:expr) ($e:expr) $($tail:tt)*) => ({
        $vec.push( $e );
        r_var_vals!(@make($vec) $($tail)*)
    });
    (@make($vec:expr)) => (());
    ($($stuff:tt)*) => ({
        let mut vec = vec![];
        r_var_vals! { @make(vec) $($stuff)* }
        let vals: $crate::var_to::vals::RVarVals = vec.into();
        vals
    });
}
/// Creates some values for some variables (hash-consed).
#[macro_export]
macro_rules! var_vals {
    ($($stuff:tt)*) => ({
        let r_var_vals = r_var_vals!($($stuff)*);
        $crate::var_to::vals::new(r_var_vals)
    });
}
