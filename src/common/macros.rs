//! Macros.


/// Does something if not in bench mode.
#[macro_export]
#[cfg(not (feature = "bench") )]
macro_rules! if_not_bench {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($then)*
  ) ;
  ($($blah:tt)*) => ($($blah)*) ;
}
#[cfg(feature = "bench")]
macro_rules! if_not_bench {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($else)*
  ) ;
  ($($blah:tt)*) => (()) ;
}


/// Gates something by an `if conf.verbose()`. Inactive in bench mode.
#[macro_export]
#[cfg(not(feature = "bench"))]
macro_rules! if_verb {
  ($($blah:tt)*) => (
    if conf.verbose() {
      $($blah)*
    }
  ) ;
}
#[cfg(feature = "bench")]
macro_rules! if_verb {
  ($($blah:tt)*) => (()) ;
}


/// Logs at info level using `info!`. Inactive in bench mode.
#[cfg(feature = "bench")]
macro_rules! log_info {
  ($($tt:tt)*) => (()) ;
}
#[cfg(not(feature = "bench"))]
macro_rules! log_info {
  ($($tt:tt)*) => ( info!{$($tt)*} ) ;
}


/// Logs at debug level using `debug!`. Inactive in bench mode.
#[cfg( feature = "bench" )]
macro_rules! log_debug {
  ($($tt:tt)*) => (()) ;
}
#[cfg( not(feature = "bench") )]
macro_rules! log_debug {
  ($($tt:tt)*) => ( debug!{$($tt)*} ) ;
}


/// Does something if in debug mode.
#[macro_export]
#[cfg( not(feature = "bench") )]
macro_rules! if_debug {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($then)*
  ) ;
  ($($blah:tt)*) => (
    if conf.debug() {
      $($blah)*
    }
  ) ;
}
#[cfg(feature = "bench")]
#[allow(unused_macros)]
macro_rules! if_debug {
  ( then { $($then:tt)* } else { $($else:tt)* } ) => (
    $($else)*
  ) ;
  ($($blah:tt)*) => (()) ;
}


/// Profiling macro.
///
/// If passed `self`, assumes `self` has a `_profiler` field.
#[macro_export]
#[cfg( not(feature = "bench") )]
macro_rules! profile {
  ( | $prof:ident | $stat:expr => add $e:expr ) => (
    $prof.stat_do( $stat, |val| val + $e )
  ) ;
  ( | $prof:ident | $meth:ident $( $scope:expr ),+ $(,)* ) => (
    $prof.$meth(
      vec![ $($scope),+ ]
    )
  ) ;
  ( $slf:ident $stat:expr => add $e:expr ) => ({
    let prof = & $slf._profiler ;
    profile!{ |prof| $stat => add $e }
  }) ;
  ( $slf:ident $meth:ident $( $scope:expr ),+ $(,)* ) => ({
    let prof = & $slf._profiler ;
    profile!{ |prof| $meth $($scope),+ }
  }) ;
}
#[cfg(feature = "bench")]
macro_rules! profile {
  ( $($tt:tt)* ) => (()) ;
}


/// Messaging macro, compiled to nothing in `release`.
#[macro_export]
#[cfg( feature = "bench" )]
macro_rules! msg {
  ( $($tt:tt)* ) => (()) ;
}
#[cfg( not(feature = "bench") )]
macro_rules! msg {
  ( debug $slf:expr => $($tt:tt)* ) => (
    if conf.debug() {
      msg!( $slf => $($tt)* )
    } else { true }
  ) ;
  ( $slf:expr => $e:expr ) => (
    if conf.verbose() {
      ::common::msg::HasLearnerCore::msg(
        $slf, $e
      )
    } else { true }
  ) ;
  ( $slf:expr => $($tt:tt)* ) => (
    if conf.verbose() {
      msg!{ $slf => format!( $($tt)* ) }
    } else { true }
  ) ;
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
  (int $e:expr) => (
    if let Some(i) = $e.to_int()? { i } else {
      return Ok( Val::N )
    }
  ) ;
  (bool $e:expr) => (
    if let Some(b) = $e.to_bool()? { b } else {
      return Ok( Val::N )
    }
  ) ;
}


/// Dumps an instance if the `PreprocConf` flag says so.
macro_rules! preproc_dump {
  ($instance:expr => $file:expr, $blah:expr) => (
    if let Some(mut file) = conf.preproc.log_file($file) ? {
      $instance.dump_as_smt2(& mut file, $blah)
    } else { Ok(()) }
  ) ;
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
        vec![ $( $values.into() ),* ]
      )
    ) ;
  }

  /// Checks that the result of an evaluation yields the correct value.
  ///
  /// Prints information before the check.
  #[macro_export]
  macro_rules! assert_eval {
    ( int $model:expr => $expr:expr, $value:expr ) => ({
      let res = $expr.eval(& $model).unwrap().to_int().unwrap().unwrap() ;
      println!(
        "{} evaluated with {} is {}, expecting {}", $expr, $model, res, $value
      ) ;
      assert_eq!( res, $value.into() )
    }) ;
    ( bool $model:expr => $expr:expr ) => ({
      let res = $expr.eval(& $model).unwrap().to_bool().unwrap().unwrap() ;
      println!(
        "{} evaluated with {} is {}, expecting true", $expr, $model, res
      ) ;
      assert!( res )
    }) ;
    ( bool not $model:expr => $expr:expr ) => ({
      let res = $expr.eval(& $model).unwrap().to_bool().unwrap().unwrap() ;
      println!(
        "{} evaluated with {} is {}, expecting false", $expr, $model, res
      ) ;
      assert!( ! res )
    }) ;
  }
}