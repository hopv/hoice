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


/// Logs at info level, using `info!`. Inactive in bench mode.
#[cfg(feature = "bench")]
macro_rules! log_info {
  ($($tt:tt)*) => (()) ;
}
#[cfg(not(feature = "bench"))]
macro_rules! log_info {
  ($($tt:tt)*) => ( info!{$($tt)*} ) ;
}


/// Logs at debug level. Inactive in bench mode.
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
#[cfg(debug_assertions)]
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
#[cfg(debug_assertions)]
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