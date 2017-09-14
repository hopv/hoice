#![doc = r#"Profiling stuff.

In `bench` mode, `Profiler` is a unit structure. Also, all macros are
deactivated, so all profiling is completely removed.
"#]

#[warn(unused_imports)]
use std::time::{ Instant, Duration } ;

use common::* ;

/// Extends duration with a pretty printing.
pub trait DurationExt {
  /// Nice string representation.
  fn to_str(& self) -> String ;
}
impl DurationExt for Duration {
  fn to_str(& self) -> String {
    format!("{}.{:0>9}", self.as_secs(), self.subsec_nanos())
  }
}

/// Profile Tree.
#[derive(PartialEq, Eq)]
pub struct ProfileTree {
  /// Duration stored at this level.
  duration: Option<Duration>,
  /// Sub-branches.
  branches: HashMap<& 'static str, ProfileTree>,
}
impl ProfileTree {
  /// Tree with nothing but the top level.
  pub fn top(top: Duration) -> Self {
    ProfileTree {
      duration: Some(top),
      branches: HashMap::new(),
    }
  }

  /// Empty tree, not visible outside.
  fn empty() -> Self {
    ProfileTree { duration: None, branches: HashMap::new() }
  }

  /// Forces a scope to be equal to the sum of its sub branches.
  ///
  /// Only legal if the scope exists and its duration is `None`.
  pub fn lift(& mut self, scope: Vec<& 'static str>) -> Res<()> {
    let mut current = self ;
    for scp in & scope {
      let tmp = current ;
      current = if let Some(current) = tmp.branches.get_mut(scp) {
        current
      } else { return Ok(()) }
    }
    let mut sum = Duration::from_secs(0) ;
    for (_, branch) in & current.branches {
      sum = sum + branch.duration.clone().unwrap_or( Duration::from_secs(0) )
    }
    if current.duration.is_some() {
      bail!( "trying to lift scope with existing duration {:?}", scope )
    }
    current.duration = Some(sum) ;
    Ok(())
  }

  /// Inserts something in the tree.
  pub fn insert(
    & mut self, scope: Vec<& 'static str>, duration: Duration
  ) {
    let (mut current, mut last_scope) = (self, "top") ;

    for scope in scope {
      let tmp = current ;
      current = tmp.branches.entry(scope).or_insert_with(
        || ProfileTree::empty()
      ) ;
      last_scope = scope
    }
    if current.duration.is_some() {
      panic!(
        "ProfileTree: trying to insert the same scope twice `{}`",
        conf.emph(last_scope)
      )
    }
    current.duration = Some(duration)
  }

  /// Iterator on the tree.
  ///
  /// Scopes are guaranteed to follow the topological order.
  pub fn iter<F>(& self, f: F)
  where F: Fn(& [& 'static str], & Duration, Duration) {
    if let Some(duration) = self.duration.as_ref() {
      let sub_duration = self.branches.iter().fold(
        Duration::from_secs(0),
        |acc, (_, time)| acc + time.duration.unwrap_or_else(
          || Duration::from_secs(0)
        )
      ) ;
      f(&[], duration, sub_duration)
    } else {
      panic!("ProfileTree: no top duration set but already iterating")
    }
    let mut stack: Vec< (_, Vec<_>) > = vec![
      ( vec![], self.branches.iter().map(|(s, p)| (*s, p)).collect() )
    ] ;

    while let Some( (scope, mut branches) ) = stack.pop() {
      if let Some( (s, profile) ) = branches.pop() {
        let mut this_scope = scope.clone() ;
        stack.push( (scope, branches) ) ;
        this_scope.push( s ) ;
        let sub_duration = profile.branches.iter().fold(
          Duration::from_secs(0),
          |acc, (_, time)| acc + time.duration.unwrap_or_else(
            || Duration::from_secs(0)
          )
        ) ;
        if let Some(duration) = profile.duration.as_ref() {
          f(& this_scope, duration, sub_duration)
        } else {
          let mut scope_str = "".to_string() ;
          for s in & this_scope {
            scope_str.push_str("::") ; scope_str.push_str(s)
          }
          warn!{
            "no duration for scope {}, setting to sum of branches",
            conf.emph(& scope_str)
          }
          f(& this_scope, & sub_duration, sub_duration.clone())
        }
        stack.push(
          (
            this_scope,
            profile.branches.iter().map(|(s, p)| (*s, p)).collect()
          )
        )
      }
    }
  }
}


/// Maps strings to counters.
pub type Stats = HashMap<String, usize> ;
/// Provides a debug print function.
pub trait CanPrint {
  /// Debug print (multi-line).
  fn print(& self) ;
}
impl CanPrint for Stats {
  fn print(& self) {
    for (stat, count) in self {
      let stat_len = ::std::cmp::min( 30, stat.len() ) ;
      println!(
        ";   {0: >1$}{2}: {3: >5}",
        "", 30 - stat_len, conf.emph(stat), count
      )
    }
  }
}
impl CanPrint for ProfileTree {
  fn print(& self) {
    self.iter(
      |scope, time, sub_time| if let Some(last) = scope.last() {
        println!(
          "; {0: >1$}|- {2}s {3}{4}", "", 2 * scope.len(), time.to_str(), last,
          if sub_time != Duration::from_secs(0) {
            format!(" ({}s)", sub_time.to_str())
          } else {
            "".into()
          }
        )
      } else {
        println!(
          "; total {}s{}", time.to_str(),
          if sub_time != Duration::from_secs(0) {
            format!(" ({}s)", sub_time.to_str())
          } else {
            "".into()
          }
        )
      }
    )
  }
}


/// Profiling structure, only in `not(bench)`.
///
/// Maintains statistics using a hashmap indexed by strings.
///
/// Internally, the structures are wrapped in `RefCell`s so that mutation
/// does not require `& mut self`.
#[cfg( not(feature = "bench") )]
pub struct Profiler {
  /// String-indexed durations.
  map: ::std::cell::RefCell<
    HashMap< Vec<& 'static str>, (Option<Instant>, Duration)>
  >,
  /// Starting tick, for total time.
  start: Instant,
  /// Other statistics.
  stats: ::std::cell::RefCell< Stats >,
}
#[cfg(feature = "bench")]
pub struct Profiler ;
impl Profiler {
  /// Constructor.
  #[cfg( not(feature = "bench") )]
  pub fn new() -> Self {
    use std::cell::RefCell ;
    Profiler {
      map: RefCell::new( HashMap::new() ),
      start: Instant::now(),
      stats: RefCell::new( HashMap::new() ),
    }
  }
  #[cfg(feature = "bench")]
  pub fn new() -> Self { Profiler }

  /// Acts on a statistic.
  #[cfg( not(feature = "bench") )]
  pub fn stat_do<F, S>(& self, stat: S, f: F)
  where F: Fn(usize) -> usize, S: Into<String> {
    let stat = stat.into() ;
    let mut map = self.stats.borrow_mut() ;
    let val = map.get(& stat).map(|n| * n).unwrap_or(0) ;
    let _ = map.insert(stat, f(val)) ;
    ()
  }

  /// Ticks.
  #[cfg( not(feature = "bench") )]
  pub fn tick(& self, scope: Vec<& 'static str>) {
    if scope.is_empty() {
      panic!("Profile: can't use scope `total`")
    }
    let mut map = self.map.borrow_mut() ;
    let time = map.entry(scope).or_insert_with(
      || ( None, Duration::from_secs(0) )
    ) ;
    time.0 = Some( Instant::now() )
  }

  /// Registers the time since the last tick.
  ///
  /// Panics if there was no tick since the last time registration.
  #[cfg( not(feature = "bench") )]
  pub fn mark(& self, scope: Vec<& 'static str>) {
    if scope.is_empty() {
      panic!("Profile: can't use scope `total`")
    }
    let mut map = self.map.borrow_mut() ;
    if let Some(
      & mut (ref mut tick, ref mut sum)
    ) = map.get_mut(& scope) {
      let mut instant = None ;
      ::std::mem::swap(& mut instant, tick) ;
      if let Some(instant) = instant {
        * sum = (* sum) + Instant::now().duration_since(instant) ;
        * tick = None
      }
    } else {
      panic!("profiling: trying to mark the time without ticking first")
    }
  }

  /// Extracts the inner hash map.
  #[cfg( not(feature = "bench") )]
  pub fn extract(& self) -> HashMap< Vec<& 'static str>, Duration > {
    let mut map = HashMap::new() ;
    for (scope, & (ref tick, ref time)) in self.map.borrow().iter() {
      if tick.is_none() {
        let _ = map.insert(scope.clone(), * time) ;
      } else {
        panic!(
          "profiling: scope `{:?}` is still live but asked to extract", scope
        )
      }
    }
    let prev = map.insert(
      vec!["total"], Instant::now().duration_since(self.start)
    ) ;
    debug_assert!( prev.is_none() ) ;
    map
  }

  /// Extracts a profile tree.
  #[cfg( not(feature = "bench") )]
  pub fn extract_tree(self) -> (ProfileTree, Stats) {
    let mut tree = ProfileTree::top(
      Instant::now().duration_since(self.start)
    ) ;
    for (
      scope, & (ref should_be_none, ref time)
    ) in self.map.borrow().iter() {
      if should_be_none.is_some() {
        warn!(
          "Profile::extract_tree: \
          still have a live instant for {:?}", scope
        )
      }
      tree.insert( scope.clone(), * time )
    }
    ( tree, self.stats.into_inner() )
  }
}