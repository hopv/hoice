//! Profiling stuff.
//!
//! In `bench` mode, [`Profiler`][profiler] is a unit structure. Also, all
//! macros are deactivated, so all profiling is completely removed.
//!
//! [profiler]: struct.Profiler.html
//! (Profiler type)

#[allow(unused_imports)]
use std::time::{Duration, Instant};

use crate::common::*;

/// Extends duration with a pretty printing.
pub trait DurationExt {
    /// Nice string representation.
    fn to_str(&self) -> String;
}
impl DurationExt for Duration {
    fn to_str(&self) -> String {
        format!("{}.{:0>9}", self.as_secs(), self.subsec_nanos())
    }
}

/// Profile Tree.
#[derive(PartialEq, Eq)]
pub struct ProfileTree {
    /// Duration stored at this level.
    duration: Option<Duration>,
    /// Sub-branches.
    branches: BTreeMap<&'static str, ProfileTree>,
}
impl ProfileTree {
    /// Tree with nothing but the top level.
    pub fn top(top: Duration) -> Self {
        ProfileTree {
            duration: Some(top),
            branches: BTreeMap::new(),
        }
    }

    /// Empty tree, not visible outside.
    fn empty() -> Self {
        ProfileTree {
            duration: None,
            branches: BTreeMap::new(),
        }
    }

    /// Debug printing (multi-line).
    #[cfg(feature = "bench")]
    #[allow(dead_code)]
    fn print<S>(&self, _: S, _: &[&'static str]) {}
    #[cfg(not(feature = "bench"))]
    #[cfg_attr(feature = "cargo-clippy", allow(print_literal))]
    fn print<S>(&self, pref: S, set_sum: &[&'static str])
    where
        S: Into<String>,
    {
        let pref = pref.into();
        self.fold(
            None,
            |prev, scope, time, sub_time| {
                if let Some(last) = scope.last() {
                    debug_assert! { ! scope.is_empty() }
                    let art = match prev {
                        Some(n) if n < scope.len() => "\\",
                        Some(_) | None => "|",
                    };
                    println!(
                        "; {5}{0: >1$}{6}- {2}s {3}{4}",
                        "",
                        // Can't be negative because `scope` contains `last`.
                        scope.len() - 1,
                        time.to_str(),
                        last,
                        if sub_time != Duration::from_secs(0) {
                            format!(" ({}s)", sub_time.to_str())
                        } else {
                            "".into()
                        },
                        pref,
                        art
                    );
                    Some(scope.len())
                } else {
                    println!(
                        "; {}{} {}s{}",
                        pref,
                        conf.happy("total"),
                        time.to_str(),
                        if sub_time != Duration::from_secs(0) {
                            format!(" ({}s)", sub_time.to_str())
                        } else {
                            "".into()
                        }
                    );
                    None
                }
            },
            set_sum,
        );
    }

    /// Inserts something in the tree.
    pub fn insert(&mut self, scope: Vec<&'static str>, duration: Duration) {
        let (mut current, mut last_scope) = (self, "top");

        for scope in scope {
            let tmp = current;
            current = tmp.branches.entry(scope).or_insert_with(ProfileTree::empty);
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
    pub fn fold<F, T>(&self, init: T, f: F, set_sum: &[&'static str])
    where
        F: Fn(T, &[&'static str], &Duration, Duration) -> T,
    {
        let mut prev = init;
        if let Some(duration) = self.duration.as_ref() {
            let sub_duration = self
                .branches
                .iter()
                .fold(Duration::from_secs(0), |acc, (_, time)| {
                    acc + time.duration.unwrap_or_else(|| Duration::from_secs(0))
                });
            prev = f(prev, &[], duration, sub_duration)
        } else {
            panic!("ProfileTree: no top duration set but already iterating")
        }
        let mut stack: Vec<(_, Vec<_>)> =
            vec![(vec![], self.branches.iter().map(|(s, p)| (*s, p)).collect())];

        while let Some((scope, mut branches)) = stack.pop() {
            if let Some((s, profile)) = branches.pop() {
                let mut this_scope = scope.clone();
                stack.push((scope, branches));
                this_scope.push(s);
                let sub_duration = profile
                    .branches
                    .iter()
                    .fold(Duration::from_secs(0), |acc, (_, time)| {
                        acc + time.duration.unwrap_or_else(|| Duration::from_secs(0))
                    });
                if let Some(duration) = profile.duration.as_ref() {
                    prev = f(prev, &this_scope, duration, sub_duration)
                } else {
                    if set_sum.iter().any(|scope| s == *scope) {
                        let mut scope_str = "".to_string();
                        for s in &this_scope {
                            scope_str.push_str("::");
                            scope_str.push_str(s)
                        }
                        warn! {
                          "no duration for scope {}, setting to sum of branches",
                          conf.emph(& scope_str)
                        }
                    }
                    prev = f(prev, &this_scope, &sub_duration, sub_duration)
                }
                stack.push((
                    this_scope,
                    profile.branches.iter().map(|(s, p)| (*s, p)).collect(),
                ))
            }
        }
    }
}

/// Maps strings to counters.
pub type Stats = BTreeMap<String, usize>;
/// Provides a debug print function.
pub trait CanPrint {
    /// True if at least one value is not `0`.
    fn has_non_zero(&self) -> bool;
    /// Debug print (multi-line).
    fn print<S>(&self, s: S)
    where
        S: Into<String>;
}
static STAT_LEN: usize = 29;
impl CanPrint for Stats {
    fn has_non_zero(&self) -> bool {
        self.values().any(|n| *n > 0)
    }
    #[cfg_attr(feature = "cargo-clippy", allow(print_literal))]
    fn print<S>(&self, pref: S)
    where
        S: Into<String>,
    {
        let pref = pref.into();
        let mut stats: Vec<_> = self.iter().collect();
        stats.sort_unstable();
        for (stat, count) in stats {
            if *count > 0 {
                let stat_len = ::std::cmp::min(STAT_LEN, stat.len());
                println!(
                    "; {4}  {0: >1$}{2}: {3: >5}",
                    "",
                    STAT_LEN - stat_len,
                    conf.emph(stat),
                    count,
                    pref
                )
            }
        }
    }
}

/// Maps scopes to
///
/// - a (start) instant option: `Some` if the scope is currently active, and
/// - a duration representing the total runtime of this scope.
pub type InstantMap = BTreeMap<Vec<&'static str>, (Option<Instant>, Duration)>;

// The following import is not used in bench mode.
#[allow(unused_imports)]
use std::cell::RefCell;

/// Profiling structure, only in `not(bench)`.
///
/// Maintains statistics using a hashmap indexed by strings.
///
/// Internally, the structures are wrapped in `RefCell`s so that mutation
/// does not require `& mut self`.
#[cfg(not(feature = "bench"))]
#[derive(Clone)]
pub struct Profiler {
    /// String-indexed durations.
    map: RefCell<InstantMap>,
    /// Starting tick, for total time.
    start: Instant,
    /// Other statistics.
    stats: RefCell<Stats>,
    /// Sub-profilers.
    subs: RefCell<Vec<(String, Profiler)>>,
    /// Other profilers.
    others: RefCell<Vec<(String, Profiler)>>,
}
#[cfg(feature = "bench")]
#[derive(Clone)]
pub struct Profiler;
impl Default for Profiler {
    fn default() -> Self {
        Self::new()
    }
}
impl Profiler {
    /// Constructor.
    #[cfg(not(feature = "bench"))]
    pub fn new() -> Self {
        Profiler {
            map: RefCell::new(InstantMap::new()),
            start: Instant::now(),
            stats: RefCell::new(Stats::new()),
            subs: RefCell::new(Vec::new()),
            others: RefCell::new(Vec::new()),
        }
    }
    #[cfg(feature = "bench")]
    pub fn new() -> Self {
        Profiler
    }

    /// Merges two profilers.
    #[cfg(feature = "bench")]
    pub fn merge(&mut self, _: Self) {}
    /// Merges two profilers.
    #[cfg(not(feature = "bench"))]
    pub fn merge(&mut self, other: Self) {
        let map = other.map.into_inner();
        let stats = other.stats.into_inner();
        let subs = other.subs.into_inner();
        for sub in subs {
            self.subs.get_mut().push(sub)
        }
        for (scope, (_, duration)) in map {
            self.map
                .get_mut()
                .entry(scope)
                .or_insert_with(|| (None, Duration::new(0, 0)))
                .1 += duration
        }
        for (scope, val) in stats {
            *self.stats.get_mut().entry(scope).or_insert_with(|| 0) += val
        }
    }

    /// Merges the durations of two profilers.
    #[cfg(feature = "bench")]
    pub fn merge_set(&mut self, _: Self) {}
    /// Merges the durations of two profilers and sets the stats.
    #[cfg(not(feature = "bench"))]
    pub fn merge_set(&mut self, other: Self) {
        let map = other.map.into_inner();
        let stats = other.stats.into_inner();
        let subs = other.subs.into_inner();
        for sub in subs {
            self.subs.get_mut().push(sub)
        }
        for (scope, (_, duration)) in map {
            self.map
                .get_mut()
                .entry(scope)
                .or_insert_with(|| (None, Duration::new(0, 0)))
                .1 += duration
        }
        for (scope, val) in stats {
            *self.stats.get_mut().entry(scope).or_insert_with(|| 0) = val
        }
    }

    /// Acts on a statistic.
    #[cfg(not(feature = "bench"))]
    pub fn stat_do<F, S>(&self, stat: S, f: F)
    where
        F: Fn(usize) -> usize,
        S: Into<String>,
    {
        let stat = stat.into();
        let mut map = self.stats.borrow_mut();
        let val = map.get(&stat).cloned().unwrap_or(0);
        let _ = map.insert(stat, f(val));
        ()
    }

    /// Ticks.
    #[cfg(not(feature = "bench"))]
    pub fn tick(&self, scope: Vec<&'static str>) {
        if scope.is_empty() {
            panic!("Profile: can't use scope `total`")
        }
        let mut map = self.map.borrow_mut();
        let time = map
            .entry(scope)
            .or_insert_with(|| (None, Duration::from_secs(0)));
        time.0 = Some(Instant::now())
    }

    /// Registers the time since the last tick.
    ///
    /// Panics if there was no tick since the last time registration.
    #[cfg(not(feature = "bench"))]
    #[cfg_attr(feature = "cargo-clippy", allow(needless_pass_by_value))]
    pub fn mark(&self, scope: Vec<&'static str>) {
        if scope.is_empty() {
            panic!("Profile: can't use scope `total`")
        }
        let mut map = self.map.borrow_mut();
        if let Some(&mut (ref mut tick, ref mut sum)) = map.get_mut(&scope) {
            let mut instant = None;
            ::std::mem::swap(&mut instant, tick);
            if let Some(instant) = instant {
                *sum += Instant::now().duration_since(instant);
                *tick = None
            }
        } else {
            panic!(
                "profiling: trying to mark the time for {:?} without ticking first",
                scope
            )
        }
    }

    /// Extracts the profile tree and the stats.
    #[cfg(not(feature = "bench"))]
    fn extract(self) -> (ProfileTree, Stats, Vec<(String, Profiler)>) {
        let mut tree = ProfileTree::top(Instant::now().duration_since(self.start));
        for (scope, &(ref should_be_none, ref time)) in self.map.borrow().iter() {
            if should_be_none.is_some() {
                warn!(
                    "Profile::extract_tree: \
                     still have a live instant for {:?}",
                    scope
                )
            }
            tree.insert(scope.clone(), *time)
        }
        (tree, self.stats.into_inner(), self.subs.into_inner())
    }

    /// Adds a sub-profiler.
    #[cfg(not(feature = "bench"))]
    pub fn add_sub<S: Into<String>>(&self, name: S, sub: Self) {
        self.subs.borrow_mut().push((name.into(), sub))
    }
    #[cfg(feature = "bench")]
    pub fn add_sub<S: Into<String>>(&self, _: S, _: Self) {}

    /// Adds an other (not a sub) profiler to this profiler.
    #[cfg(not(feature = "bench"))]
    pub fn drain_subs(&self) -> Vec<(String, Profiler)> {
        let mut res = vec![];
        ::std::mem::swap(&mut res, &mut *self.subs.borrow_mut());
        res
    }

    /// Adds an other (not a sub) profiler to this profiler.
    #[cfg(not(feature = "bench"))]
    pub fn add_other<S: Into<String>>(&self, name: S, other: Self) -> () {
        self.others.borrow_mut().push((name.into(), other))
    }
    #[cfg(feature = "bench")]
    pub fn add_other<S>(&self, _: S, _: Self) -> () {}

    /// Adds an other (not a sub) profiler to this profiler.
    #[cfg(not(feature = "bench"))]
    pub fn drain_others(&self) -> Vec<(String, Profiler)> {
        let mut res = vec![];
        ::std::mem::swap(&mut res, &mut *self.others.borrow_mut());
        res
    }

    /// Consumes and prints a profiler.
    ///
    /// - `set_sum` is a slice of scopes which have no duration and will be set
    ///   to the sum of their branches (without triggering a warning)
    #[cfg(not(feature = "bench"))]
    pub fn print<S1, S2>(self, name: S1, pref: S2, set_sum: &[&'static str])
    where
        S1: Into<String>,
        S2: Into<String>,
    {
        let name = name.into();
        let pref = pref.into();

        println!("; {}{} {}", pref, conf.emph(&name), conf.emph("{"));
        let sub_pref = format!("{}  ", pref);

        let (tree, stats, subs) = self.extract();
        tree.print(sub_pref.clone(), set_sum);
        if stats.has_non_zero() {
            println!("; {}{}:", sub_pref, conf.happy("metrics"));
            stats.print(format!("{}{} ", sub_pref, conf.happy("|")))
        }

        scoped! {
          for (sub_name, sub) in subs {
            println!("; ") ;
            sub.print(
              format!("{}/{}", name, sub_name), sub_pref.clone(), set_sum
            ) ;
          }
        }
        println!("; {}{}", pref, conf.emph("}"))
    }
}
