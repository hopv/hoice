//! Sample dependency tracking.

#![allow(dead_code)]

use std::borrow::Borrow;

use crate::{
    common::{
        // smt::FullParser as Parser,
        // var_to::vals::{ VarValsMap, VarValsSet },
        var_to::vals::VarValsMap,
        *,
    },
    unsat_core::*,
};

/// Maps term arguments to concrete ones.
pub type TArgMap = HConMap<VarTerms, VarVals>;
/// Maps term arguments to Origins.
pub type OTArgMap = HConMap<VarTerms, Vec<Origin>>;

/// An optional rhs.
pub type Rhs = Option<(PrdIdx, VarTerms, VarVals)>;

/// The origin of a sample is a clause and some samples for activating the rhs.
type Origin = (ClsIdx, PrdHMap<TArgMap>);

/// Polarity of a sample: positive or negative.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Polarity {
    /// Positive?
    pos: bool,
}
impl Polarity {
    /// Positive constructor.
    pub fn pos() -> Self {
        Polarity { pos: true }
    }
    /// Negative constructor.
    pub fn neg() -> Self {
        Polarity { pos: false }
    }

    /// True if the polarity is positive.
    pub fn is_pos(self) -> bool {
        self.pos
    }
}
mylib::impl_fmt! {
  Polarity(self, fmt) {
    fmt.write_str( if self.pos { "+" } else { "-" } )
  }
}

/// Known samples: positive or negative.
#[derive(Default)]
pub struct KnownSamples {
    /// Positive samples.
    pos: PrdHMap<VarValsMap<(VarTerms, Origin)>>,
    /// Negative samples.
    neg: PrdHMap<VarValsMap<(Rhs, Origin)>>,
}
impl KnownSamples {
    /// Constructor.
    pub fn new() -> Self {
        KnownSamples {
            pos: PrdHMap::new(),
            neg: PrdHMap::new(),
        }
    }

    /// Writes itself.
    pub fn write<W: Write>(&self, w: &mut W, pref: &str) -> Res<()> {
        writeln!(w, "{}pos {{", pref)?;
        for (pred, map) in &self.pos {
            for (args, &(_, (clause, ref lhs))) in map {
                write!(w, "{}  ({} {}) <=#{}=", pref, pred, args, clause)?;
                for (pred, argss) in lhs {
                    for (_, args) in argss {
                        write!(w, " ({} {})", pred, args)?
                    }
                }
                writeln!(w)?
            }
        }
        writeln!(w, "{}}}", pref)?;
        writeln!(w, "{}neg {{", pref)?;
        for (pred, map) in &self.neg {
            for (args, &(ref rhs, (clause, ref lhs))) in map {
                write!(w, "{}  ({} {}) from ", pref, pred, args)?;
                if let Some((pred, _, ref args)) = rhs {
                    write!(w, "({} {})", pred, args)?
                } else {
                    write!(w, "false")?
                }
                write!(w, " <=#{}=", clause)?;
                for (pred, argss) in lhs {
                    for (_, args) in argss {
                        write!(w, " ({} {})", pred, args)?
                    }
                }
                writeln!(w)?
            }
        }
        writeln!(w, "{}}}", pref)?;
        Ok(())
    }

    /// Number of positive samples of a predicate.
    pub fn pos_len<P: Borrow<PrdIdx>>(&self, pred: P) -> usize {
        self.pos
            .get(pred.borrow())
            .map(|args| args.len())
            .unwrap_or(0)
    }
    /// Number of negative samples of a predicate.
    pub fn neg_len<P: Borrow<PrdIdx>>(&self, pred: P) -> usize {
        self.neg
            .get(pred.borrow())
            .map(|args| args.len())
            .unwrap_or(0)
    }

    /// Gets the origin of a positive sample.
    pub fn get_pos<P: Borrow<PrdIdx>>(
        &self,
        pred: P,
        args: &VarVals,
    ) -> Option<&(VarTerms, Origin)> {
        self.pos.get(pred.borrow()).and_then(|map| map.get(args))
    }
    /// True if the sample is known to be positive.
    pub fn is_pos<P: Borrow<PrdIdx>>(&self, pred: P, args: &VarVals) -> bool {
        self.get_pos(pred, args).is_some()
    }

    /// Gets the origin of a negative sample.
    pub fn get_neg<P: Borrow<PrdIdx>>(&self, pred: P, args: &VarVals) -> Option<&(Rhs, Origin)> {
        self.neg.get(pred.borrow()).and_then(|map| map.get(args))
    }
    /// True if the sample is known to be negative.
    pub fn is_neg<P: Borrow<PrdIdx>>(&self, pred: P, args: &VarVals) -> bool {
        self.get_neg(pred, args).is_some()
    }

    /// Gets the orign of a sample.
    pub fn get<P: Borrow<PrdIdx>>(
        &self,
        polarity: Polarity,
        pred: P,
        args: &VarVals,
    ) -> Option<(Rhs, Origin)> {
        if polarity.is_pos() {
            self.get_pos(pred.borrow(), args)
                .map(|&(ref fargs, ref origin)| {
                    (
                        Some((*pred.borrow(), fargs.clone(), args.clone())),
                        origin.clone(),
                    )
                })
        } else {
            self.get_neg(pred, args)
                .map(|(rhs, origin)| (rhs.clone(), origin.clone()))
        }
    }

    /// Registers a positive sample.
    ///
    /// Returns a sample related to this one but registered negative if any.
    ///
    /// If the sample is already registered as positive, overwrites the old
    /// origin.
    pub fn add_pos(
        &mut self,
        pred: PrdIdx,
        fargs: VarTerms,
        args: VarVals,
        origin: Origin,
    ) -> Option<VarVals> {
        let res = self
            .neg
            .get(&pred)
            .and_then(|map| map.keys().find(|other| other.is_related_to(&args)))
            .cloned();

        self.pos
            .entry(pred)
            .or_insert_with(VarValsMap::new)
            .insert(args, (fargs, origin));

        res
    }

    /// Registers a negative sample.
    ///
    /// Returns a sample related to this one but registered positive if any.
    ///
    /// If the sample is already registered as negative, overwrites the old
    /// origin.
    pub fn add_neg(
        &mut self,
        pred: PrdIdx,
        args: VarVals,
        rhs: Rhs,
        origin: Origin,
    ) -> Option<VarVals> {
        let res = self
            .pos
            .get(&pred)
            .and_then(|map| map.keys().find(|other| other.is_related_to(&args)))
            .cloned();

        self.neg
            .entry(pred)
            .or_insert_with(VarValsMap::new)
            .insert(args, (rhs, origin));

        res
    }

    pub fn update(
        &mut self,
        rhs: Option<(PrdIdx, &VarTerms, &VarVals)>,
        lhs: &PrdHMap<TArgMap>,
        clause: ClsIdx,
    ) -> Either<Option<bool>, (PrdIdx, VarVals, VarVals)> {
        macro_rules! done {
            (trivial) => {{
                return Either::Left(None);
            }};
            (changed) => {{
                return Either::Left(Some(true));
            }};
            (not changed) => {{
                return Either::Left(Some(false));
            }};
            (adding pos $pred:expr, $fargs:expr, $args:expr, $origin:expr) => {{
                if let Some(neg) =
                    self.add_pos($pred, $fargs.clone(), $args.clone(), $origin.clone())
                {
                    done!(contradiction $pred, $args.clone(), neg.clone())
                } else {
                    done!(changed)
                }
            }};
            (adding neg $pred:expr, $args:expr, $rhs:expr, $origin:expr) => {{
                if let Some(pos) = self.add_neg($pred, $args.clone(), $rhs, $origin.clone()) {
                    done!(contradiction $pred, pos.clone(), $args.clone())
                } else {
                    done!(changed)
                }
            }};
            (contradiction $pred:expr, $pos:expr, $neg:expr) => {{
                return Either::Right(($pred, $pos.clone(), $neg.clone()));
            }};
        }

        let (mut lhs_pos, mut lhs_neg, mut lhs_unk) = (vec![], vec![], vec![]);

        let rhs_true = rhs.map(|(pred, fargs, args)| {
            (
                pred,
                fargs,
                args,
                if self.is_pos(pred, args) {
                    Some(true)
                } else if self.is_neg(pred, args) {
                    Some(false)
                } else {
                    None
                },
            )
        });

        for (pred, argss) in lhs {
            for (_, args) in argss {
                if self.is_pos(pred, args) {
                    lhs_pos.push((pred, args))
                } else if self.is_neg(pred, args) {
                    lhs_neg.push((pred, args))
                } else {
                    lhs_unk.push((pred, args))
                }
            }
        }

        match (
      lhs_pos.is_empty(), lhs_neg.is_empty(), lhs_unk.len(), rhs_true
    ) {

      // At least on negative application in lhs.
      ( _, false, _, _ ) |
      // Rhs positive.
      ( _, _, _, Some((_, _, _, Some(true))) ) => done!(
        trivial
      ),

      // Whole lhs is positive, rhs negative (will trigger a contradiction).
      ( _, true, 0, Some((pred, fargs, args, Some(false))) ) => done!(
        adding pos pred, (* fargs), (* args), (clause, lhs.clone())
      ),

      // Whole lhs is positive, rhs unknown.
      ( _, true, 0, Some((pred, fargs, args, None)) ) => done!(
        adding pos pred, (* fargs), (* args), (clause, lhs.clone())
      ),

      // Whole lhs is positive, no rhs.
      ( _, true, 0, None ) => {
        // Add the first sample in the lhs (will trigger a contradiction).
        if let Some((pred, argss)) = lhs.iter().next() {
          if let Some((_, args)) = argss.iter().next() {
            done!(
              adding neg * pred, args, None, (clause, lhs.clone())
            )
          } else {
            unreachable!("empty argument sets are not allowed")
          }
        } else {
          unreachable!("empty clauses can only exist in preprocessing")
        }
      },

      // Whole lhs positive but one unknown, no rhs.
      ( _, true, 1, rhs @ None ) |
      // Whole lhs positive but one unknown, negative rhs.
      ( _, true, 1, rhs @ Some((_, _, _, Some(false))) ) => {
        // Unknown sample needs to be negative.
        let (pred, args) = lhs_unk.pop().unwrap() ;
        debug_assert_eq! { lhs_unk.len(), 0 }
        done!(
          adding neg
          * pred, args.clone(),
          rhs.map( |(pred, fargs, args, _)| (
            pred, (* fargs).clone(), (* args).clone()
          ) ),
          (clause, lhs.clone())
        )
      },

      // Unknown rhs and some unknown in lhs.
      ( _, _, unk_len, Some((_, _, _, None))) => {
        debug_assert! { unk_len > 0 }
        done!(not changed)
      },

      // Otherwise we have more than one unknown.
      (_, _, unk_len, rhs) => {
        debug_assert! {
          unk_len > 1 || rhs.map(
            |(_, _, _, val)| val.is_none()
          ).unwrap_or(false)
        }
        done!(not changed)
      }

    }
    }
}

/// A frame of a trace (explanation).
pub struct TraceFrame {
    /// Clause this result comes from.
    pub clause: ClsIdx,
    /// Values for the variables of the clauses that yield this frame.
    pub values: VarHMap<Val>,
    /// Positiveness flag.
    pub polarity: Polarity,
    /// Predicate.
    pub pred: PrdIdx,
    /// Arguments.
    pub args: VarVals,
    /// Optional rhs.
    pub rhs: Rhs,
    /// Antecedents.
    pub lhs: PrdHMap<TArgMap>,
}

impl TraceFrame {
    /// Constructor.
    pub fn new(
        clause: ClsIdx,
        values: VarHMap<Val>,
        polarity: Polarity,
        pred: PrdIdx,
        args: VarVals,
        rhs: Rhs,
        lhs: PrdHMap<TArgMap>,
    ) -> Self {
        TraceFrame {
            clause,
            values,
            polarity,
            pred,
            args,
            rhs,
            lhs,
        }
    }

    /// Writes itself as a derivation.
    pub fn write_as_derivation<W: Write>(
        &self,
        w: &mut W,
        pref: &str,
        instance: &Instance,
    ) -> Res<()> {
        let clause = &instance[self.clause];

        let original_clause_index = clause.from();

        let original_clause_name =
            if let Some(name) = instance.name_of_old_clause(original_clause_index) {
                name
            } else {
                return Ok(());
            };

        writeln!(w, "{}({}", pref, original_clause_name)?;

        writeln!(w, "{}  ( ; Values for the clause's variables:", pref)?;
        for (var, val) in &self.values {
            writeln!(
                w,
                "{}    (define-fun {} {} {})",
                pref, clause.vars[*var], clause.vars[*var].typ, val
            )?;
        }
        writeln!(w, "{}  )", pref)?;

        writeln!(
            w,
            "{}  (=> ; Concrete values for applications (non-ordered):",
            pref
        )?;
        if self.lhs.is_empty() {
            writeln!(w, "{}    true", pref)?
        } else {
            write!(w, "{}    (and", pref)?;
            for (pred, argss) in &self.lhs {
                for (_, args) in argss {
                    write!(w, " ({} {})", instance[*pred], args)?
                }
            }
            writeln!(w, ")")?
        }
        if let Some((pred, _, ref args)) = self.rhs {
            writeln!(w, "{}    ({} {})", pref, instance[pred], args)?
        } else {
            writeln!(w, "{}    false", pref)?
        }
        writeln!(w, "{}  )", pref)?;

        writeln!(w, "{}  ; Yields:", pref)?;
        write!(w, "{}  ", pref)?;
        let closing = if !self.polarity.is_pos() {
            write!(w, "(not ")?;
            ")"
        } else {
            ""
        };
        writeln!(w, "({} {}){}", instance[self.pred], self.args, closing)?;

        writeln!(w, "{})", pref)?;
        Ok(())
    }

    /// Writes itself.
    pub fn write<W: Write>(&self, w: &mut W, pref: &str, instance: &Instance) -> Res<()> {
        writeln!(
            w,
            "{}{} ({} {}) {{",
            pref,
            if self.polarity.is_pos() { "+" } else { "-" },
            instance[self.pred],
            self.args
        )?;

        if let Some(&(pred, _, ref args)) = self.rhs.as_ref() {
            write!(w, "{}  ({} {})", pref, instance[pred], args)?
        } else {
            write!(w, "{}  false", pref)?
        }

        write!(w, " <=#{}=", self.clause)?;

        for (&pred, argss) in &self.lhs {
            for (_, args) in argss {
                write!(w, " ({} {})", instance[pred], args)?
            }
        }
        writeln!(w)?;
        let clause = &instance[self.clause];
        write!(w, "{}  with", pref)?;
        for (var, val) in &self.values {
            write!(w, " {}: {},", clause.vars[*var], val)?
        }
        writeln!(w)?;

        writeln!(w, "{}}}", pref)?;
        Ok(())
    }
}

/// A trace: an explanation for the value of the last sample.
pub struct Trace {
    /// Frames of the trace.
    pub frames: Vec<TraceFrame>,
}
impl Trace {
    /// Constructor.
    pub fn new(frames: Vec<TraceFrame>) -> Self {
        Trace { frames }
    }

    /// Writes itself.
    pub fn write<W: Write>(&self, w: &mut W, pref: &str, instance: &Instance) -> Res<()> {
        for frame in &self.frames {
            frame.write(w, &format!("{}  ", pref), instance)?
        }
        Ok(())
    }

    /// Writes itself as a derivation.
    pub fn write_as_derivation<W: Write>(
        &self,
        w: &mut W,
        pref: &str,
        instance: &Instance,
    ) -> Res<()> {
        for frame in &self.frames {
            frame.write_as_derivation(w, pref, instance)?
        }
        Ok(())
    }

    /// Returns all clauses mentioned in this trace.
    pub fn all_clauses(&self, set: &mut ClsSet) {
        for frame in &self.frames {
            set.insert(frame.clause);
        }
    }
}

/// A proof: an explanation of an unsat result.
pub struct UnsatProof {
    /// Predicate.
    pred: PrdIdx,
    /// Positive sample.
    pos: VarVals,
    /// Negative sample.
    neg: VarVals,
    /// Derivation for `pos`.
    pos_trace: Trace,
    /// Derivation for `neg`.
    neg_trace: Trace,
}
impl UnsatProof {
    /// Retrieves the unsat core.
    pub fn core(&self) -> ClsSet {
        let mut res = ClsSet::new();
        self.pos_trace.all_clauses(&mut res);
        self.neg_trace.all_clauses(&mut res);
        res
    }

    /// Writes itself.
    pub fn write<W: Write>(&self, w: &mut W, instance: &Instance) -> Res<()> {
        writeln!(w, "(")?;

        writeln!(w, "  ; Contradiction:")?;
        writeln!(
            w,
            "  ( and ({} {}) (not ({} {})) )",
            instance[self.pred], self.pos, instance[self.pred], self.neg
        )?;

        writeln!(w)?;
        writeln!(
            w,
            "  ( ; Derivation for ({} {}):",
            instance[self.pred], self.pos
        )?;

        self.pos_trace.write_as_derivation(w, "    ", instance)?;

        writeln!(w, "  )")?;

        writeln!(w)?;
        writeln!(
            w,
            "  ( ; Derivation for (not ({} {})):",
            instance[self.pred], self.neg
        )?;

        self.neg_trace.write_as_derivation(w, "    ", instance)?;

        writeln!(w, "  )")?;

        write!(w, ")")?;

        Ok(())
    }
}

/** Stores the graph of dependencies between samples.

This is maintained by the teacher when unsat core production is active and is
returned in case of an unsat result. The graph allows to retrieve values for
the original clauses that explain why some sample needs to be both true and
false at the same time.
*/
#[derive(Clone, Debug, Default)]
pub struct SampleGraph {
    /// Maps samples to the clause and the samples for this clause they come
    /// from.
    graph: PrdHMap<VarValsMap<OTArgMap>>,
    /// Negative samples.
    neg: Vec<Origin>,
}

impl SampleGraph {
    /// Creates a new sample graph.
    pub fn new() -> Self {
        SampleGraph {
            graph: PrdHMap::new(),
            neg: vec![],
        }
    }

    /// Merges two graphs.
    pub fn merge(&mut self, other: Self) {
        let SampleGraph { graph, mut neg } = other;

        for (pred, map) in graph {
            let pred_target = self
                .graph
                .entry(pred)
                .or_insert_with(|| VarValsMap::with_capacity(map.len()));
            for (args, origins) in map {
                let target = pred_target
                    .entry(args)
                    .or_insert_with(|| OTArgMap::with_capacity(origins.len()));
                for (fargs, origins) in origins {
                    let target = target
                        .entry(fargs)
                        .or_insert_with(|| Vec::with_capacity(origins.len()));
                    for origin in origins {
                        if !target.contains(&origin) {
                            target.push(origin)
                        }
                    }
                }
            }
        }

        neg.retain(|origin| self.neg.iter().all(|o| o != origin));
        for origin in neg {
            self.neg.push(origin)
        }
    }

    /// Adds traceability for a sample.
    pub fn add(
        &mut self,
        prd: PrdIdx,
        fargs: VarTerms,
        args: VarVals,
        cls: ClsIdx,
        samples: PrdHMap<TArgMap>,
    ) {
        if_log! { @3
          log! { @3
            "adding origin for ({} {})", prd, args ;
            "from clause #{} {{", cls
          }
          for (pred, samples) in & samples {
            log! { @3 "  from predicate {}:", pred }
            for (_, sample) in samples {
              log! { @3 "    {}", sample }
            }
          }
          log! { @3 "}}" }
        }
        self.graph
            .entry(prd)
            .or_insert_with(VarValsMap::new)
            .entry(args)
            .or_insert_with(OTArgMap::new)
            .entry(fargs)
            .or_insert_with(|| vec![])
            .push((cls, samples))
    }

    /// Adds traceability for a negative sample.
    pub fn add_neg(&mut self, cls: ClsIdx, samples: PrdHMap<TArgMap>) {
        self.neg.push((cls, samples))
    }

    /// Searches for a contradiction in the graph.
    ///
    /// If a contradiction is detected, returns
    ///
    /// - the related positive and negative samples
    /// - known samples (pos/neg)
    fn find_contradiction(&mut self) -> Option<(PrdIdx, VarVals, VarVals, KnownSamples)> {
        // Known samples (positive/negative) and their relevant origin.
        let mut known = KnownSamples::new();
        // Fixed point flag.
        let mut fixed_point = false;

        // Stuff to remove from non-negative constraints.
        let mut to_rm_1 = vec![];

        let mut res = None;

        macro_rules! cleanup {
            () => {{
                for (pred, args) in to_rm_1.drain(0..) {
                    let rmed = self
                        .graph
                        .get_mut(&pred)
                        .map(|arg_map| arg_map.remove(&args));
                    debug_assert! { rmed.is_some() }
                }
                self.graph.retain(|_, arg_map| !arg_map.is_empty())
            }};
        }

        // Saturate the propagation mechanism.
        'saturate: while !fixed_point {
            fixed_point = true;

            for (pred, arg_map) in &self.graph {
                for (args, origins) in arg_map {
                    for (fargs, origins) in origins {
                        for &(clause, ref lhs) in origins {
                            match known.update(
                Some((* pred, fargs, args)), lhs, clause
              ) {
                // Used.
                Either::Left(changed @ Some(true)) |
                // Trivial.
                Either::Left(changed @ None) => {
                  if changed.is_some() {
                    fixed_point = false ;
                  }
                  to_rm_1.push((* pred, args.clone()))
                },

                // Nothing changed.
                Either::Left(Some(false)) => (),

                // Contradiction.
                Either::Right(c) => {
                  debug_assert! { res.is_none() }
                  res = Some(c) ;
                  break 'saturate
                },
              }
                        }
                    }
                }
            }

            let mut neg_cnt = 0;
            while neg_cnt < self.neg.len() {
                match known.update(
          None, & self.neg[neg_cnt].1, self.neg[neg_cnt].0
        ) {
          // Used.
          Either::Left(changed @ Some(true)) |
          // Trivial.
          Either::Left(changed @ None) => {
            if changed.is_some() {
              fixed_point = false ;
            }
            self.neg.swap_remove(neg_cnt) ;
          },

          // Nothing changed.
          Either::Left(Some(false)) => {
            neg_cnt += 1
          },

          // Contradiction.
          Either::Right(c) => {
            debug_assert! { res.is_none() }
            res = Some(c) ;
            break 'saturate
          },
        }
            }

            cleanup!()
        }

        res.map(|(pred, pos, neg)| (pred, pos, neg, known))
    }

    // /// Traces the origin of a sample.
    // fn trace<'a>(
    //   & 'a self,
    //   pred: PrdIdx, args: & VarVals,
    //   polarity: Polarity,
    //   known: & KnownSamples,
    //   solver: & mut Solver<Parser>,
    //   instance: & Instance,
    // ) -> Res<Trace> {

    //   // Samples for which we already have an explanation for.
    //   let mut explained = PrdHMap::<VarValsSet>::new() ;

    //   // Checks whether a sample is explained or inserts a sample in explained
    //   // samples.
    //   macro_rules! explained {
    //     // Checks whether a sample is already explained.
    //     (contains $pred:expr, $args:expr) => (
    //       explained.get(& $pred).map(
    //         |set| set.contains(& $args)
    //       ).unwrap_or(false)
    //     ) ;

    //     // Adds a sample as explained.
    //     (insert $pred:expr, $args:expr) => ({
    //       let is_new = explained.entry($pred).or_insert_with(
    //         VarValsSet::new
    //       ).insert($args) ;
    //       debug_assert! { is_new }
    //     }) ;
    //   }

    //   // Result: full trace of explanation.
    //   let mut res = vec![] ;

    //   // Stores the samples we need to explain.
    //   let mut to_explain = vec![ (polarity, pred, args.clone()) ] ;

    //   // Explain all samples.
    //   'all_samples: while let Some(
    //     (polarity, pred, args)
    //   ) = to_explain.pop() {

    //     // Already explained?
    //     if explained!(contains pred, & args) {
    //       continue 'all_samples
    //     }

    //     let (rhs, (clause, lhs)) = if let Some(origin) = known.get(
    //       polarity, pred, & args
    //     ) {
    //       origin
    //     } else {
    //       bail!("unable to explain why sample ({} {}) is positive", pred, args)
    //     } ;

    //     // Take care of the antecedents.
    //     for (pred, argss) in lhs.iter() {
    //       for (_, args) in argss {
    //         to_explain.push(
    //           (Polarity::pos(), * pred, args.clone())
    //         )
    //       }
    //     }

    //     let mut map = VarHMap::new() ;

    //     {
    //       use common::smt::{ SmtConj, EqConj } ;

    //       solver.comment(
    //         & format!("Working on clause #{}", clause)
    //       ) ? ;
    //       let clause = & instance[clause] ;

    //       solver.push(1) ? ;

    //       clause.declare(solver) ? ;

    //       let conj = SmtConj::new(clause.lhs_terms()) ;

    //       solver.assert(& conj) ? ;

    //       debug_assert_eq! { clause.lhs_preds().len(), lhs.len() }

    //       debug_assert! {
    //         lhs.iter().all(
    //           |(pred, argss)| clause.lhs_preds().iter().any(
    //             |(p, a)| p == pred && argss.len() == a.len() && argss.iter().all(
    //               |(args, _)| a.iter().any(
    //                 |a| a == args
    //               )
    //             )
    //           )
    //         )
    //       }

    //       for argss in lhs.values() {
    //         for (fargs, sample) in argss {
    //           let eq_conj = EqConj::new(fargs, sample) ;
    //           solver.assert(& eq_conj) ?
    //         }
    //       }

    //       if let Some((pred, ref fargs, ref args)) = rhs {
    //         debug_assert! {
    //           if let Some((p, fa)) = clause.rhs() {
    //             pred == p && fa == fargs
    //           } else {
    //             false
    //           }
    //         }
    //         let eq_conj = EqConj::new(fargs, args) ;
    //         solver.assert(& eq_conj) ?
    //       }

    //       if ! solver.check_sat() ? {
    //         bail!("error retrieving unsat core, trace is not feasible")
    //       }

    //       let model = solver.get_model() ? ;
    //       let model = Parser.fix_model(model) ? ;

    //       solver.pop(1) ? ;

    //       for (var, _, val) in model {
    //         let prev = map.insert(var, val) ;
    //         debug_assert_eq! { prev, None }
    //       }

    //     }

    //     // Append to result.
    //     res.push(
    //       TraceFrame::new(
    //         clause, map, polarity, pred, args.clone(), rhs, lhs
    //       )
    //     ) ;

    //     // Remember we explained this sample.
    //     explained! { insert pred, args }

    //   }

    //   res.reverse() ;

    //   Ok( Trace::new(res) )
    // }

    /// Extracts a proof for unsat.
    pub fn get_proof(&mut self, _instance: &Instance) -> Res<UnsatProof> {
        bail!("unimplemented");
        // let (
        //   pred, pos, neg, known
        // ) = if let Some(contradiction) = self.find_contradiction() {
        //   contradiction
        // } else {
        //   bail!("could not retrieve unsat result")
        // } ;

        // let mut solver = conf.solver.spawn(
        //   "core_extraction", Parser, & instance
        // ) ? ;
        // let pos_trace = self.trace(
        //   pred, & pos, Polarity::pos(), & known, & mut solver,
        //   instance
        // ) ? ;
        // let neg_trace = self.trace(
        //   pred, & neg, Polarity::neg(), & known, & mut solver,
        //   instance
        // ) ? ;

        // Ok(
        //   UnsatProof {
        //     pred, pos, neg, pos_trace, neg_trace
        //   }
        // )
    }

    /// Writes the sample graph with a prefix.
    pub fn write<W: Write>(&self, w: &mut W, pref: &str, instance: &Instance) -> IoRes<()> {
        writeln!(w, "{}sample graph {{", pref)?;

        for (pred, map) in &self.graph {
            writeln!(w, "{}  {}:", pref, instance[*pred])?;
            for (args, origins) in map {
                for origins in origins.values() {
                    for &(clause, ref apps) in origins {
                        write!(w, "{}    {}  <=#{}=", pref, args, clause)?;
                        if apps.is_empty() {
                            write!(w, "  true")?
                        } else {
                            for (pred, argss) in apps {
                                for args in argss.values() {
                                    write!(w, "  ({} {})", instance[*pred], args)?
                                }
                            }
                        }
                        writeln!(w)?
                    }
                }
            }
        }

        for (clause, ref apps) in &self.neg {
            write!(w, "{}  false  <=#{}=", pref, clause)?;
            if apps.is_empty() {
                write!(w, "  true")?
            } else {
                for (pred, argss) in apps {
                    for args in argss.values() {
                        write!(w, "  ({} {})", instance[*pred], args)?
                    }
                }
            }
            writeln!(w)?
        }

        writeln!(w, "{}}}", pref)
    }
}
