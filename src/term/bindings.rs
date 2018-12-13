//! Let bindings module.

use crate::common::*;

/// Stores let bindings.
///
/// Stores a sequence of let bindings. Each element of the sequence is a map from terms to a
/// variable. Each term map is such that all terms have exactly the same depth. The sequence is
/// ordered by increasing term depth.
///
/// This ensures that the sequence `[ map_i ]` is such that if `i < j`, no subterm of a term in
/// `map_i` can appear in `map_j`.
///
/// `Bindings` are constructed using `BindingBuilder`s.
#[derive(Debug, Clone)]
pub struct Bindings {
    first_fresh: VarIdx,
    bindings: Vec<TermMap<VarIdx>>,
}
impl Bindings {
    /// Bindings accessor.
    pub fn bindings(&self) -> &[TermMap<VarIdx>] {
        &self.bindings
    }

    /// True if the bindings are empty.
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }

    /// Writes a variable in the default format.
    pub fn write_var<W>(w: &mut W, var: VarIdx) -> IoRes<()>
    where
        W: Write,
    {
        VarIdx::write(w, var)
    }

    /// Writes the **opening** of the let-bindings.
    pub fn write_opening<W, WriteVar>(
        &self,
        w: &mut W,
        write_var: WriteVar,
        pref: &str,
    ) -> IoRes<()>
    where
        W: Write,
        WriteVar: Fn(&mut W, VarIdx) -> IoRes<()>,
    {
        // let write_var = &mut write_var;
        let first_fresh = self.first_fresh;
        for (current, term_map) in self.bindings.iter().enumerate() {
            writeln!(w, "{}(let", pref)?;
            write!(w, "{}  (", pref)?;
            for (term, var) in term_map {
                write!(w, " ({} ", var.default_str())?;
                term.write_with_raw(
                    w,
                    |w, var| {
                        if var >= first_fresh {
                            write!(w, "{}", var.default_str())
                        } else {
                            write_var(w, var)
                        }
                    },
                    Some(&self.bindings[0..current]),
                )?;
                write!(w, ")")?
            }
            writeln!(w, " )")?
        }

        Ok(())
    }

    /// Writes the **closing** part of the let-bindings.
    pub fn write_closing<W>(&self, w: &mut W, pref: &str) -> IoRes<()>
    where
        W: Write,
    {
        write!(w, "{}", pref)?;
        for _ in &self.bindings {
            write!(w, ")")?
        }
        writeln!(w)?;
        Ok(())
    }
}

/// Bindings builder.
///
/// Aggregates information about how many times a (sub)term appears in the term gradually fed to
/// it. This builder uses information from term hashconsing: all terms that do not have more than 2
/// references pointing to themselves are ignored.
///
/// This implies that the builder assumes all the terms it will work on are already constructed:
/// the haconsing reference counts are relevant for all the terms the bindings are for.
#[derive(Default)]
pub struct Builder {
    /// Maps term depth to a map from terms of that depth to the number of times they where
    /// encountered in the terms seen so far.
    depth_map: BTreeMap<usize, TermMap<usize>>,
}
impl Builder {
    /// Constructor.
    pub fn new() -> Self {
        Builder {
            depth_map: BTreeMap::new(),
        }
    }

    /// Builds bindings from the information it accumulated so far.
    pub fn build(mut self, mut fresh: VarIdx) -> Option<Bindings> {
        let first_fresh = fresh;
        let mut empty = 0;
        for term_map in self.depth_map.values_mut() {
            term_map.retain(|_, count| *count > 2);
            if term_map.is_empty() {
                empty += 1
            }
        }

        if empty == self.depth_map.len() {
            return None;
        }

        let mut bindings = Vec::with_capacity(self.depth_map.len() - empty);

        for (_depth, term_map) in self.depth_map {
            if term_map.is_empty() {
                continue;
            }

            let mut nu_term_map = TermMap::new();
            for (term, _) in term_map {
                debug_assert_eq! { term.depth(), _depth }
                let prev = nu_term_map.insert(term, fresh);
                debug_assert! { prev.is_none() }
                fresh.inc()
            }

            bindings.push(nu_term_map)
        }

        Some(Bindings {
            first_fresh,
            bindings,
        })
    }

    /// Scans a term to the builder.
    pub fn scan_term(mut self, term: &Term) -> Self {
        term.iter(|term| {
            let term = term.to_hcons();
            if term.arc_count() > 1 && term.depth() > 1 {
                let count = self
                    .depth_map
                    .entry(term.depth())
                    .or_insert_with(TermMap::new)
                    .entry(term)
                    .or_insert(0);
                *count += 1
            }
        });
        self
    }

    /// Scans some terms to the builder.
    pub fn scan_terms<'a, Terms>(mut self, terms: Terms) -> Self
    where
        Terms: IntoIterator<Item = &'a Term>,
    {
        for term in terms {
            self = self.scan_term(term)
        }
        self
    }

    /// Scans some predicate applications to the builder.
    pub fn scan_pred_apps(mut self, apps: &PredApps) -> Self {
        for argss in apps.values() {
            for args in argss {
                self = self.scan_terms(args.iter())
            }
        }
        self
    }

    /// Scans an optional predicate application to the builder.
    pub fn scan_pred_app(mut self, app: Option<(PrdIdx, &VarTerms)>) -> Self {
        if let Some((_, args)) = app.as_ref() {
            self = self.scan_terms(args.iter())
        }
        self
    }

    /// Scans only the lhs terms of a clause.
    pub fn scan_clause_lhs_terms(self, clause: &Clause) -> Self {
        self.scan_terms(clause.lhs_terms())
    }

    /// Scans a clause.
    pub fn scan_clause(self, clause: &Clause) -> Self {
        self.scan_clause_lhs_terms(clause)
            .scan_pred_apps(clause.lhs_preds())
            .scan_pred_app(clause.rhs())
    }
}
