//! Iterator over all the leaves in a term.

use std::slice::Iter;

use crate::common::*;

/// Iterator over all the leaves in a term.
pub struct LeafIter<'a> {
    /// Stack of subterms to look at.
    stack: Vec<Iter<'a, Term>>,
    /// Original starting term if this is the first iteration. None otherwise.
    term: Option<&'a RTerm>,
}

impl<'a> LeafIter<'a> {
    /// Constructor.
    pub fn of_rterm(term: &'a RTerm) -> Self {
        LeafIter {
            stack: Vec::with_capacity(11),
            term: Some(term),
        }
    }
}

impl<'a> Iterator for LeafIter<'a> {
    type Item = Either<(&'a Typ, VarIdx), &'a Val>;

    fn next(&mut self) -> Option<Self::Item> {
        'find_next: loop {
            let mut current = if let Some(term) = ::std::mem::replace(&mut self.term, None) {
                // First iteration.
                term
            } else {
                loop {
                    // Something in the stack?
                    if let Some(iter) = self.stack.last_mut() {
                        // Is there something in `iter`?
                        if let Some(term) = iter.next() {
                            // Use that
                            break term.get();
                        } else {
                            // Keep going, stack will be popped below.
                        }
                    } else {
                        return None;
                    }

                    // Only reachable if
                    // - stack is not empty, and
                    // there was nothing in the last element of the stack.
                    let iter = self.stack.pop();
                    debug_assert_eq! {
                      iter.map(
                        |mut iter| iter.next().map(
                          |_| "iter non-empty"
                        ).unwrap_or("ok")
                      ).unwrap_or("stack was empty") , "ok"
                    }
                }
            };

            use crate::term::RTerm::*;

            'go_down: loop {
                let next = match *current {
                    Var(ref typ, var) => Either::Left((typ, var)),
                    Cst(ref val) => Either::Right(val),

                    DTypSlc { ref term, .. }
                    | DTypTst { ref term, .. }
                    | CArray { ref term, .. } => {
                        current = term.get();
                        continue 'go_down;
                    }

                    App { ref args, .. } | Fun { ref args, .. } | DTypNew { ref args, .. } => {
                        self.stack.push(args.iter());
                        continue 'find_next;
                    }
                };

                return Some(next);
            }
        }
    }
}
