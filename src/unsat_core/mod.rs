/*! Unsat cores related types.

Unsat core extraction is a bit technical. It is made complex by preprocessing
which heavily modifies the clauses.

Some reconstruction is needed. To achieve this, when unsat core production is
active, we need to remember the original clauses and enough information about
the unsat result.

This information comes in two flavors, depending on how the unsat result was
obtained.




# Unsat by Preprocessing

When preprocessing discovers the instance is unsat, it is because a clause is
trivially false. That is, some clause `C`

```smt
(forall ( <vars> ) (=> <lhs> <rhs>) )
```

is such that

```smt
(exists ( <vars> ) (and <lhs> (not <rhs>)) )
```

(This means that there is no predicate application in the clause.)

In this case, the unsat information is a valuation for `<vars>` and the index
of the **original** clause `C_o`.

Note that preprocessing might have removed predicate applications from the
original clause (by inlining), and thus reconstruction might involve looking in
more clauses than just `C_o` to trace the unsatisfiability.





# Unsat by Learning

When learning discovers the instance is unsat, it is because a sample `(<pred>
<args>)` for predicate `<pred>` needs to be both true and false. These two
facts come in general from sample constraints (implications) forcing other
samples to be true or false, each coming from specific clauses.

In this case, reconstruction consists in retrieving values for the variables of
all the original clauses that gave rise to the sample constraints involved in
the unsat result.

Once we have this, we still need to check whether the original clauses mention
other predicate applications (removed by preprocessing). If there are such
applications, we need to trace these back too.

*/

use common::{
  *, data::sample::Sample
} ;



pub mod sample_graph ;



pub use self::sample_graph::SampleGraph ;


/// An unsat core.
///
/// Stores some valuations for the variables of the *original* clauses.
pub type UnsatCore = Vec<
  (ClsIdx, VarHMap<Val>)
> ;











/** Information produced by the teacher to explain an unsat result.

In addition to the dependencies between samples, contains a positive and a negative samples such that one subsumes the other.

There's three cases:

- non-partial case: both samples have to be the same

    ```js
    pos: (pred 7 42),
    neg: (pred 7 42),
    ```

- partial case:

    - `pos` subsumes `neg`

        ```js
        pos: (pred _ 42),
        neg: (pred 7 42),
        ```

    - `neg` subsumes `pos`

        ```js
        pos: (pred _ 42),
        neg: (pred _  _),
        ```
*/
pub struct TeacherCore {
  /// Positive sample.
  pub pos: Sample,
  /// Negative sample.
  pub neg: Sample,

  /// Sample dependencies.
  pub graph: SampleGraph,
}

impl TeacherCore {

  /// Constructor.
  ///
  /// # Panic
  ///
  /// If `pos` and `neg`
  ///
  /// - are about different predicates, or
  /// - are not related (one does not subsume the other)
  pub fn new(graph: SampleGraph, pos: Sample, neg: Sample) -> Self {
    use common::data::args::SubsumeExt ;

    if pos.pred != neg.pred {
      panic!(
        "trying to construct `TeacherCore` with illegal samples\n  \
        positive sample is about predicate #{}, but negative one is about #{}",
        pos.pred, neg.pred
      )
    } else if pos.args.compare( & neg.args ).is_none() {
      panic!(
        "trying to construct `TeacherCore` with illegal samples\n  \
        positive and negative sample are not related\n  \
        (one does not subsume the other)"
      )
    }

    TeacherCore { graph, pos, neg }
  }


  /// Extracts the unsat core.
  ///
  /// The unsat core returned is *w.r.t.* the sample dependencies. That is, in
  /// general some more work needs to be done to retrieve information about
  /// predicates that have been removed by preprocessing.
  ///
  /// The core should be *sorted*, meaning positive clauses should be first and
  /// their consequence (transitively) follow, leading to the final negative
  /// clause yielding the unsat result. **This is not a stable assumption to
  /// make about this function.**
  pub fn core(& self) -> UnsatCore {
    unimplemented!()
  }

}






/// Debug stuff.
impl TeacherCore {
  /// Prints the teacher core with a prefix.
  pub fn print(
    & self, pref: & str, instance: & Instance
  ) {
    self.write(& mut stdout(), pref, instance).unwrap()
  }

  /// Writes the teacher core with a prefix.
  pub fn write<W: Write>(
    & self, w: & mut W, pref: & str, instance: & Instance
  ) -> Res<()> {
    writeln!(w, "{}teacher core {{", pref) ? ;

    writeln!(
      w, "{}  pos: ({} {}),", pref, instance[self.pos.pred], self.pos.args
    ) ? ;
    writeln!(
      w, "{}  neg: ({} {}),", pref, instance[self.neg.pred], self.neg.args
    ) ? ;

    writeln!(w, "{}", pref) ? ;

    self.graph.write(w, & format!("{}  ", pref), instance) ? ;

    writeln!(w, "{}}}", pref) ? ;
    Ok(())
  }

}


// /// Unsat core information.
// pub struct UCore {
//   /// The original instance.
//   instance: Instance,
// }



