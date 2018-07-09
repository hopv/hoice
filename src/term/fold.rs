//! Types for folding over terms.

use common::* ;

use std::slice::Iter ;

/// Fold info for terms.
enum FoldInfo<'a, Info> {
  /// Constant array.
  Arr {
    /// Type.
    typ: & 'a Typ,
  },

  /// Operator application.
  App {
    /// Type.
    typ: & 'a Typ,
    /// Operator.
    op: Op,
    /// Info already processed.
    lft_args: Vec<Info>,
    /// Kids left to process.
    rgt_args: Iter<'a, Term>,
  },

  /// Datatype constructor.
  New {
    /// Type of the application.
    typ: & 'a Typ,
    /// Name of the constructor.
    name: & 'a String,
    /// Kids already processed.
    lft_args: Vec<Info>,
    /// Kids left to process.
    rgt_args: Iter<'a, Term>,
  },

  /// Datatype selector.
  Sel {
    /// Type.
    typ: & 'a Typ,
    /// Name.
    name: & 'a String,
  },
}


/// Folds over a term.
///
/// Early returns **iff** any a call to one of the input functions returns an
/// error.
///
/// # Type parameters
///
/// - `Info`: information extracted by the folding process
/// - `VarF`: will run on variables
/// - `CstF`: will run on constants
/// - `AppF`: will run on the result of folding on operator applications
/// - `ArrF`: will run on the result of folding on arrays
/// - `NewF`: will run on the result of folding on datatype constructors
/// - `SlcF`: will run on the result of folding on datatype selectors
pub fn fold_res<Info, VarF, CstF, AppF, ArrF, NewF, SlcF>(
  term: & RTerm,
  varf: VarF, cstf: CstF,
  appf: AppF, arrf: ArrF,
  newf: NewF, slcf: SlcF,
) -> Res<Info>
where
VarF: FnMut(& Typ, VarIdx) -> Res<Info>,
CstF: FnMut(& Val) -> Res<Info>,
AppF: FnMut(& Typ, Op, Vec<Info>) -> Res<Info>,
ArrF: FnMut(& Typ, Info) -> Res<Info>,
NewF: FnMut(& Typ, & String, Vec<Info>) -> Res<Info>,
SlcF: FnMut(& Typ, & String, Info) -> Res<Info>, {
  fold_custom_res(term, varf, cstf, appf, arrf, newf, slcf)
}


/// Folds over a term.
///
/// # Type parameters
///
/// - `Info`: information extracted by the folding process
/// - `VarF`: will run on variables
/// - `CstF`: will run on constants
/// - `AppF`: will run on the result of folding on operator applications
/// - `ArrF`: will run on the result of folding on arrays
/// - `NewF`: will run on the result of folding on datatype constructors
/// - `SlcF`: will run on the result of folding on datatype selectors
pub fn fold<Info, VarF, CstF, AppF, ArrF, NewF, SlcF>(
  term: & RTerm,
  mut varf: VarF, mut cstf: CstF,
  mut appf: AppF, mut arrf: ArrF,
  mut newf: NewF, mut slcf: SlcF,
) -> Info
where
VarF: FnMut(& Typ, VarIdx) -> Info,
CstF: FnMut(& Val) -> Info,
AppF: FnMut(& Typ, Op, Vec<Info>) -> Info,
ArrF: FnMut(& Typ, Info) -> Info,
NewF: FnMut(& Typ, & String, Vec<Info>) -> Info,
SlcF: FnMut(& Typ, & String, Info) -> Info, {
  fold_custom_res::< Info, (), _, _, _, _, _, _ >(
    term,
    |t,v| Ok( varf(t, v) ),
    |v| Ok( cstf(v) ),
    |t, o, i| Ok( appf(t, o, i) ),
    |t, i| Ok( arrf(t, i) ),
    |t, s, i| Ok( newf(t, s, i) ),
    |t, s, i| Ok( slcf(t, s, i) ),
  ).unwrap()
  //^^^^^^~~~~ this unwrap is proved safe trivially.
}


/// Folds over a term.
///
/// This function returns an error **iff** one of the function provided returns
/// one.
///
/// # Type parameters
///
/// - `Info`: information extracted by the folding process
/// - `E`: type of errors (for early returns)
/// - `VarF`: will run on variables
/// - `CstF`: will run on constants
/// - `AppF`: will run on the result of folding on operator applications
/// - `ArrF`: will run on the result of folding on arrays
/// - `NewF`: will run on the result of folding on datatype constructors
/// - `SlcF`: will run on the result of folding on datatype selectors
pub fn fold_custom_res<Info, E, VarF, CstF, AppF, ArrF, NewF, SlcF>(
  term: & RTerm,
  mut varf: VarF, mut cstf: CstF,
  mut appf: AppF, mut arrf: ArrF,
  mut newf: NewF, mut slcf: SlcF,
) -> Result<Info, E>
where
VarF: FnMut(& Typ, VarIdx) -> Result<Info, E>,
CstF: FnMut(& Val) -> Result<Info, E>,
AppF: FnMut(& Typ, Op, Vec<Info>) -> Result<Info, E>,
ArrF: FnMut(& Typ, Info) -> Result<Info, E>,
NewF: FnMut(& Typ, & String, Vec<Info>) -> Result<Info, E>,
SlcF: FnMut(& Typ, & String, Info) -> Result<Info, E>, {
  use term::RTerm ;

  // Stack of stuff to zip on.
  let mut stack: Vec< FoldInfo<Info> > = Vec::with_capacity(11) ;

  // Term we're currently going into.
  let mut curr = term ;

  'go_down: loop {

    // Retrieve info for `curr` if it's a leaf. Keep going down otherwise.
    let mut info = match * curr {

      // Leaves (there's one more case: nullary datatype constructors, handled
      // below).

      RTerm::Var(ref typ, idx) => varf(typ, idx) ?,

      RTerm::Cst(ref val) => cstf(val) ?,

      // Not a leaf, we're going into their kids and updating the stack.

      RTerm::CArray { ref typ, ref term } => {
        curr = term ;
        stack.push( FoldInfo::Arr { typ } ) ;
        continue 'go_down
      },

      RTerm::App { ref typ, op, ref args } => {
        let lft_args = Vec::with_capacity( args.len() ) ;
        let mut rgt_args = args.iter() ;

        curr = rgt_args.next().expect(
          "illegal nullary operator application"
        ) ;

        stack.push(
          FoldInfo::App { typ, op, lft_args, rgt_args }
        ) ;

        continue 'go_down
      },

      RTerm::DTypNew { ref typ, ref name, ref args } => {
        let lft_args = Vec::with_capacity( args.len() ) ;
        let mut rgt_args = args.iter() ;

        if let Some(term) = rgt_args.next() {
          // Not a nullary constructor, go down.
          curr = term ;
          stack.push(
            FoldInfo::New { typ, name, lft_args, rgt_args }
          ) ;

          continue 'go_down

        } else {
          // Nullary constructor, retrieve info.
          newf(typ, name, vec![]) ?
        }
      },

      RTerm::DTypSlc { ref typ, ref name, ref term } => {
        curr = term ;
        stack.push(
          FoldInfo::Sel { typ, name }
        ) ;

        continue 'go_down
      },

      RTerm::Fun { ref typ, ref name, ref args } => unimplemented!(),

    } ;


    // We have the info, time to go up.
    'go_up: loop {

      match stack.pop() {

        // If none, we're done, the current info is for the original term.
        None => return Ok(info),

        // Array, current info is for the default value.
        Some(
          FoldInfo::Arr { typ }
        ) => {
          // Update info and keep going up.
          info = arrf(typ, info) ? ;
          continue 'go_up
        },

        // Operator application, info is for the kid between `lft_args` and
        // `rgt_args`.
        Some(
          FoldInfo::App { typ, op, mut lft_args, mut rgt_args }
        ) => {

          lft_args.push(info) ;

          // Are we done with this application?
          if let Some(term) = rgt_args.next() {
            // Let's go down in `term`.
            curr = term ;
            // Don't forget to push back the zip info in the stack.
            stack.push(
              FoldInfo::App { typ, op, lft_args, rgt_args }
            ) ;
            // Go down.
            continue 'go_down

          } else {
            // No more term to go down into. Update info and go up.
            info = appf(typ, op, lft_args) ? ;
            continue 'go_up
          }

        },

        // Datatype constructor, info is for the kid between `lft_args` and
        // `rgt_args`.
        Some(
          FoldInfo::New { typ, name, mut lft_args, mut rgt_args }
        ) => {

          lft_args.push(info) ;

          // Are we done with this constructor?
          if let Some(term) = rgt_args.next() {
            // Let's go down in `term`.
            curr = term ;
            // Don't forget to push back the zip info in the stack.
            stack.push(
              FoldInfo::New { typ, name, lft_args, rgt_args }
            ) ;
            // Go down.
            continue 'go_down

          } else {
            // No more term to go down into. Update info and go up.
            info = newf(typ, name, lft_args) ? ;
            continue 'go_up
          }

        },

        // Datatype selector, info is for the subterm.
        Some(
          FoldInfo::Sel { typ, name }
        ) => {
          // Update info and go up.
          info = slcf(typ, name, info) ? ;
          continue 'go_up
        },

      }

    }

  }
}
