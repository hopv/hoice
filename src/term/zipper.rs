//! Types for zipping over terms.

use common::* ;

use std::slice::Iter ;

/// Zip info for terms.
enum ZipInfo<'a, Info> {
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
  }
}


/// Zips over a term.
///
/// Early returns **iff** any a call to one of the input functions returns an
/// error.
///
/// # Type parameters
///
/// - `Info`: information extracted by the zipping process
/// - `VarF`: will run on variables
/// - `CstF`: will run on constants
/// - `AppF`: will run on the result of zipping on operator applications
/// - `ArrF`: will run on the result of zipping on arrays
/// - `NewF`: will run on the result of zipping on datatype constructors
pub fn zip_res<Info, VarF, CstF, AppF, ArrF, NewF>(
  term: & RTerm, varf: VarF, cstf: CstF, appf: AppF, arrf: ArrF, newf: NewF
) -> Res<Info>
where
VarF: FnMut(& Typ, VarIdx) -> Res<Info>,
CstF: FnMut(& Val) -> Res<Info>,
AppF: FnMut(& Typ, Op, Vec<Info>) -> Res<Info>,
ArrF: FnMut(& Typ, Info) -> Res<Info>,
NewF: FnMut(& Typ, & String, Vec<Info>) -> Res<Info>, {
  zip_custom_res(term, varf, cstf, appf, arrf, newf)
}


/// Zips over a term.
///
/// # Type parameters
///
/// - `Info`: information extracted by the zipping process
/// - `VarF`: will run on variables
/// - `CstF`: will run on constants
/// - `AppF`: will run on the result of zipping on operator applications
/// - `ArrF`: will run on the result of zipping on arrays
/// - `NewF`: will run on the result of zipping on datatype constructors
pub fn zip<Info, VarF, CstF, AppF, ArrF, NewF>(
  term: & RTerm,
  mut varf: VarF, mut cstf: CstF, mut appf: AppF,
  mut arrf: ArrF, mut newf: NewF
) -> Info
where
VarF: FnMut(& Typ, VarIdx) -> Info,
CstF: FnMut(& Val) -> Info,
AppF: FnMut(& Typ, Op, Vec<Info>) -> Info,
ArrF: FnMut(& Typ, Info) -> Info,
NewF: FnMut(& Typ, & String, Vec<Info>) -> Info, {
  zip_custom_res::< Info, (), _, _, _, _, _ >(
    term,
    |t,v| Ok( varf(t, v) ),
    |v| Ok( cstf(v) ),
    |t, o, i| Ok( appf(t, o, i) ),
    |t, i| Ok( arrf(t, i) ),
    |t, s, i| Ok( newf(t, s, i) ),
  ).unwrap()
  //^^^^^^~~~~ this unwrap is proved safe trivially.
}


/// Zips over a term.
///
/// This function returns an error **iff** one of the function provided returns
/// one.
///
/// # Type parameters
///
/// - `Info`: information extracted by the zipping process
/// - `E`: type of errors (for early returns)
/// - `VarF`: will run on variables
/// - `CstF`: will run on constants
/// - `AppF`: will run on the result of zipping on operator applications
/// - `ArrF`: will run on the result of zipping on arrays
/// - `NewF`: will run on the result of zipping on datatype constructors
pub fn zip_custom_res<Info, E, VarF, CstF, AppF, ArrF, NewF>(
  term: & RTerm,
  mut varf: VarF, mut cstf: CstF, mut appf: AppF,
  mut arrf: ArrF, mut newf: NewF
) -> Result<Info, E>
where
VarF: FnMut(& Typ, VarIdx) -> Result<Info, E>,
CstF: FnMut(& Val) -> Result<Info, E>,
AppF: FnMut(& Typ, Op, Vec<Info>) -> Result<Info, E>,
ArrF: FnMut(& Typ, Info) -> Result<Info, E>,
NewF: FnMut(& Typ, & String, Vec<Info>) -> Result<Info, E>, {
  use term::RTerm ;

  // Stack of stuff to zip on.
  let mut stack: Vec< ZipInfo<Info> > = Vec::with_capacity(11) ;

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
        stack.push( ZipInfo::Arr { typ } ) ;
        continue 'go_down
      },

      RTerm::App { ref typ, op, ref args } => {
        let lft_args = Vec::with_capacity( args.len() ) ;
        let mut rgt_args = args.iter() ;

        curr = rgt_args.next().expect(
          "illegal nullary operator application"
        ) ;

        stack.push(
          ZipInfo::App { typ, op, lft_args, rgt_args }
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
            ZipInfo::New { typ, name, lft_args, rgt_args }
          ) ;

          continue 'go_down

        } else {
          // Nullary constructor, retrieve info.
          newf(typ, name, vec![]) ?
        }
      },

    } ;


    // We have the info, time to go up.
    'go_up: loop {

      match stack.pop() {

        // If none, we're done, the current info is for the original term.
        None => return Ok(info),

        // Array, current info is for the default value.
        Some(
          ZipInfo::Arr { typ }
        ) => {
          // Update info and keep going up.
          info = arrf(typ, info) ? ;
          continue 'go_up
        },

        // Operator application, info is for the kid between `lft_args` and
        // `rgt_args`.
        Some(
          ZipInfo::App { typ, op, mut lft_args, mut rgt_args }
        ) => {

          lft_args.push(info) ;

          // Are we done with this application?
          if let Some(term) = rgt_args.next() {
            // Let's go down in `term`.
            curr = term ;
            // Don't forget to push back the zip info in the stack.
            stack.push(
              ZipInfo::App { typ, op, lft_args, rgt_args }
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
          ZipInfo::New { typ, name, mut lft_args, mut rgt_args }
        ) => {

          lft_args.push(info) ;

          // Are we done with this constructor?
          if let Some(term) = rgt_args.next() {
            // Let's go down in `term`.
            curr = term ;
            // Don't forget to push back the zip info in the stack.
            stack.push(
              ZipInfo::New { typ, name, lft_args, rgt_args }
            ) ;
            // Go down.
            continue 'go_down

          } else {
            // No more term to go down into. Update info and go up.
            info = newf(typ, name, lft_args) ? ;
            continue 'go_up
          }

        },

      }

    }

  }
}
