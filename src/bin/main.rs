//! Entry point for the binary.

#[allow(unused_imports)]
#[macro_use]
extern crate human_panic ;
extern crate hoice ;

use hoice::common::* ;

#[cfg(not(debug_assertions))]
fn setup() {
  setup_panic!()
}
#[cfg(debug_assertions)]
fn setup() {
  ()
}

fn main() {
  setup() ;

  // Work and report error if any.
  if let Err(errs) = ::hoice::work() {
    let errs = match * errs.kind() {
      ErrorKind::Z3SpawnError => format!(
        "could not spawn z3 using command `{}`\n\
        make sure the z3 binary has that name and is in your path,\n\
        or specify a different z3 command with option `{}`",
        conf.emph( & conf.solver.conf().get_cmd() ),
        conf.emph( "--z3" )
      ).into(),
      _ => errs
    } ;
    print_err(errs) ;
    ::std::process::exit(2)
  } else {
    ::std::process::exit(0)
  }
}
