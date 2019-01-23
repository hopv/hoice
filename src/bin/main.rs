//! Entry point for the binary.

use hoice::common::*;

// /// Renices the process group.
// #[cfg(windows)]
// fn renice() {}

// /// Renices the process group.
// #[cfg(not(windows))]
// fn renice() {
//     let whole_group = ::libc::PRIO_PGRP;
//     let result = unsafe { ::libc::setpriority(whole_group, 0, 50) };
//     debug_assert_eq!(result, 0)
// }

/// Entry point.
fn main() {
    // renice();
    // Work and report error if any.
    if let Err(errs) = ::hoice::work() {
        let errs = match *errs.kind() {
            ErrorKind::Z3SpawnError => format!(
                "could not spawn z3 using command `{}`\n\
                 make sure the z3 binary has that name and is in your path,\n\
                 or specify a different z3 command with option `{}`",
                conf.emph(&conf.solver.conf().get_cmd()),
                conf.emph("--z3")
            )
            .into(),
            _ => errs,
        };
        print_err(&errs);
        ::std::process::exit(2)
    } else {
        ::std::process::exit(0)
    }
}
