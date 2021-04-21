//! [Hoice][hoice] is Horn clause solver based on the [ICE][ice] framework. The
//! original approach was modified to handle non-linear Horn clauses and
//! multi-predicates natively.
//!
//! [hoice]: https://github.com/hopv/hoice
//! (hoice repository on github)
//! [ice]: http://madhu.cs.illinois.edu/CAV14ice.pdf
//! (ICE paper PDF)

#![doc(test(attr(deny(warnings))))]
#![allow(non_upper_case_globals)]

// extern crate lazy_static;
// #[macro_use]
// extern crate mylib;
// #[macro_use]
// extern crate error_chain;
// #[macro_use]
// extern crate clap;
// extern crate ansi_term as ansi;
// #[macro_use]
// extern crate hashconsing;
// extern crate atty;
// extern crate either;
// extern crate libc;
// extern crate num;
// extern crate rand;
// extern crate rand_xorshift;
// extern crate rsmt2;

#[macro_use]
pub mod common;
pub mod check;
pub mod data;
pub mod dtyp;
pub mod errors;
pub mod fun;
pub mod info;
mod instance;
pub mod learning;
pub mod parse;
pub mod preproc;
pub mod split;
pub mod teacher;
pub mod term;
pub mod unsat_core;
pub mod val;
pub mod var_to;

use crate::common::*;
use crate::instance::Instance;

/// Parses command-line arguments and works.
pub fn work() -> Res<()> {
    // Reading from file?
    if let Some(file_path) = conf.in_file() {
        use std::fs::OpenOptions;

        // Are we in check mode?
        if let Some(output_file) = conf.check_file() {
            return check::do_it(file_path, output_file);
        }

        // Not in check mode, open file
        let file = OpenOptions::new()
            .read(true)
            .open(file_path)
            .chain_err(|| format!("while opening input file `{}`", conf.emph(file_path)))?;

        read_and_work(file, true, false, false)?;
        Ok(())
    } else {
        // Reading from stdin.

        let stdin = ::std::io::stdin();

        read_and_work(stdin, false, false, false)?;
        Ok(())
    }
}

/// Reads a script from a `Read`er and works.
///
/// Arguments:
///
/// - `file_input`: indicates whether we're reading from a file. If true, parse
///   errors will mention the line where the error occured.
///
/// - `stop_on_check`: forces the function to return once the first check is
///   complete. Only used in tests.
///
/// - `stop_on_err`: forces to stop at the first error. Only used in tests.
pub fn read_and_work<R: ::std::io::Read>(
    reader: R,
    file_input: bool,
    stop_on_check: bool,
    stop_on_err: bool,
) -> Res<(Option<ConjModel>, Instance)> {
    use crate::parse::{ItemRead, ParserCxt};

    let profiler = Profiler::new();

    let mut reader = ::std::io::BufReader::new(reader);
    // String buffer.
    let buf = &mut String::with_capacity(2000);
    // Parser context.
    let mut parser_cxt = ParserCxt::new();
    // Line offset of the parser.
    let mut line_off = 0;
    // Instance.
    let mut instance = Instance::new();
    // Current model.
    let mut model = None;
    // Any error encountered?
    // let mut error = false ;

    // Unsat core.
    //
    // - `None`             if not unsat
    let mut unsat = None;

    // Original instance.
    let mut original_instance = None;

    'parse_work: loop {
        use crate::parse::Parsed;

        profile! { |profiler| tick "parsing" }

        buf.clear();
        let lines_parsed = reader.read_item(buf).chain_err(|| "while reading input")?;

        if lines_parsed == 0 && file_input {
            profile! { |profiler| mark "parsing" }
            break 'parse_work;
        }
        let parse_res = parser_cxt
            .parser(&buf, line_off, &profiler)
            .parse(&mut instance);

        line_off += lines_parsed;

        let parse_res = match parse_res {
            Ok(res) => res,
            Err(e) => {
                if stop_on_err {
                    return Err(e);
                }
                // error = true ;
                print_err(&e);
                profile! { |profiler| mark "parsing" }
                continue 'parse_work;
            }
        };

        profile! { |profiler| mark "parsing" }

        match parse_res {
            // Check-sat on unsat instance?
            Parsed::CheckSat if unsat.is_some() => {
                println!("unsat");

                if stop_on_check {
                    return Ok((model, instance));
                }
            }

            // Check-sat, start class.
            Parsed::CheckSat => {
                if instance.proofs() {
                    let mut old = instance.clone();
                    old.finalize()
                        .chain_err(|| "while finalizing original instance")?;
                    original_instance = Some(old)
                }
                log! { @info "Running top pre-processing" }

                let preproc_profiler = Profiler::new();
                match profile! {
                  |profiler| wrap {
                    preproc::work(& mut instance, & preproc_profiler)
                  } "top preproc"
                } {
                    Ok(()) => (),
                    Err(e) => {
                        if e.is_timeout() {
                            println!("timeout");
                            print_stats("top", profiler);
                            ::std::process::exit(0)
                        } else if e.is_unknown() {
                            println!("unknown");
                            continue;
                        } else if e.is_unsat() {
                            unsat = Some(unsat_core::UnsatRes::None)
                        } else {
                            bail!(e)
                        }
                    }
                }
                print_stats("top preproc", preproc_profiler);

                model = if let (false, Some(maybe_model)) =
                    (instance.no_simplify_clauses(), instance.is_trivial_conj()?)
                {
                    // Pre-processing already decided satisfiability.
                    log! { @info "solved by pre-processing" }
                    if !maybe_model.is_unsat() {
                        println!("sat")
                    } else {
                        use crate::unsat_core::UnsatRes;
                        println!("unsat");
                        unsat = Some(if instance.proofs() {
                            UnsatRes::empty_entry()
                        } else {
                            UnsatRes::None
                        })
                    }
                    maybe_model.into_option()
                } else {
                    let arc_instance = Arc::new(instance);
                    let solve_res = split::work(&arc_instance, &profiler);

                    instance = unwrap_arc(arc_instance)
                        .chain_err(|| "while trying to recover instance")?;

                    match solve_res {
                        Ok(Some(Either::Left(res))) => {
                            println!("sat");
                            Some(instance.extend_model(res)?)
                        }
                        Ok(None) => {
                            println!("unknown");
                            None
                        }
                        Ok(Some(Either::Right(res))) => {
                            unsat = Some(res);
                            println!("unsat");
                            None
                        }
                        Err(ref e) if e.is_unsat() => {
                            unsat = Some(unsat_core::UnsatRes::None);
                            warn!(
                                "unsat was obtained by a legacy mechanism, \
                                 core/proof will not be available"
                            );
                            println!("unsat");
                            None
                        }
                        Err(ref e) if e.is_timeout() => {
                            println!("timeout");
                            print_stats("top", profiler);
                            ::std::process::exit(0)
                        }
                        Err(ref e) if e.is_unknown() => {
                            println!("unknown");
                            None
                        }
                        Err(e) => {
                            bail!(e)
                        }
                    }
                };

                if stop_on_check {
                    return Ok((model, instance));
                }
            }

            Parsed::GetUnsatCore | Parsed::GetModel if !conf.infer => (),

            // Print unsat core if available.
            Parsed::GetUnsatCore => println!("unsupported"),

            // Print unsat core if available.
            Parsed::GetProof => {
                if let Some(unsat_res) = unsat.as_ref() {
                    if let Err(e) = original_instance
                        .as_ref()
                        .ok_or::<Error>(
                            "unable to retrieve original instance for proof reconstruction".into(),
                        )
                        .and_then(|original| {
                            unsat_res
                                .write_proof(&mut stdout(), &instance, original)
                                .chain_err(|| "while writing unsat proof")
                        })
                    {
                        print_err(&e)
                    }
                } else {
                    print_err(&"no unsat proof available".into())
                }
            }

            // Print model if available.
            Parsed::GetModel => {
                if let Some(model) = model.as_mut() {
                    // Simplify model before writing it.
                    // instance.simplify_pred_defs(model) ? ;
                    let stdout = &mut stdout();
                    instance.write_model(&model, stdout)?
                } else {
                    bail!("no model available")
                }
            }

            Parsed::Items => {
                if instance.print_success() {
                    println!("success")
                }
            }

            Parsed::Reset => {
                parser_cxt.reset();
                instance = Instance::new();
                model = None
            }

            Parsed::Eof => {
                if stop_on_check {
                    bail!("reached <eof> without reading a check-sat...")
                } else {
                    ()
                }
            }

            Parsed::Exit => break 'parse_work,
        }
    }

    print_stats("top", profiler);

    Ok((model, instance))
}

/// Waits until an `Arc` is unwrap-able.
fn unwrap_arc<T>(arc: Arc<T>) -> Res<T> {
    while Arc::strong_count(&arc) != 1 {}
    if let Ok(res) = Arc::try_unwrap(arc) {
        Ok(res)
    } else {
        bail!("unable to unwrap `Arc`")
    }
}
