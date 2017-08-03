#![doc = r#"
# TODO

- improve `rsmt2` and make smt learner more efficient and less ad hoc
- remove all the useless error messages in lo-level rsmt2 writers
"#]

#![allow(non_upper_case_globals)]

#[macro_use]
extern crate lazy_static ;
#[macro_use]
extern crate mylib ;
#[macro_use]
extern crate error_chain ;
#[macro_use]
extern crate log ;
extern crate env_logger ;
#[macro_use]
extern crate clap ;
extern crate ansi_term as ansi ;
extern crate regex ;
#[macro_use]
extern crate nom ;
extern crate hashconsing ;
#[macro_use]
extern crate rsmt2 ;
extern crate num ;
extern crate rayon ;

pub mod errors ;
#[macro_use]
pub mod common ;
pub mod instance ;
pub mod teacher ;
pub mod learning ;

pub mod check ;

use common::* ;


/// Log record formatter.
fn format(log: & ::log::LogRecord) -> String {
  use log::LogLevel::* ;
  match log.level() {
    Error => {
      let mut s = String::new() ;
      s.push_str(
        & format!(
          "({}\n\"",
          conf.bad("error")
        )
      ) ;
      let mut pref = "" ;
      for line in format!( "{}", log.args() ).lines() {
        s.push_str( & format!("{}{}", pref, line) ) ;
        pref = "\n"
      }
      s.push_str(& format!("\"\n)") ) ;
      s
    },
    Warn => {
      let mut s = String::new() ;
      s.push_str(
        & format!(
          "; {}",
          conf.sad("|===| Warning:")
        )
      ) ;
      for line in format!( "{}", log.args() ).lines() {
        s.push_str( & format!("\n; {} {}", conf.sad("|"), line) )
      }
      s.push_str(& format!("\n; {}", conf.sad("|===|\n")) ) ;
      s
    },
    Trace => {
      let mut s = String::new() ;
      s.push_str(
        & format!(
          "; {}{}{}",
          "|===| Trace (",
          conf.emph( log.target() ),
          "):"
        )
      ) ;
      for line in format!( "{}", log.args() ).lines() {
        s.push_str( & format!("\n; {} {}", "|", line) )
      }
      s.push_str(& format!("\n; {}","|===|\n") ) ;
      s
    },
    Info | Debug => {
      let push = |
        s: & mut String, pref, line: & str, if_empty
      | if ! line.is_empty() {
        s.push_str(pref) ;
        s.push_str(line)
      } else {
        s.push_str(if_empty)
      } ;
      let original = format!( "{}\n", log.args() ) ;
      let mut s = String::with_capacity(original.len() + 20) ;
      for_first!{
        original.lines() => {
          |fst| {
            push(& mut s, "; ", fst, "")
          }, then |nxt| {
            push(& mut s, "\n; ", nxt, "\n")
          }
        }
      }
      s
    },
  }
}

fn main() {

  // Initialize log.
  if let Err(e) = ::env_logger::LogBuilder::new().target(
    ::env_logger::LogTarget::Stdout
  ).format(format).filter( None, conf.verb.filter() ).init() {
    println!("Error while initializing logger:") ;
    println!("{}", e) ;
    ::std::process::exit(2)
  }

  // Work and report error if any.
  if let Err(errs) = work() {
    let errs = match * errs.kind() {
      ErrorKind::Z3SpawnError => format!(
        "could not spawn z3 using command `{}`\n\
        make sure the z3 binary has that name and is in your path,\n\
        or specify a different z3 command with option `{}`",
        conf.emph( & conf.z3_cmd ),
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


/// TODO:
///
/// - load input file incrementally
fn work() -> Res<()> {

  // Creates smt log directory if needed.
  conf.init() ? ;

  let mut builder = ::instance::build::InstBuild::mk() ;
  builder.reduce().chain_err(
    || "during instance reduction"
  ) ? ;

  if let Some(file_path) = conf.file.as_ref() {
    use std::fs::{ OpenOptions } ;
    use std::io::* ;

    info!{ "loading instance from `{}`...", conf.emph(file_path) }
    let mut buffer = Vec::with_capacity(1007) ;
    let mut file = OpenOptions::new().read(true).open(file_path).chain_err(
      || format!("while opening input file `{}`", conf.emph(file_path))
    ) ? ;
    let _ = file.read_to_end(& mut buffer).chain_err(
      || format!("while reading input file `{}`", conf.emph(file_path))
    ) ? ;

    let (rest, infer) = if let Some(res) = builder.parse(& buffer) {
      res
    } else {
      bail!( builder.to_error(& buffer, Some(0)) )
    } ;

    info!{
      "done: read {} declarations and {} clauses (read {} of {} bytes)\n",
      builder.preds().len(), builder.clauses().len(),
      buffer.len() - rest, buffer.len()
    }

    if ! infer {
      info!{ "no `infer` command provided" }
      return Ok(())
    }

    let instance = builder.to_instance(& buffer, Some(0)) ? ;

    info!{
      "instance:\n{}", instance.string_do( (), |s| s.to_string() ) ?
    }

    // let qualifiers = ::learning::ice::mining::Qualifiers::mk(& instance) ;

    // for pred in PrdRange::zero_to(
    //   instance.preds().len()
    // ) {
    //   println!("qualifiers for {}", conf.emph(& instance[pred].name) ) ;
    //   for qual in qualifiers.of(pred) {
    //     println!("  {}", qual)
    //   }
    //   println!("")
    // }

    teacher::start_class(instance)

  } else {
    info!{ "loading instance from `{}`...", conf.emph("stdin") }
    bail!("parsing from stdin is not implemented")
  }
}
