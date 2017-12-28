//! Entry point for the binary.

extern crate hoice ;

extern crate log ;
extern crate env_logger ;
#[macro_use]
extern crate mylib ;

use hoice::common::* ;


/// Log record formatter.
fn format(log: & ::log::LogRecord) -> String {
  use log::LogLevel::* ;
  match log.level() {
    Error => {
      let mut s = String::new() ;
      s.push_str(
        & format!(
          "({} \"\n",
          conf.bad("error")
        )
      ) ;
      for line in format!( "{}", log.args() ).lines() {
        s.push_str( & format!("  {}\n", line) ) ;
      }
      s.push_str(& format!("\")") ) ;
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
      s.push_str(& format!("\n; {}\n", conf.sad("|===|")) ) ;
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
      s.push_str(& format!("\n; {}\n","|===|") ) ;
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
