//! Error types.
//!
//! Two specific events are handled are errors so that they propagate upwards
//! naturally, although technically they're not really errors.
//!
//! - [`ErrorKind::Unsat`][unsat], self-explanatory ;
//! - [`LError::Exit`][exit], used in learners to bail out of the learning
//!   phase when the teacher sent an exit order.
//!
//! [unsat]: enum.ErrorKind.html#variant.Unsat
//! (Unsat variant of the ErrorKind enum)
//! [exit]: learners/enum.LError.html#variant.Exit
//! (Exit variant of the LError enum)

use common::* ;


/// Parse error data.
#[derive(Debug)]
pub struct ParseErrorData {
  /// Error message.
  pub msg: String,
  /// Portion of the line *before* the error token.
  pub pref: String,
  /// Token that caused the error.
  pub token: String,
  /// Portion of the line *after* the error token.
  pub suff: String,
  /// Line of the error, relative to the portion of the input accessible by
  /// whoever constructed the error.
  pub line: Option<usize>,
}
impl_fmt!{
  ParseErrorData(self, fmt) {
    let line_str = if let Some(line) = self.line {
      format!("{} ", line)
    } else { "".into() } ;
    write!(
      fmt, "{}", self.msg
    ) ? ;
    if let Some(line) = self.line {
      writeln!(
        fmt, " at [{}]:", conf.emph(
          & format!("{}:{}", line, self.pref.len() + 1)
        )
      ) ?
    } else {
      writeln!(fmt, ":") ?
    }
    writeln!(
      fmt, "{0: ^1$}|", "", line_str.len()
    ) ? ;
    writeln!(
      fmt, "{}| {}{}{}",
      & line_str,
      conf.emph(& self.pref), conf.bad(& self.token), conf.emph(& self.suff)
    ) ? ;
    writeln!(
      fmt, "{0: ^1$}| {0: ^2$}{3}", "", line_str.len(), self.pref.len(),
      conf.bad( & format!("{0:^>1$}", "", self.token.len()) )
    )
  }
}

error_chain!{
  types {
    Error, ErrorKind, ResultExt, Res ;
  }

  links {
    SmtError(
      ::rsmt2::errors::Error, ::rsmt2::errors::ErrorKind
    ) #[doc = "Error at SMT level."] ;
  }

  foreign_links {
    Io(::std::io::Error) #[doc = "IO error."] ;
  }

  errors {
    #[doc = "Parse error."]
    ParseError(data: ParseErrorData) {
      description("parse error")
      display("{}", data)
    }
    #[doc = "Could not spawn z3."]
    Z3SpawnError {
      description("could not spawn z3")
      display("could not spawn z3")
    }
    #[doc = "Not really an error, unsat early return."]
    Unsat {
      description("unsat")
      display("unsat")
    }
    /// Not really an error, unsat early return.
    ///
    /// When raised by a kid, `core` is none, only the samples causing the
    /// unsat result is there. The teacher adds the core.
    NuUnsat(
      unsat: Vec<(PrdIdx, Args)>,
      core: Option<::common::data::unsat_core::SampleGraph>
    ) {
      description("unsat")
      display("unsat")
    }
    #[doc = "Not really an error, exit early return."]
    Exit {
      description("exit")
      display("exit")
    }
    #[doc = "Timeout reached."]
    Timeout {
      description("timeout")
      display("timeout")
    }
  }
}

impl Error {
  /// True if the kind of the error is [`ErrorKind::Unsat`][unsat].
  ///
  /// [unsat]: enum.ErrorKind.html#variant.Unsat
  /// (ErrorKind's Unsat variant)
  pub fn is_unsat(& self) -> bool {
    match * self.kind() {
      ErrorKind::Unsat => true,
      ErrorKind::NuUnsat(_, _) => true,
      _ => false,
    }
  }

  /// True if the kind of the error is [`ErrorKind::Timeout`][timeout].
  ///
  /// [timeout]: enum.ErrorKind.html#variant.Timeout
  /// (ErrorKind's Timeout variant)
  pub fn is_timeout(& self) -> bool {
    match * self.kind() {
      ErrorKind::Timeout => true,
      _ => false,
    }
  }

  /// True if the kind of the error is [`ErrorKind::Exit`][exit].
  ///
  /// [exit]: enum.ErrorKind.html#variant.Exit
  /// (ErrorKind's Exit variant)
  pub fn is_exit(& self) -> bool {
    match * self.kind() {
      ErrorKind::Exit => true,
      _ => false,
    }
  }
}


/// Prints an error.
pub fn print_err(errs: Error) {
  println!(
    "({} \"", conf.bad("error")
  ) ;
  for err in errs.iter() {
    for line in format!("{}", err).lines() {
      println!("  {}", line)
    }
  }
  println!("\")")
}
