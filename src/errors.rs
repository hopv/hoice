//! Error types.

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
    ) ? ;
    writeln!(fmt, "")
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
      _ => false,
    }
  }
}


/// Prints an error.
pub fn print_err(errs: Error) {
  let mut lines ;
  for_first!(
    errs.iter() => {
      |err| lines = format!("{}", err),
      then |err| lines = format!("{}\n{}", lines, err),
      yild error!{"{}", lines}
    } else ()
  )
}