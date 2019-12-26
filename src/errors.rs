//! Error types.
//!
//! Some events are handled are errors so that they propagate upwards naturally, although
//! technically they're not really errors:
//!
//! - [`ErrorKind::Unsat`]
//! - [`ErrorKind::Timeout`]
//! - [`ErrorKind::Unknown`] (when hoice gave up on solving the clauses)
//!
//! As such, one should **not** use the usual `chain_err` function but [`chain`] instead.
//!
//! [`ErrorKind::Unsat`]: enum.ErrorKind.html#variant.Unsat (Unsat variant of ErrorKind)
//! [`ErrorKind::Timeout`]: enum.ErrorKind.html#variant.Timeout (Timeout variant of ErrorKind)
//! [`ErrorKind::Unknown`]: enum.ErrorKind.html#variant.Unknown (Unknown variant of ErrorKind)
//! [`chain`]: struct.Error.html#method.chain (chain function over Error)

use crate::common::*;

/// A term type-checking error.
///
/// Can be created by
///
/// - [`term::try_app`] when creating operator applications
/// - [`term::try_fun`] when creating function calls
///
/// [`term::try_app`]: ../term/fn.try_app.html (try_app function)
/// [`term::try_fun`]: ../term/fn.try_fun.html (try_fun function)
#[derive(Clone, Debug)]
pub enum TypError {
    /// No type info, just an error message.
    Msg(String),
    /// Type error on a specific argument.
    Typ {
        /// The type that was expected. `None` if the type is unknown, for arithmetic operators for
        /// instance.
        expected: Option<Typ>,
        /// The actual type found.
        obtained: Typ,
        /// The index of the argument that caused the error.
        index: usize,
    },
}

mylib::impl_fmt! {
    TypError(self, fmt) {
        match self {
            TypError::Msg(s) => write!(fmt, "{}", s),
            TypError::Typ {
                expected, obtained, index
            } => write!(fmt,
                "error on argument #{}: found {} expected {}",
                index, obtained,
                expected.as_ref().map(
                    |t| format!("{}", t)
                ).unwrap_or_else(|| "something else".to_string())
            )
        }
    }
}

impl TypError {
    /// Message constructor.
    pub fn msg<S: Into<String>>(s: S) -> Self {
        TypError::Msg(s.into())
    }

    /// Type info constructor.
    pub fn typ(expected: Option<Typ>, obtained: Typ, index: usize) -> Self {
        TypError::Typ {
            expected,
            obtained,
            index,
        }
    }
}

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
mylib::impl_fmt! {
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

error_chain::error_chain! {
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
        #[doc = "Not really an error, unknown early return."]
        Unknown {
            description(consts::err::unknown_desc)
            display("unknown")
        }
        #[doc = "Not really an error, unsat early return."]
        Unsat {
            description(consts::err::unsat_desc)
            display("unsat")
        }
        #[doc = "Not really an error, unsat early return because of some clause."]
        UnsatFrom(clause: ClsIdx) {
            description(consts::err::unsat_desc)
            display("unsat by #{}", clause)
        }
        #[doc = "Not really an error, exit early return."]
        Exit {
            description(consts::err::exit_desc)
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
    pub fn is_unsat(&self) -> bool {
        for err in self.iter() {
            if err.description() == consts::err::unsat_desc {
                return true;
            }
        }
        false
    }

    /// True if the kind of the error is [`ErrorKind::Unknown`][unknown].
    ///
    /// [unknown]: enum.ErrorKind.html#variant.Unknown
    /// (ErrorKind's Unknown variant)
    pub fn is_unknown(&self) -> bool {
        for err in self.iter() {
            if err.description() == consts::err::unknown_desc
                || err.description() == ::rsmt2::errors::ErrorKind::Unknown.description()
            {
                return true;
            }
        }
        false
    }

    /// Returns the clause explaining an unsat result if any.
    pub fn unsat_cause(&self) -> Option<ClsIdx> {
        match self.kind() {
            ErrorKind::UnsatFrom(clause) => Some(*clause),
            _ => None,
        }
    }

    /// True if the kind of the error is a timeout.
    ///
    /// [timeout]: enum.ErrorKind.html#variant.Timeout
    /// (ErrorKind's Timeout variant)
    pub fn is_timeout(&self) -> bool {
        if let ErrorKind::SmtError(smt_err) = self.kind() {
            return smt_err.is_timeout();
        }
        for err in self.iter() {
            if err.description() == consts::err::timeout_desc {
                return true;
            }
        }
        false
    }

    /// True if the kind of the error is [`ErrorKind::Exit`][exit].
    ///
    /// [exit]: enum.ErrorKind.html#variant.Exit (ErrorKind's Exit variant)
    pub fn is_exit(&self) -> bool {
        for err in self.iter() {
            if err.description() == consts::err::exit_desc {
                return true;
            }
        }
        false
    }
}

/// Prints an error.
pub fn print_err(errs: &Error) {
    println!("({} \"", conf.bad("error"));
    let mut list = vec![];
    for err in errs.iter() {
        list.push(err)
    }
    for err in list.into_iter().rev() {
        for line in format!("{}", err).lines() {
            println!("  {}", line)
        }
    }
    println!("\")")
}
