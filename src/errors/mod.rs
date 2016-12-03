// Copyright (c) 2016 Fabian Schuiki

//! Utilities to implement diagnostics and error reporting facilities.

use source::Span;
use std::fmt;



/// A handler deals with errors.
#[derive(Debug)]
pub struct Handler {
}


pub static DUMMY_HANDLER: Handler = Handler{};


/// Used to emit structured error messages.
#[must_use]
#[derive(Clone, Debug)]
pub struct DiagnosticBuilder<'a> {
	pub handler: &'a Handler,
	pub message: String,
}

/// A diagnostic result type. Either carries the result `T` in the Ok variant,
/// or an assembled diagnostic in the Err variant.
pub type DiagResult<'a, T> = Result<T, DiagnosticBuilder<'a>>;



#[must_use]
#[derive(Clone, Debug)]
pub struct DiagBuilder2 {
	pub severity: Severity,
	pub message: String,
	pub span: Option<Span>,
}

/// A diagnostic result type. Either carries the result `T` in the Ok variant,
/// or an assembled diagnostic in the Err variant.
pub type DiagResult2<T> = Result<T, DiagBuilder2>;

impl DiagBuilder2 {
	pub fn fatal<S: Into<String>>(message: S) -> DiagBuilder2 {
		DiagBuilder2 {
			severity: Severity::Fatal,
			message: message.into(),
			span: None,
		}
	}

	pub fn error<S: Into<String>>(message: S) -> DiagBuilder2 {
		DiagBuilder2 {
			severity: Severity::Error,
			message: message.into(),
			span: None,
		}
	}

	pub fn warning<S: Into<String>>(message: S) -> DiagBuilder2 {
		DiagBuilder2 {
			severity: Severity::Warning,
			message: message.into(),
			span: None,
		}
	}

	pub fn span<S: Into<Span>>(self, span: S) -> DiagBuilder2 {
		DiagBuilder2 {
			span: Some(span.into()),
			..self
		}
	}

	pub fn get_severity(&self) -> Severity {
		self.severity
	}

	pub fn get_message(&self) -> &String {
		&self.message
	}

	pub fn get_span(&self) -> Option<Span> {
		self.span
	}
}



#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Severity {
	Fatal,
	Error,
	Warning,
	Note,
}

impl Severity {
	pub fn to_str(self) -> &'static str {
		match self {
			Severity::Fatal => "fatal",
			Severity::Error => "error",
			Severity::Warning => "warning",
			Severity::Note => "note",
		}
	}
}

impl fmt::Display for Severity {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}", self.to_str())
	}
}
