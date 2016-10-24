// Copyright (c) 2016 Fabian Schuiki

//! Utilities to implement diagnostics and error reporting facilities.

use source::Span;



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
	pub message: String,
}

/// A diagnostic result type. Either carries the result `T` in the Ok variant,
/// or an assembled diagnostic in the Err variant.
pub type DiagResult2<T> = Result<T, DiagBuilder2>;

impl DiagBuilder2 {
	pub fn fatal<S: Into<String>>(message: S) -> DiagBuilder2 {
		DiagBuilder2 { message: message.into() }
	}

	pub fn span(self, span: Span) -> DiagBuilder2 {
		self
	}
}
