// Copyright (c) 2016-2018 Fabian Schuiki

//! Utilities to implement diagnostics and error reporting facilities.

use source::Span;
use std::fmt;

/// Print debug information. Omitted in release builds.
#[macro_export]
#[cfg(debug_assertions)]
macro_rules! debugln {
    ($($arg:tt)*) => { eprintln!("\x1B[34;1mdebug:\x1B[m {}", format!($($arg)*)); }
}

/// Print debug information. Omitted in release builds.
#[macro_export]
#[cfg(not(debug_assertions))]
macro_rules! debugln {
    ($($arg:tt)*) => {}
}

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

/// Emits diagnostic messages.
pub trait DiagEmitter {
	/// Emit a diagnostic message.
	fn emit(&self, diag: DiagBuilder2);
}

impl<'a, T> DiagEmitter for &'a T where T: DiagEmitter + ?Sized {
	fn emit(&self, diag: DiagBuilder2) {
		(*self).emit(diag)
	}
}

#[must_use]
#[derive(Clone, Debug)]
pub struct DiagBuilder2 {
	pub severity: Severity,
	pub message: String,
	pub segments: Vec<DiagSegment>,
}

#[derive(Clone, Debug)]
pub enum DiagSegment {
	Span(Span),
	Note(String),
}

/// A diagnostic result type. Either carries the result `T` in the Ok variant,
/// or an assembled diagnostic in the Err variant.
pub type DiagResult2<T> = Result<T, DiagBuilder2>;

impl DiagBuilder2 {
	pub fn new<S: Into<String>>(severity: Severity, message: S) -> DiagBuilder2 {
		DiagBuilder2 {
			severity: severity,
			message: message.into(),
			segments: Vec::new(),
		}
	}

	pub fn bug<S: Into<String>>(message: S) -> DiagBuilder2 {
		DiagBuilder2::new(Severity::Bug, message)
	}

	pub fn fatal<S: Into<String>>(message: S) -> DiagBuilder2 {
		DiagBuilder2::new(Severity::Fatal, message)
	}

	pub fn error<S: Into<String>>(message: S) -> DiagBuilder2 {
		DiagBuilder2::new(Severity::Error, message)
	}

	pub fn warning<S: Into<String>>(message: S) -> DiagBuilder2 {
		DiagBuilder2::new(Severity::Warning, message)
	}

	pub fn note<S: Into<String>>(message: S) -> DiagBuilder2 {
		DiagBuilder2::new(Severity::Note, message)
	}

	pub fn segment(self, segment: DiagSegment) -> DiagBuilder2 {
		let mut segments = self.segments;
		segments.push(segment);
		DiagBuilder2 {
			segments: segments,
			..self
		}
	}

	pub fn span<S: Into<Span>>(self, span: S) -> DiagBuilder2 {
		self.segment(DiagSegment::Span(span.into()))
	}

	pub fn add_note<S: Into<String>>(self, message: S) -> DiagBuilder2 {
		self.segment(DiagSegment::Note(message.into()))
	}

	pub fn get_severity(&self) -> Severity {
		self.severity
	}

	pub fn get_message(&self) -> &String {
		&self.message
	}

	pub fn get_segments(&self) -> &[DiagSegment] {
		&self.segments
	}
}



#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Severity {
	Note,
	Warning,
	Error,
	Fatal,
	Bug,
}

impl Severity {
	pub fn to_str(self) -> &'static str {
		match self {
			Severity::Fatal => "fatal",
			Severity::Error => "error",
			Severity::Warning => "warning",
			Severity::Note => "note",
			Severity::Bug => "compiler bug",
		}
	}
}

impl fmt::Display for Severity {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}", self.to_str())
	}
}

impl fmt::Display for DiagBuilder2 {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		let mut colorcode = match self.get_severity() {
			Severity::Bug | Severity::Fatal | Severity::Error => "\x1B[31;1m",
			Severity::Warning => "\x1B[33;1m",
			Severity::Note => "\x1B[36;1m",
		};
		write!(f, "{}{}:\x1B[m\x1B[1m {}\x1B[m\n", colorcode, self.get_severity(), self.get_message())?;

		for segment in &self.segments {
			match *segment {
				DiagSegment::Span(sp) => {
					let c = sp.source.get_content();
					let mut iter = c.extract_iter(0, sp.begin);

					// Look for the start of the line.
					let mut col = 1;
					let mut line = 1;
					let mut line_offset = sp.begin;
					while let Some(c) = iter.next_back() {
						match c.1 {
							'\n' => { line += 1; break; },
							'\r' => continue,
							_ => {
								col += 1;
								line_offset = c.0;
							}
						}
					}

					// Count the number of lines.
					while let Some(c) = iter.next_back() {
						if c.1 == '\n' {
							line += 1;
						}
					}

					// Print the line in question.
					let text: String = c.iter_from(line_offset).map(|x| x.1).take_while(|c| *c != '\n' && *c != '\r').collect();
					write!(f, "  --> {}:{}:{}-{}:\n", sp.source.get_path(), line, col, col + sp.extract().len())?;
					write!(f, "   | \n")?;
					write!(f, "   | ")?;
					for (mut i,c) in text.char_indices() {
						i += line_offset;
						if sp.begin != sp.end {
							if i == sp.begin { write!(f, "{}", colorcode)?; }
							if i == sp.end { write!(f, "\x1B[m")?; }
						}
						match c {
							'\t' => write!(f, "    ")?,
							c => write!(f, "{}", c)?,
						}
					}
					write!(f, "\x1B[m\n")?;
					write!(f, "   | ")?;

					// Print the caret markers for the line in question.
					let mut pd = ' ';
					for (mut i,c) in text.char_indices() {
						i += line_offset;
						let d = if (i >= sp.begin && i < sp.end) || (i == sp.begin && sp.begin == sp.end) {
							'^'
						} else {
							' '
						};
						if d != pd {
							write!(f, "{}", if d == ' ' {"\x1B[m"} else {colorcode})?;
						}
						pd = d;
						match c {
							'\t' => write!(f, "{}{}{}{}", d, d, d, d)?,
							_ => write!(f, "{}", d)?,
						}
					}
					write!(f, "\x1B[m\n")?;
					colorcode = "\x1B[1m";
				}
				DiagSegment::Note(ref message) => write!(f, "   = \x1B[1mnote:\x1B[m {}\n", message)?,
			}
		}

		if self.get_severity() == Severity::Bug {
			write!(f, "\nYou have encountered a compiler bug. Sorry about that! We would appreciate if you open an issue [1] and describe how you triggered the bug, together with a minimal snippet of code to reproduce it. Thanks!\n")?;
			write!(f, "[1]: https://github.com/fabianschuiki/moore\n")?;
		}

		Ok(())
	}
}
