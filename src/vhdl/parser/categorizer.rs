// Copyright (c) 2017 Fabian Schuiki

use moore_common::grind::Grinder;
use moore_common::errors::DiagBuilder2;


/// A grinder that categorizes characters into different groups as per the VHDL
/// language standard.
pub struct Categorizer<T> {
	inner: T,
}

impl<T> Categorizer<T> where T: Grinder<Item=Option<(usize, char, u8)>, Error=DiagBuilder2> {
	/// Create a new categorizer.
	pub fn new(inner: T) -> Categorizer<T> {
		Categorizer { inner: inner }
	}
}

impl<T> Grinder for Categorizer<T> where T: Grinder<Item=Option<(usize, char, u8)>, Error=DiagBuilder2> {
	type Item = Option<(usize, char, u8, Category)>;
	type Error = DiagBuilder2;

	fn emit(&mut self, err: Self::Error) {
		self.inner.emit(err);
	}

	fn next(&mut self) -> Self::Item {
		let (offset, c, sz) = match self.inner.next() {
			Some(v) => v,
			None => return None,
		};
		let cat = match c {
			'"' | '#' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | '-' | '.' |
			'/' | ':' | ';' | '<'  | '=' | '>' | '?' | '@' | '[' | ']' | '_' |
			'`' | '|' => Category::Special,
			c if c.is_alphabetic() => Category::Letter,
			c if c.is_digit(10) => Category::Digit,
			c if c.is_whitespace() => Category::Space,
			_ => Category::Other,
		};
		Some((offset, c, sz, cat))
	}
}

/// A character category. Special means the special characters as defined by the
/// VHDL standard to be meaningful syntactically.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Category {
	Letter,
	Digit,
	Special,
	Space,
	Other,
}
