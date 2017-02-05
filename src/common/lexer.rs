// Copyright (c) 2016-2017 Fabian Schuiki

//! Lexer utilities.

use std::io::Read;
use std::cmp::max;
use errors::DiagResult;
use std::collections::VecDeque;


/// A trait that can supply a peekable stream of characters.
pub trait Reader {
	fn peek(&mut self, offset: usize) -> Option<char>;
	fn consume(&mut self, amount: usize);
	fn clear(&mut self);
	fn to_string(&self) -> String;
}

/// A trait that can supply a stream of tokens.
pub trait Lexer<T> {
	fn next_token<'td>(&mut self) -> DiagResult<'td, T>;
}


pub struct AccumulatingReader {
	rd: Box<Read>,
	buf: Vec<u8>,
	base: usize,
	pos: usize,
	tail: usize,
}

impl AccumulatingReader {
	pub fn new(rd: Box<Read>) -> AccumulatingReader {
		AccumulatingReader {
			rd: rd,
			buf: Vec::new(),
			base: 0,
			pos: 0,
			tail: 0,
		}
	}

	/// Grow and fill the internal buffer such that at least min_len characters
	/// are present, or the end of the file has been reached. This function may
	/// shift the buffer contents around, in which case previous buffer indices
	/// become invalid. Recalculate all indices derived from `base`, `pos`, or
	/// `tail` after a call to this function.
	pub fn refill(&mut self, mut min_len: usize) {
		// Move the buffer contents to the beginning to make more space at the
		// end.
		if self.base > 0 {
			// println!("    Rebasing {} to 0 ({} bytes)", self.base, self.tail-self.base);
			for i in 0..(self.tail-self.base) {
				self.buf[i] = self.buf[self.base+i]
			}
			self.pos -= self.base;
			self.tail -= self.base;
			min_len -= self.base;
			self.base = 0;
		}
		assert!(self.base == 0);

		// Increase the buffer size to make sure the requested min_len can be
		// accomodated.
		let cur_len = self.buf.len();
		if min_len > cur_len {
			let new_len = max(cur_len*2, 32);
			// println!("    Resizing buffer to {} bytes", new_len);
			self.buf.resize(new_len, 0);
		}
		assert!(self.buf.len() >= min_len);

		// Keep reading data until at least min_len bytes are in the buffer.
		// Note that this will usually fill in the entire buffer.
		while min_len > self.tail {
			let nread = {
				let dst = &mut self.buf[self.tail..];
				let nread = self.rd.read(dst).unwrap();
				// println!("    Read {} out of a max of {} bytes", nread, dst.len());
				nread
			};
			if nread == 0 {
				// println!("    Seems like we've hit EOF");
				break;
			}
			self.tail += nread;
			// println!("      {:?}", &self.buf[self.base..self.tail]);
		}
	}

	/// Return a slice of the consumed bytes.
	pub fn slice(&self) -> &[u8] {
		&self.buf[self.base .. self.pos]
	}

	/// Return a slice of the remaining bytes, starting at the last call to
	/// clear().
	pub fn rem_slice(&self) -> &[u8] {
		&self.buf[self.base ..]
	}
}

impl Reader for AccumulatingReader {
	/// Return the value of the byte that is `off` bytes away from the current
	/// position in the input file. If the `off` lies beyond the end of file,
	/// `None` is returned.
	fn peek(&mut self, off: usize) -> Option<char> {
		// If the requested offset lies outside the chunk of the file that is
		// currently in memory, refill the buffer first.
		let idx = self.pos+off;
		if idx >= self.tail {
			self.refill(idx+1)
		}

		// The previous call to refill may move things around in the buffer, so
		// the index needs to be recalculated. If it lies beyond what we were
		// able to read from the file, as indicated by `self.tail`, return
		// `None` to indicate the end of the file.
		let idx = self.pos+off;
		if idx < self.tail {
			Some(self.buf[idx] as char)
		} else {
			None
		}
	}

	/// Consume the next `amt` bytes of the input. All consumed bytes since the
	/// last `clear()` can be accessed via `slice()` or `to_string()`.
	fn consume(&mut self, amt: usize) {
		self.pos += amt
	}

	/// Clear the consumed bytes.
	fn clear(&mut self) {
		self.base = self.pos
	}

	/// Convert the consumed bytes to a String.
	fn to_string(&self) -> String {
		// TODO: Don't just unwrap, but handle the case where the input file is
		// not valid UTF8.
		String::from_utf8(self.slice().to_vec()).unwrap()
	}
}


pub struct StringReader<'tdata> {
	// data: &'tdata str,
	iter: Box<Iterator<Item = char> + 'tdata>,
	buf: Vec<char>,
	base: usize,
	pos: usize,
	tail: usize,
}

impl<'tdata> StringReader<'tdata> {
	pub fn new(data: &'tdata str) -> StringReader<'tdata> {
		StringReader {
			// data: data,
			iter: Box::new(data.chars()),
			buf: Vec::new(),
			base: 0,
			pos: 0,
			tail: 0,
		}
	}

	fn refill(&mut self, mut min_len: usize) {
		// Move the buffer contents to the beginning to make more space at the
		// end.
		if self.base > 0 {
			for i in 0..(self.tail-self.base) {
				self.buf[i] = self.buf[self.base+i]
			}
			self.pos -= self.base;
			self.tail -= self.base;
			min_len -= self.base;
			self.base = 0;
		}
		assert!(self.base == 0);

		// Increase the buffer size to make sure the requested min_len can be
		// accomodated.
		let cur_len = self.buf.len();
		if min_len > cur_len {
			let new_len = max(cur_len*2, 32);
			self.buf.resize(new_len, 0 as char);
		}
		assert!(self.buf.len() >= min_len);

		// Keep reading data until at least min_len bytes are in the buffer.
		// Note that this will usually fill in the entire buffer.
		while min_len > self.tail {
			match self.iter.next() {
				Some(c) => {
					self.buf[self.tail] = c;
					self.tail += 1;
				},
				None => break,
			}
		}
	}
}

impl<'tdata> Reader for StringReader<'tdata> {
	fn peek(&mut self, offset: usize) -> Option<char> {
		// If the requested offset lies outside the chunk of characters that has
		// been parsed, refill the buffer first.
		let idx = self.pos + offset;
		if idx >= self.tail {
			self.refill(idx+1)
		}

		// The previous call to refill may move things around in the buffer, so
		// the index needs to be recalculated. If it lies beyond what we were
		// able to parse from the string, as indicated by `self.tail`, return
		// `None` to indicate the end of the file.
		let idx = self.pos + offset;
		if idx < self.tail {
			Some(self.buf[idx])
		} else {
			None
		}
	}

	fn consume(&mut self, amount: usize) {
		self.pos += amount;
	}

	fn clear(&mut self) {
		self.base = self.pos;
	}

	fn to_string(&self) -> String {
		let mut s = String::new();
		for c in self.buf[self.base .. self.pos].iter() {
			s.push(*c);
		}
		s
	}
}



/// A lexer chaining the tokens of multiple other lexers after another. Lexers
/// can be pushed onto an internal stack and will then be queried for tokens
/// until their respective Eof has been reached. At that point, the lexer is
/// popped off the stack and the next lexer's tokens are produced. An Eof is
/// returned once all lexers have been drained.
pub struct StackedLexer<T> {
	stack: Vec<Box<Lexer<T>>>,
	eof: T,
}

impl<T> StackedLexer<T> {
	pub fn new(eof: T) -> StackedLexer<T> {
		StackedLexer {
			stack: Vec::new(),
			eof: eof,
		}
	}

	pub fn push(&mut self, lexer: Box<Lexer<T>>) {
		self.stack.push(lexer);
	}
}

impl<T: Clone + PartialEq> Lexer<T> for StackedLexer<T> {
	fn next_token<'td>(&mut self) -> DiagResult<'td, T> {
		loop {
			let token =
				if let Some(lexer) = self.stack.last_mut() {
					try!(lexer.next_token())
				} else {
					return Ok(self.eof.clone());
				};
			if token == self.eof {
				self.stack.pop();
				continue;
			} else {
				return Ok(token);
			}
		}
	}
}



/// A buffered lexer that allows tokens to be peeked at before they are actually
/// consumed.
pub struct BufferedLexer<T> {
	inner: Box<Lexer<T>>,
	eof: T,
	buffer: VecDeque<T>,
	done: bool,
}

impl<T: Clone + PartialEq> BufferedLexer<T> {
	/// Create a new buffered lexer.
	pub fn new(inner: Box<Lexer<T>>, eof: T) -> BufferedLexer<T> {
		BufferedLexer {
			inner: inner,
			eof: eof,
			buffer: VecDeque::new(),
			done: false,
		}
	}

	/// Peek at a token not yet consumed. This function merely returns a
	/// reference to said token. Use `pop()` to advance the lexer.
	pub fn peek<'td>(&mut self, offset: usize) -> DiagResult<'td, &T> {
		// Fill the buffer up to the offset that should be peeked at. If an Eof is
		// encountered beforehand, set the `done` flag and abort.
		while !self.done && self.buffer.len() <= offset {
			let token = try!(self.inner.next_token());
			if token == self.eof {
				self.done = true;
			}
			self.buffer.push_back(token);
		}

		// Return the token at the requested offset, or the Eof token if the
		// offset lies beyond the end of the stream.
		Ok(self.buffer.get(offset).unwrap_or(&self.eof))
		// if offset < self.buffer.len() {
		// } else {
		// 	Ok(self.eof.clone())
		// }
	}

	/// Insert a token in front of the stream such that it becomes the next
	/// token to be returned from `peek(0)` or `pop()`.
	#[allow(unused_variables)]
	pub fn push(&mut self, token: T) {
		unimplemented!();
	}

	/// Consume and return the current token. This is the same token that would
	/// be returned by `peek(0)`.
	pub fn pop<'td>(&mut self) -> DiagResult<'td, T> {
		if self.buffer.is_empty() && !self.done {
			self.inner.next_token()
		} else {
			Ok(self.buffer.pop_front().expect("pop() called on drained BufferedLexer"))
		}
	}

	pub fn inner(&self) -> &Lexer<T> {
		&*self.inner
	}

	pub fn inner_mut(&mut self) -> &mut Lexer<T> {
		&mut *self.inner
	}
}
