// Copyright (c) 2016 Fabian Schuiki

//! Lexer utilities.

use std::io::Read;
use std::cmp::max;


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

	/// Return the value of the byte that is `off` bytes away from the current
	/// position in the input file. If the `off` lies beyond the end of file,
	/// `None` is returned.
	pub fn peek(&mut self, off: usize) -> Option<char> {
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

	/// Consume the next `amt` bytes of the input. All consumed bytes since the
	/// last `clear()` can be accessed via `slice()` or `to_string()`.
	pub fn consume(&mut self, amt: usize) {
		self.pos += amt
	}

	/// Clear the consumed bytes.
	pub fn clear(&mut self) {
		self.base = self.pos
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

	/// Convert the consumed bytes to a String.
	pub fn to_string(&self) -> String {
		// TODO: Don't just unwrap, but handle the case where the input file is
		// not valid UTF8.
		String::from_utf8(self.slice().to_vec()).unwrap()
	}
}
