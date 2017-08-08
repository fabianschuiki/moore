// Copyright (c) 2017 Fabian Schuiki

//! This module provides an abstraction similar to iterators. Elements are
//! produced in one direction, while errors bubble backwards until they are
//! vented. This allows for complex transformation chains such as lexical
//! analyzers and parsers to be constructed, where errors, warnings, or notices
//! might be emitted without disturbing the transformation.

use std;
use std::marker::PhantomData;

pub mod utf8;
mod peek;
mod lookahead;
mod filter;

pub use self::peek::Peekable;
pub use self::lookahead::Lookahead;
pub use self::filter::Filter;


pub trait Chisel: Default {
	type Value;
	fn end() -> Self;
	fn is_end(&self) -> bool;
	fn value(self) -> Option<Self::Value>;
	fn value_ref(&self) -> Option<&Self::Value>;
}

impl<T> Chisel for Option<T> {
	type Value = T;
	fn end() -> Option<T> { None }
	fn is_end(&self) -> bool { self.is_none() }
	fn value(self) -> Option<T> { self }
	fn value_ref(&self) -> Option<&T> { self.as_ref() }
}



pub trait Grinder {
	type Item: Chisel;
	type Error;

	fn next(&mut self) -> Self::Item;
	fn emit(&mut self, err: Self::Error);

	#[inline]
	fn vent<F,E>(self, f: F) -> Vent<Self, F, E> where Self: Sized, F: Fn(E) {
		Vent { inner: self, ventfn: f, phantom: PhantomData }
	}

	#[inline]
	fn unwrap(self) -> Unwrap<Self> where Self: Sized {
		Unwrap { inner: self }
	}

	#[inline]
	fn map_err<F,E>(self, f: F) -> MapErrGrinder<Self, F, E> where Self: Sized, F: Fn(E) -> Self::Error {
		MapErrGrinder { inner: self, mapfn: f, phantom: PhantomData }
	}

	#[inline]
	fn peekable(self) -> Peekable<Self> where Self: Sized {
		Peekable::new(self)
	}

	#[inline]
	fn lookaheadable(self) -> Lookahead<Self> where Self: Sized {
		Lookahead::new(self)
	}

	#[inline]
	fn filter<F>(self, f: F) -> Filter<Self, F> where Self: Sized, F: Fn(&<Self::Item as Chisel>::Value) -> bool {
		Filter::new(self, f)
	}
}

// All Grinder implement UnventedGrinder.
// impl<T: Grinder> UnventedGrinder for T {
// 	type Item = T::Item;

// 	fn next(&mut self) -> Self::Item {
// 		self.next()
// 	}
// }

// impl<I: Chisel, E: Debug> Iterator for Grinder<Item=I, Error=E> {
// 	type Item = <Self as Grinder>::Item;
// 	fn next(&mut self) -> Option<Self::Item> {
// 		self.next().value()
// 	}
// }

impl<I, C: Chisel<Value=I>, E> Iterator for Grinder<Item=C, Error=E> {
	type Item = I;

	fn next(&mut self) -> Option<I> {
		self.next().value()
	}
}



pub struct Vent<T: Grinder, F, E> {
	inner: T,
	ventfn: F,
	phantom: PhantomData<E>,
}

impl<T: Grinder, E, F> Grinder for Vent<T,F,E> where F: Fn(E) {
	type Item = T::Item;
	type Error = E;

	fn next(&mut self) -> Self::Item {
		self.inner.next()
	}

	fn emit(&mut self, err: E) {
		(self.ventfn)(err)
	}
}



pub struct MapErrGrinder<T: Grinder, F, E> {
	inner: T,
	mapfn: F,
	phantom: PhantomData<E>,
}

impl<T,E,F> Grinder for MapErrGrinder<T,F,E>
where T: Grinder, F: Fn(E) -> T::Error {
	type Item = T::Item;
	type Error = E;

	fn next(&mut self) -> Self::Item {
		self.inner.next()
	}

	fn emit(&mut self, err: E) {
		let e = (self.mapfn)(err);
		self.inner.emit(e);
	}
}



pub struct Read<R: std::io::Read> {
	inner: R,
	buffer: Vec<u8>,
	ptr: usize,
	max: usize,
}

impl<R: std::io::Read> Grinder for Read<R> {
	type Item = Option<std::io::Result<u8>>;
	type Error = ();

	fn next(&mut self) -> Self::Item {
		if self.ptr >= self.max {
			self.ptr = 0;
			match self.inner.read(&mut self.buffer) {
				Ok(sz) if sz > 0 => self.max = sz,
				Ok(_) => return None,
				Err(e) => return Some(Err(e)),
			}
		}
		let v = Some(Ok(self.buffer[self.ptr]));
		self.ptr += 1;
		v
	}

	fn emit(&mut self, _: ()) {
		unreachable!()
	}
}

// pub fn from_read<T: std::io::Read>(read: T) -> Iter<std::io::Bytes<std::io::BufReader<T>>> {
// 	use std::io::Read;
// 	from_iter(std::io::BufReader::with_capacity(1024, read).bytes())
// }

pub fn from_read<T: std::io::Read>(read: T) -> Read<T> {
	Read { inner: read, buffer: Vec::with_capacity(1024), ptr: 0, max: 0 }
}



pub struct Iter<I: Iterator> {
	inner: I,
}

impl<I: Iterator> Grinder for Iter<I> {
	type Item = Option<I::Item>;
	type Error = ();

	fn next(&mut self) -> Option<I::Item> {
		self.inner.next()
	}

	fn emit(&mut self, _: ()) {
		unreachable!()
	}
}

pub fn from_iter<I: Iterator>(iter: I) -> Iter<I> {
	Iter { inner: iter }
}



pub struct Unwrap<T: Grinder> {
	inner: T,
}

impl<I,E,C,T> Grinder for Unwrap<T>
where C: Chisel<Value=Result<I,E>>, T: Grinder<Item=C, Error=E> {
	type Item = Option<I>;
	type Error = T::Error;

	fn emit(&mut self, err: E) {
		self.inner.emit(err)
	}

	fn next(&mut self) -> Self::Item {
		match self.inner.next().value() {
			Some(Ok(v)) => Some(v),
			Some(Err(e)) => {
				self.emit(e);
				None
			}
			None => None
		}
	}
}
