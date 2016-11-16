// Copyright (c) 2016 Fabian Schuiki

//! A name table that internalizes all names presented to it and allows for them
//! to be referred to by a lightweight tag. This structure is heavily inspired
//! by the interner used in the Rust compiler.

use std::borrow::Borrow;
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::ops::Deref;
use std::rc::Rc;


/// A name is a lightweight 32 bit tag that refers to a string in a name table.
/// During parsing, encountered strings are inserted into the name table and
/// only the corresponding tag is kept in the token. Names which have their most
/// significant bit set represent case sensitive names, such as for extended
/// identifiers.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name(pub u32);

impl Name {
	/// Check if the name is case sensitive.
	pub fn is_case_sensitive(&self) -> bool {
		self.0 >> 31 == 1
	}

	/// Return the string representation of this name.
	pub fn as_str(self) -> RcStr {
		get_name_table().get(self)
	}
}

impl fmt::Debug for Name {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{}({})", self, self.0)
	}
}

impl fmt::Display for Name {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt::Display::fmt(&self.as_str(), f)
	}
}



/// A reference-counted string that acts like a regular str slice, hiding the
/// fact that it is wrapped in Rc<>.
#[derive(Clone, PartialEq, Hash, PartialOrd)]
pub struct RcStr(Rc<String>);

impl RcStr {
	/// Create a new ref-counted string which is a copy of `value`.
	pub fn new(value: &str) -> RcStr {
		RcStr(Rc::new(value.to_string()))
	}

	/// Create a new ref-counted string that contains `value`, without
	/// allocating any new storage.
	pub fn from(value: String) -> RcStr {
		RcStr(Rc::new(value))
	}
}

impl Eq for RcStr {}

impl Ord for RcStr {
	fn cmp(&self, other: &RcStr) -> Ordering {
		self[..].cmp(&other[..])
	}
}

impl fmt::Debug for RcStr {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self[..].fmt(f)
	}
}

impl fmt::Display for RcStr {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		self[..].fmt(f)
	}
}

impl Borrow<str> for RcStr {
	fn borrow(&self) -> &str {
		&self.0[..]
	}
}

impl Deref for RcStr {
	type Target = str;
	fn deref(&self) -> &str {
		&self.0[..]
	}
}



/// A lookup table of names. Internalizes strings either in a case sensitive or
/// case insensitive way. Allows for bidirectional lookup, i.e. by string or by
/// assigned name.
pub struct NameTable {
	map: RefCell<HashMap<RcStr, Name>>,
	vect: RefCell<Vec<RcStr>>,
}

impl NameTable {
	/// Create a new empty name table.
	pub fn new() -> NameTable {
		NameTable {
			map: RefCell::new(HashMap::new()),
			vect: RefCell::new(Vec::new()),
		}
	}

	/// Obtain a name for a string. This either inserts the string into the
	/// table and returns the new name, or returns the existing name if the
	/// string already exists in the table.
	pub fn intern(&self, value: &str, case_sensitive: bool) -> Name {
		let mut map = self.map.borrow_mut();
		if let Some(&idx) = map.get(value) {
			return idx;
		}

		// Since the name is not present in the table yet, we allocate a new idx
		// for it. Also, if it is a case-insensitive name, we insert both its
		// original form as well as its lowercase form into the lookup table.
		let mut vect = self.vect.borrow_mut();
		if case_sensitive {
			let new_idx = Name(vect.len() as u32 | 1 << 31);
			let v = RcStr::new(value);
			map.insert(v.clone(), new_idx);
			vect.push(v);
			new_idx
		} else {
			let new_idx = Name(vect.len() as u32);
			let lower = value.to_lowercase();
			if let Some(&idx) = map.get(lower.as_str()) {
				return idx;
			}
			let v = RcStr::new(value);
			map.insert(RcStr::from(lower), new_idx);
			map.insert(v.clone(), new_idx);
			vect.push(v);
			new_idx
		}
	}

	/// Retrieve the string given a name tag.
	pub fn get(&self, idx: Name) -> RcStr {
		(*self.vect.borrow())[(idx.0 & !(1 << 31)) as usize].clone()
	}

	/// Try to find a string.
	pub fn find<Q: ?Sized>(&self, value: &Q) -> Option<Name>
	where RcStr: Borrow<Q>, Q: Eq + Hash {
		(*self.map.borrow()).get(value).map(|v| *v)
	}
}

/// Get this thread's current name table.
pub fn get_name_table() -> Rc<NameTable> {
	thread_local!(static TBL: Rc<NameTable> = {
		let nt = NameTable::new();
		// token::prefill_name_table(&mut nt);
		Rc::new(nt)
	});
	TBL.with(|x| x.clone())
}
