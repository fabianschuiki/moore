// Copyright (c) 2016-2017 Fabian Schuiki

//! A global source file table that assigns an opaque ID to each processed
//! source file. This helps keeping the source location lean and allow for
//! simple querying of information.

extern crate memmap;
use name::RcStr;
use self::memmap::Mmap;
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::hash::Hash;
use std::path::Path;
use std::rc::Rc;



pub const INVALID_SOURCE: Source = Source(0);
pub const INVALID_LOCATION: Location = Location { source: INVALID_SOURCE, offset: 0 };
pub const INVALID_SPAN: Span = Span { source: INVALID_SOURCE, begin: 0, end: 0 };


#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Source(pub u32);

impl Source {
	/// Return the path of this source file.
	pub fn get_path(self) -> RcStr {
		get_source_manager().with(self, |x| x.get_path())
	}

	/// Access the contents of this source file.
	pub fn get_content(self) -> Rc<SourceContent> {
		get_source_manager().with(self, |x| x.get_content())
	}

	/// Copy a range of the source content into a String instance owned by the
	/// caller, possibly converting the encoding such that the result is in
	/// UTF-8.
	pub fn extract(self, begin: usize, end: usize) -> String {
		get_source_manager().with(self, |x| x.extract(begin, end))
	}
}

impl fmt::Debug for Source {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		if self.0 > 0 {
			write!(f, "Source({}; \"{}\")", self.0, self.get_path())
		} else {
			write!(f, "Source(INVALID)")
		}
	}
}

impl fmt::Display for Source {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		fmt::Display::fmt(&self.get_path(), f)
	}
}



pub trait SourceFile {
	fn get_id(&self) -> Source;
	fn get_path(&self) -> RcStr;
	// TODO: getter for character iterator
	// TODO: getter for source file extracts

	/// Obtain the content of this source file. The returned object may be used
	/// to iterate over the characters in the file or extract portions of it.
	fn get_content(&self) -> Rc<SourceContent>;

	/// Copy a range of the source content into a String instance owned by the
	/// caller, possibly converting the encoding such that the result is in
	/// UTF-8.
	fn extract(&self, begin: usize, end: usize) -> String {
		self.get_content().extract(begin, end)
	}
}

pub trait SourceContent {
	/// Obtain an iterator over the characters within the source file, together
	/// with their respective byte positions.
	fn iter(&self) -> Box<CharIter>;

	/// Obtain an iterator over the characters within the source file, starting
	/// at the provided location `offset`, together with their respective byte
	/// positions.
	fn iter_from(&self, offset: usize) -> Box<CharIter>;

	/// Copy a range of the source content into a String instance owned by the
	/// caller, possibly converting the encoding such that the result is in
	/// UTF-8.
	fn extract(&self, begin: usize, end: usize) -> String;

	/// Obtain an iterator over an extract of the source content. This might be
	/// more efficient than copying the extract into a String.
	fn extract_iter(&self, begin: usize, end: usize) -> Box<CharIter>;
}



/// A manager for source files and their assigned IDs.
pub struct SourceManager {
	map: RefCell<HashMap<RcStr, Source>>,
	vect: RefCell<Vec<Box<SourceFile>>>,
}

impl SourceManager {
	fn new() -> SourceManager {
		SourceManager {
			map: RefCell::new(HashMap::new()),
			vect: RefCell::new(Vec::new()),
		}
	}

	/// Obtain the source file for a given source ID.
	pub fn with<F, R>(&self, id: Source, f: F) -> R
	where F: FnOnce(&SourceFile) -> R {
		let ref vect = *self.vect.borrow();
		assert!(id.0 > 0, "invalid source");
		assert!((id.0 as usize - 1) < vect.len(), "unknown source file: Source({}) >= {}", id.0, vect.len());
		f(&*vect[id.0 as usize - 1])
	}

	pub fn find<Q: ?Sized>(&self, filename: &Q) -> Option<Source>
	where RcStr: Borrow<Q>, Q: Eq + Hash {
		(*self.map.borrow()).get(filename).map(|v| *v)
	}

	pub fn open(&self, filename: &str) -> Option<Source> {
		// Check if the file has already been opened and return its pointer.
		let mut map = self.map.borrow_mut();
		if let Some(&id) = map.get(filename) {
			return Some(id);
		}

		// Check whether the file exists and allocate a new index for it.
		if Path::new(filename).exists() {
			let mut vect = self.vect.borrow_mut();
			let new_id = Source(vect.len() as u32 + 1);
			let v = RcStr::new(filename);
			map.insert(v.clone(), new_id);
			vect.push(Box::new(DiskSourceFile {
				id: new_id,
				filename: v,
				content: RefCell::new(None),
			}));
			Some(new_id)
		} else {
			None
		}
	}

	/// Create a virtual file from the contents of a string and add it to the
	/// source manager. Future calls to `open()` with the given filename will
	/// yield the provided contents.
	pub fn add(&self, filename: &str, content: &str) -> Source {
		let mut map = self.map.borrow_mut();
		assert!(!map.contains_key(filename), "add failed: source \"{}\" already exists", filename);
		let mut vect = self.vect.borrow_mut();
		let new_id = Source(vect.len() as u32 + 1);
		let v = RcStr::new(filename);
		map.insert(v.clone(), new_id);
		vect.push(Box::new(VirtualSourceFile {
			id: new_id,
			filename: v,
			content: Rc::new(VirtualSourceContent(content.to_string())),
		}));
		new_id
	}
}



/// Get the global source manager.
pub fn get_source_manager() -> Rc<SourceManager> {
	thread_local!(static MNGR: Rc<SourceManager> = {
		Rc::new(SourceManager::new())
	});
	MNGR.with(|x| x.clone())
}



/// A virtual source file that has no correspondence in the file system. Useful
/// for unit tests.
struct VirtualSourceFile {
	id: Source,
	filename: RcStr,
	content: Rc<VirtualSourceContent>,
}

struct VirtualSourceContent(pub String);

impl SourceFile for VirtualSourceFile {
	fn get_id(&self) -> Source {
		self.id
	}

	fn get_path(&self) -> RcStr {
		self.filename.clone()
	}

	fn get_content(&self) -> Rc<SourceContent> {
		self.content.clone()
	}
}

impl SourceContent for VirtualSourceContent {
	fn iter(&self) -> Box<CharIter> {
		Box::new(self.0.char_indices())
	}

	fn iter_from(&self, offset: usize) -> Box<CharIter> {
		Box::new(self.0[offset..].char_indices())
	}

	fn extract(&self, begin: usize, end: usize) -> String {
		self.0[begin..end].to_string()
	}

	fn extract_iter(&self, begin: usize, end: usize) -> Box<CharIter> {
		Box::new(self.0[begin..end].char_indices())
	}
}



/// A source file on disk.
struct DiskSourceFile {
	id: Source,
	filename: RcStr,
	content: RefCell<Option<Rc<DiskSourceContent>>>,
}

#[derive(Debug)]
struct DiskSourceContent(pub Mmap);

impl SourceFile for DiskSourceFile {
	fn get_id(&self) -> Source {
		self.id
	}

	fn get_path(&self) -> RcStr {
		self.filename.clone()
	}

	fn get_content(&self) -> Rc<SourceContent> {
		use self::memmap::Protection;
		let is_none = self.content.borrow().is_none();
		if is_none {
			let c = Rc::new(DiskSourceContent(
				Mmap::open_path(Path::new(&*self.filename), Protection::Read).unwrap()
			));
			*self.content.borrow_mut() = Some(c.clone());
			c
		} else {
			self.content.borrow().clone().unwrap()
		}
	}
}

impl SourceContent for DiskSourceContent {
	fn iter(&self) -> Box<CharIter> {
		use std::str;
		Box::new(str::from_utf8(unsafe { self.0.as_slice() }).unwrap().char_indices())
	}

	fn iter_from(&self, offset: usize) -> Box<CharIter> {
		use std::str;
		Box::new(str::from_utf8(unsafe { &self.0.as_slice()[offset..] }).unwrap().char_indices())
	}

	fn extract(&self, begin: usize, end: usize) -> String {
		use std::str;
		str::from_utf8(unsafe { &self.0.as_slice()[begin..end] }).unwrap().to_string()
	}

	fn extract_iter(&self, begin: usize, end: usize) -> Box<CharIter> {
		use std::str;
		Box::new(str::from_utf8(unsafe { &self.0.as_slice()[begin..end] }).unwrap().char_indices())
	}
}



/// An iterator that yields the characters from an input file together with the
/// byte positions within the stream.
pub type CharIter<'a> = DoubleEndedIterator<Item = (usize, char)> + 'a;



/// A single location within a source file, expressed as a byte offset.
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct Location {
	pub source: Source,
	pub offset: usize,
}

impl Location {
	/// Create a new location.
	pub fn new(source: Source, offset: usize) -> Location {
		Location { source: source, offset: offset }
	}

	/// Obtain an iterator into the source file at this location.
	pub fn iter<'a>(self, content: &'a Rc<SourceContent>) -> Box<CharIter<'a>> {
		content.iter_from(self.offset)
	}
}

impl fmt::Debug for Location {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{:?}:{}", self.source, self.offset)
	}
}

impl Into<Span> for Location {
	fn into(self) -> Span {
		Span::new(self.source, self.offset, self.offset)
	}
}



/// A span of locations within a source file, expressed as a half-open interval
/// of bytes `[begin,end)`.
#[derive(Copy, Clone, PartialOrd, Ord, PartialEq, Eq)]
pub struct Span {
	pub source: Source,
	pub begin: usize,
	pub end: usize,
}

impl Span {
	/// Create a new span from two byte offsets.
	pub fn new(source: Source, begin: usize, end: usize) -> Span {
		Span { source: source, begin: begin, end: end }
	}

	/// Create a new span that covers two spans, i.e. represents the smallest
	/// possible span that fully contains both input spans `a` and `b`.
	pub fn union<S: Into<Span>>(a: S, b: S) -> Span {
		use std::cmp::{min, max};
		let sa = a.into();
		let sb = b.into();
		// assert_eq!(sa.source, sb.source);
		if sa.source != sb.source {
			return sa;
		}
		Span {
			source: sa.source,
			begin: min(sa.begin, sb.begin),
			end: max(sa.end, sb.end),
		}
	}

	/// Modify this range to also cover the entirety of the `other` range. The
	/// `other` range must lie in the same source as `self`.
	pub fn expand<S: Into<Span>>(&mut self, other: S) -> &mut Self {
		use std::cmp::{min, max};
		let o = other.into();
		// assert_eq!(self.source, o.source);
		if self.source == o.source {
			self.begin = min(self.begin, o.begin);
			self.end = max(self.end, o.end);
		}
		self
	}

	/// Return the location just before the first character in this span.
	pub fn begin(&self) -> Location {
		Location::new(self.source, self.begin)
	}

	/// Return the location just after the last character in this span.
	pub fn end(&self) -> Location {
		Location::new(self.source, self.end)
	}

	/// Copy the portion of the source file in this span into an owned string.
	pub fn extract(&self) -> String {
		self.source.get_content().extract(self.begin, self.end)
	}

	/// Obtain an iterator over the extract of the source file describe by this
	/// span.
	pub fn iter<'a>(self, content: &'a Rc<SourceContent>) -> Box<CharIter<'a>> {
		content.extract_iter(self.begin, self.end)
	}
}

impl fmt::Debug for Span {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{:?}:{}-{}", self.source, self.begin, self.end)
	}
}



#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	#[should_panic(expected = "invalid source")]
	fn invalid_source_id() {
		get_source_manager().with(Source(0), |_|());
	}

	#[test]
	#[should_panic(expected = "unknown source file")]
	fn unknown_source_id() {
		get_source_manager().with(Source(1), |_|());
	}

	#[test]
	fn inject_file() {
		let sm = get_source_manager();
		let id = sm.add("flabberghasted.txt", "Hello\nWorld\n");
		let source = sm.open("flabberghasted.txt").expect("file should exist");
		assert_eq!(source, id);
	}

	#[test]
	fn inexistent_file() {
		let sm = get_source_manager();
		assert_eq!(sm.open("/this/path/points/nowhere"), None);
	}

	#[test]
	fn chars() {
		let sm = get_source_manager();
		let source = sm.add("test.txt", "老虎.");
		let content = source.get_content();
		let elements: Vec<(usize,char)> = content.iter().collect();
		assert_eq!(elements, vec![(0,'老'), (3,'虎'), (6,'.')]);
	}

	#[test]
	fn file() {
		use std::path::Path;
		use std::fs::File;
		use std::io::Write;

		let path = Path::new("/tmp/moore-test");
		let data = "Löwe 老虎 Léopard\n";
		File::create(path).unwrap().write_all(data.as_bytes()).unwrap();

		let sm = get_source_manager();
		let source = sm.open(path.to_str().unwrap()).expect("file should exist");
		let content = source.get_content();
		let expected: Vec<_> = data.char_indices().collect();
		let actual: Vec<_> = content.iter().collect();

		assert_eq!(expected, actual);
	}
}
