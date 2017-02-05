// Copyright (c) 2017 Fabian Schuiki

//! This module implements the on-disk AST storage. Items can be serialized to
//! disk and deserialized again ata later point.

use std;
use std::collections::HashSet;
use std::fs::OpenOptions;
use std::io::prelude::*;
use std::io::{Error, ErrorKind};
use std::path::PathBuf;
use super::ast;
use bincode::SizeLimit;
use bincode::rustc_serialize::{encode_into, decode_from};


pub fn store_items(path: &str, key: &str, ast: ast::Root) -> std::io::Result<()> {
	let mut file = OpenOptions::new().append(true).create(true).open(path)?;
	file.write(&[42])?;
	encode_into(&ast, &mut file, SizeLimit::Infinite)
		.map_err(|e| Error::new(ErrorKind::Other, e))
}


pub fn load_items(path: &str) -> std::io::Result<Vec<ast::Root>> {
	let mut file = OpenOptions::new().read(true).open(path)?;
	let mut v = Vec::new();
	loop {
		let mut tagbuf = [0];
		if let Err(e) = file.read_exact(&mut tagbuf) {
			if e.kind() == std::io::ErrorKind::UnexpectedEof {
				break;
			} else {
				return Err(e);
			}
		} else {
			assert_eq!(tagbuf[0], 42);
		}
		match decode_from(&mut file, SizeLimit::Infinite) {
			Ok(x) => v.push(x),
			Err(e) => return Err(Error::new(ErrorKind::InvalidInput, e)),
		}
	}
	Ok(v)
}
