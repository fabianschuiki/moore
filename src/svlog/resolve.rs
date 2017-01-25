// Copyright (c) 2017 Fabian Schuiki

use super::ast;
use name::*;
use source::*;
use errors::*;
use std::collections::HashMap;


pub fn build_symtbl(asts: &[ast::Root]) -> SymTbl {
	let mut tbl = HashMap::new();
	let mut diags = Vec::new();

	for i in 0..asts.len() {
		let ast = &asts[i];
		for item in &ast.items {
			let (name, span, id) = match *item {
				ast::Item::Module(ref decl) => (decl.name, decl.name_span, 0),
				ast::Item::Interface(ref decl) => (decl.name, decl.name_span, 0),
				ast::Item::Package(ref decl) => (decl.name, decl.name_span, 0),
				_ => continue
			};

			if let Some(ex) = tbl.insert(name, (span, i, id)) {
				if ex.0 != span {
					diags.push(DiagBuilder2::error(format!("name `{}` has already been declared", name)).span(span));
					diags.push(DiagBuilder2::note("previous declaration was here").span(ex.0));
				}
			}
		}
	}

	for d in diags {
		println!("{}", d);
	}

	SymTbl {
		tbl: tbl,
	}
}


pub struct SymTbl {
	tbl: HashMap<Name, (Span, usize, usize)>,
}
