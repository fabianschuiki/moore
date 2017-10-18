// Copyright (c) 2016-2017 Fabian Schuiki
#![allow(dead_code)]
#![allow(unused_variables)]

extern crate clap;
extern crate sha1;
extern crate bincode;
extern crate rustc_serialize;
extern crate typed_arena;
#[macro_use]
extern crate moore_common;
extern crate moore_svlog;
extern crate moore_vhdl;
pub mod score;
use moore_common::*;
use moore_common::errors::*;
use moore_common::name::Name;
use moore_svlog as svlog;
use moore_vhdl as vhdl;
use clap::{Arg, App, SubCommand, ArgMatches};
use std::path::Path;
use score::Scoreboard;


#[derive(Debug)]
enum Language {
	Verilog,
	SystemVerilog,
	Vhdl,
}


fn main() {
	let matches = App::new("moore")
		.arg(Arg::with_name("trace_scoreboard")
			.long("trace-scoreboard"))
		.subcommand(SubCommand::with_name("compile")
			.arg(Arg::with_name("inc")
				.short("I")
				.value_name("DIR")
				.help("Adds a search path for SystemVerilog includes")
				.multiple(true)
				.takes_value(true)
				.number_of_values(1))
			.arg(Arg::with_name("preproc")
				.short("E")
				.help("Only preprocess input files"))
			.arg(Arg::with_name("dump_ast")
				.long("dump-ast")
				.help("Dump the parsed abstract syntax tree"))
			.arg(Arg::with_name("INPUT")
				.help("The input file to use")
				.required(true)
				.index(1)))
		.subcommand(SubCommand::with_name("elaborate")
			.arg(Arg::with_name("NAME")
				.help("Entity or module to elaborate")
				.required(true)
				.index(1))
			.arg(Arg::with_name("ignore_duplicate_defs")
				.long("ignore-duplicate-defs")
				.help("Ignore multiple module/entity definitions")))
		.subcommand(SubCommand::with_name("score")
			.arg(Arg::with_name("inc")
				.short("I")
				.value_name("DIR")
				.help("Add a search path for SystemVerilog includes")
				.multiple(true)
				.takes_value(true)
				.number_of_values(1))
			.arg(Arg::with_name("dump_ast")
				.long("dump-ast")
				.help("Dump the parsed abstract syntax tree"))
			.arg(Arg::with_name("lib")
				.short("l")
				.long("lib")
				.value_name("LIB")
				.help("Name of the library to compile into")
				.takes_value(true)
				.number_of_values(1))
			.arg(Arg::with_name("elaborate")
				.short("e")
				.long("elaborate")
				.value_name("ENTITY")
				.help("Elaborate an entity or module")
				.multiple(true)
				.takes_value(true)
				.number_of_values(1))
			.arg(Arg::with_name("INPUT")
				.help("The input files to compile")
				.multiple(true)
				.required(true)))
		.get_matches();

	let mut session = Session::new();
	session.opts.trace_scoreboard = matches.is_present("trace_scoreboard");

	if let Some(m) = matches.subcommand_matches("compile") {
		compile(m);
	} else if let Some(m) = matches.subcommand_matches("elaborate") {
		session.opts.ignore_duplicate_defs = m.is_present("ignore_duplicate_defs");
		elaborate(m, &session);
	} else if let Some(m) = matches.subcommand_matches("score") {
		score(&session, m);
	}
}


fn compile(matches: &ArgMatches) {
	// Prepare a list of include paths.
	let include_paths: Vec<_> = match matches.values_of("inc") {
		Some(args) => args.map(|x| std::path::Path::new(x)).collect(),
		None => Vec::new()
	};
	let filename = matches.value_of("INPUT").unwrap();

	// Detect the file type.
	let language = match Path::new(&filename).extension().and_then(|s| s.to_str()) {
		Some("sv") | Some("svh") => Language::SystemVerilog,
		Some("v") => Language::Verilog,
		Some("vhd") | Some("vhdl") => Language::Vhdl,
		Some(_) => panic!("Unrecognized extension of file '{}'", filename),
		None => panic!("Unable to determine language of file '{}'", filename),
	};

	let sm = source::get_source_manager();
	let source = match sm.open(&filename) {
		Some(s) => s,
		None => panic!("Unable to open input file '{}'", filename),
	};

	match language {
		Language::SystemVerilog | Language::Verilog => {
			// Run the input file only through the SystemVerilog preprocessor if
			// so requested on the command line.
			let preproc = svlog::preproc::Preprocessor::new(source, &include_paths);
			if matches.is_present("preproc") {
				for res in preproc {
					print!("{}", res.unwrap().1.extract());
				}
			} else {
				let lexer = svlog::lexer::Lexer::new(preproc);
				let ast = match svlog::parser::parse(lexer) {
					Ok(x) => x,
					Err(()) => std::process::exit(1),
				};

				// TODO: Serialize the parsed AST to disk. If a file is parsed
				// multiple times, the tree of the previous iteration needs to
				// be removed. Upon elaboration, it must be possible to
				// efficiently query the AST for identifiers and check in which
				// subtree the node lives.

				let key = {
					let mut s = sha1::Sha1::new();
					s.update(filename.as_bytes());
					s.digest().to_string()
				};
				svlog::store::store_items(".moore", &key, ast).unwrap();
			}
		}
		Language::Vhdl => {
			let mut ast = match vhdl::syntax::parse(source) {
				Ok(x) => x,
				Err(()) => std::process::exit(1),
			};
			if matches.is_present("dump_ast") {
				println!("{:#?}", ast);
			}

			// Be very stupid for now, and don't write anything to disk. Just
			// keep on using this AST and pretend that it was loaded from disk.
			// TODO: Fix this once we have a proper way of persisting build data
			// to disk.

			// 1) renumber AST nodes and build scope and symbol table
			let mut symtbl = vhdl::symtbl::SymTbl::new();
			{
				use name::get_name_table;
				use source::{Spanned, INVALID_SPAN};
				use self::vhdl::symtbl::{DefName, Def};
				let mut renum = vhdl::pass::renumber::Renumberer::new(&mut symtbl);
				let name = get_name_table().intern("work", false); // could be something other than "work"
				let work = get_name_table().intern("work", false);
				let lib_id = renum.symtbl.get_library_id(name);
				renum.push_scope(lib_id);
				// This declares the library under its actual name, but also the
				// alias "work". Maybe we should move this somewhere more
				// appropriate.
				renum.declare(Spanned::new(DefName::Ident(name), INVALID_SPAN), Def::Lib(lib_id));
				if name != work {
					renum.declare(Spanned::new(DefName::Ident(work), INVALID_SPAN), Def::Lib(lib_id));
				}
				ast = ast.into_iter().map(|n| renum.fold_design_unit(n)).collect();
				renum.pop_scope();
				println!("renumbered {} design units", ast.len());
			}

			// 2) resolve names and map to HIR
			{
				use name::get_name_table;
				let mut lower = vhdl::pass::lower::Lowerer::new(&mut symtbl);
				let name = get_name_table().intern("work", false); // could be something other than "work"
				let lib_id = lower.symtbl.get_library_id(name);
				lower.push_scope(lib_id);
				let hir: Vec<_> = ast.into_iter().map(|n| lower.fold_design_unit(n)).collect();
				lower.pop_scope();
				println!("lowered design units: {:#?}", hir);
			}
		}
	}
}


fn elaborate(matches: &ArgMatches, session: &Session) {
	use moore_common::errors::DiagBuilder2;

	// Load the syntax trees previously parsed and stored into the library.
	let mut asts = svlog::store::load_items(".moore").unwrap();

	// Renumber the AST nodes.
	svlog::renumber::renumber(&mut asts);

	// Perform name resolution.
	let nameres = match svlog::resolve::resolve(session, &asts) {
		Ok(x) => x,
		Err(_) => {
			println!("{}", DiagBuilder2::fatal("name resolution failed"));
			std::process::exit(1);
		}
	};

	// Find the ID of the module we are supposed to be elaborating.
	let top_name = matches.value_of("NAME").unwrap();
	let top = match (||{
		for ast in &asts {
			for item in &ast.items {
				if let svlog::ast::Item::Module(ref decl) = *item {
					if &*decl.name.as_str() == top_name {
						return Some(decl.id);
					}
				}
			}
		}
		None
	})() {
		Some(id) => id,
		None => {
			println!("{}", DiagBuilder2::fatal(format!("unable to find top module `{}`", top_name)));
			std::process::exit(1);
		}
	};

	// Lower to HIR.
	let hir = match svlog::hir::lower(session, &nameres, top, asts) {
		Ok(x) => x,
		Err(_) => {
			println!("{}", DiagBuilder2::fatal("lowering to HIR failed"));
			std::process::exit(1);
		},
	};
	println!("lowered {} modules", hir.mods.len());
}


fn score(sess: &Session, matches: &ArgMatches) {
	use moore_common::name::get_name_table;

	// Prepare a list of include paths.
	let include_paths: Vec<_> = match matches.values_of("inc") {
		Some(args) => args.map(|x| std::path::Path::new(x)).collect(),
		None => Vec::new()
	};

	// Establish into which library the entities will be compiled. Later on this
	// should be made configurable per entity.
	let lib = get_name_table().intern(matches.value_of("lib").unwrap_or("work"), true);

	// Parse the input files.
	let mut failed = false;
	let mut asts = Vec::new();
	for filename in matches.values_of("INPUT").unwrap() {
		// Detect the file type.
		let language = match Path::new(&filename).extension().and_then(|s| s.to_str()) {
			Some("sv") | Some("svh") => Language::SystemVerilog,
			Some("v") => Language::Verilog,
			Some("vhd") | Some("vhdl") => Language::Vhdl,
			Some(_) => panic!("Unrecognized extension of file '{}'", filename),
			None => panic!("Unable to determine language of file '{}'", filename),
		};

		// Add the file to the source manager.
		let sm = source::get_source_manager();
		let source = match sm.open(&filename) {
			Some(s) => s,
			None => panic!("Unable to open input file '{}'", filename),
		};

		// Parse the file.
		match language {
			Language::SystemVerilog | Language::Verilog => {
				let preproc = svlog::preproc::Preprocessor::new(source, &include_paths);
				let lexer = svlog::lexer::Lexer::new(preproc);
				match svlog::parser::parse(lexer) {
					Ok(x) => asts.push(score::Ast::Svlog(x)),
					Err(()) => failed = true,
				}
			}
			Language::Vhdl => {
				match vhdl::syntax::parse(source) {
					Ok(x) => asts.push(score::Ast::Vhdl(x)),
					Err(()) => failed = true,
				}
			}
		}
	}
	if failed {
		std::process::exit(1);
	}

	// Dump the AST if so requested.
	if matches.is_present("dump_ast") {
		println!("{:#?}", asts);
	}

	// Create the scoreboard and add the initial map of libraries.
	let arenas = score::Arenas::new();
	let mut sb = Scoreboard::new(sess, &arenas);
	// vhdl_sb.set_parent(&sb);
	let lib_id = sb.add_library(lib, &asts);
	println!("lib_id = {:?}", lib_id);
	println!("{:?}", sb);

	// Elaborate the requested entities or modules.
	if let Some(names) = matches.values_of("elaborate") {
		for name in names {
			match elaborate_name(&mut sb, lib_id, name) {
				Ok(_) => (),
				Err(_) => failed = true,
			};
		}
	}
	if failed {
		std::process::exit(1);
	}
}

/// Resolve an entity/module specificaiton of the form `[lib.]entity[.arch]` for
/// elaboration.
fn elaborate_name(sb: &mut Scoreboard, lib_id: score::LibRef, input_name: &str) -> Result<(),()> {
	let (lib, name, arch) = parse_elaborate_name(input_name)?;
	println!("parsed `{}` into (lib: {:?}, name: {:?}, arch: {:?})", input_name, lib, name, arch);

	// Resolve the library name if one was provided.
	let lib = {
		if let Some(lib) = lib {
			let rid = sb.root;
			match sb.defs(score::ScopeRef::Root(rid))?.get(&lib) {
				Some(&score::Def::Lib(d)) => d,
				_ => {
					sb.emit(DiagBuilder2::error(format!("Library `{}` does not exist", lib)));
					return Err(());
				},
			}
		} else {
			lib_id
		}
	};
	println!("using library {:?}", lib);

	// Resolve the entity name.
	// TODO: Make sure that the thing we resolve to actually is a VHDL entity or
	// a SystemVerilog module. Right we happily accept packages as well.
	#[derive(Debug)]
	enum Entity {
		Vhdl(vhdl::score::EntityRef),
		Svlog(NodeId), // TODO: handle svlog case
	};
	let entity = match sb.defs(lib.into())?.get(&name) {
		Some(&score::Def::Vhdl(vhdl::score::Def::Entity(e))) => Entity::Vhdl(e),
		Some(&score::Def::Svlog(e)) => Entity::Svlog(e),
		_ => {
			sb.emit(DiagBuilder2::error(format!("Entity or module `{}` does not exist", name)));
			return Err(());
		}
	};
	println!("using entity {:?}", entity);

	// In case we're elaborating a VHDL entity, resolve the architecture name if
	// one was provided, or find a default architecture to use.
	#[derive(Debug)]
	enum Elaborate {
		Vhdl(vhdl::score::EntityRef, vhdl::score::ArchRef),
		Svlog(NodeId),
	}
	let elab = match entity {
		Entity::Vhdl(entity) => {
			let archs = sb.vhdl.archs(vhdl::score::LibRef::new(lib.into()))?.get(&entity).unwrap();
			let arch_ref = if let Some(arch) = arch {
				match archs.1.get(&arch) {
					Some(&id) => id,
					None => {
						sb.emit(DiagBuilder2::error(format!("`{}` is not an architecture of entity `{}`", arch, name)));
						return Err(());
					}
				}
			} else {
				match archs.0.last() {
					Some(&id) => id,
					None => {
						sb.emit(DiagBuilder2::error(format!("Entity `{}` has no architecture defined", name)));
						return Err(());
					}
				}
			};
			Elaborate::Vhdl(entity, arch_ref)
		}
		Entity::Svlog(module) => {
			Elaborate::Svlog(module)
		}
	};

	println!("elaborating {:?}", elab);
	Ok(())
}


/// Parse an entity name of the form `(first\.)?second((arch))?` for
/// elaboration.
fn parse_elaborate_name<S: AsRef<str>>(name: S) -> Result<(Option<Name>, Name, Option<Name>), ()> {
	use self::name::get_name_table;
	let name = name.as_ref();
	let nt = get_name_table();

	// Isolate the first name.
	let x: &[_] = &['.', '('];
	let (first, rest) = {
		if let Some(pos) = name.find(x) {
			let (a,b) = name.split_at(pos);
			(a, Some(b))
		} else {
			(name, None)
		}
	};
	let first = nt.intern(first, true);

	// Isolate the second name.
	let (second, rest) = {
		if let Some(rest) = rest {
			if rest.starts_with('.') {
				let rest = &rest[1..];
				if let Some(pos) = rest.find('(') {
					let (a,b) = rest.split_at(pos);
					(Some(a), Some(b))
				} else {
					(Some(rest), None)
				}
			} else {
				(None, Some(rest))
			}
		} else {
			(None, None)
		}
	};
	let second = second.map(|s| nt.intern(s, true));

	// Isolate the architecture name.
	let third = {
		if let Some(rest) = rest {
			if rest.starts_with('(') && rest.ends_with(')') {
				Some(&rest[1..rest.len()-1])
			} else {
				None
			}
		} else {
			None
		}
	};
	let third = third.map(|t| nt.intern(t, true));

	// Return the names in the appropriate order.
	let (lib, ent) = {
		if let Some(second) = second {
			(Some(first), second)
		} else {
			(None, first)
		}
	};

	Ok((lib, ent, third))
}
