// Copyright (c) 2016-2018 Fabian Schuiki

//! A hardware description language compiler.

extern crate clap;
extern crate llhd;
extern crate moore;
extern crate sha1;
#[macro_use]
extern crate log;

use clap::{App, Arg, ArgMatches};
use moore::common::score::NodeRef;
use moore::errors::*;
use moore::name::Name;
use moore::score::{ScoreBoard, ScoreContext};
use moore::*;
use std::{path::Path, str::FromStr};

#[derive(Debug)]
enum Language {
    Verilog,
    SystemVerilog,
    Vhdl,
}

fn main() {
    let matches = App::new(env!("CARGO_PKG_NAME"))
        .version(env!("CARGO_PKG_VERSION"))
        .author(env!("CARGO_PKG_AUTHORS"))
        .about("A compiler for hardware description languages.")
        .arg(
            Arg::with_name("trace_scoreboard")
                .long("trace-scoreboard")
                .global(true),
        )
        .arg(
            Arg::with_name("verbosity")
                .short("v")
                .multiple(true)
                .help("Increase message verbosity"),
        )
        .arg(
            Arg::with_name("quiet")
                .short("q")
                .help("Silence all output"),
        )
        .arg(
            Arg::with_name("timestamp")
                .short("t")
                .help("prepend log lines with a timestamp")
                .takes_value(true)
                .possible_values(&["none", "sec", "ms", "ns"]),
        )
        .arg(
            Arg::with_name("verbosity-opts")
                .short("V")
                .help("Sets verbosity settings")
                .takes_value(true)
                .multiple(true)
                .number_of_values(1)
                .possible_values(&["types", "expr-types", "type-contexts", "typeck", "names"])
                .global(true),
        )
        .arg(
            Arg::with_name("inc")
                .short("I")
                .value_name("DIR")
                .help("Add a search path for SystemVerilog includes")
                .multiple(true)
                .takes_value(true)
                .number_of_values(1),
        )
        .arg(
            Arg::with_name("dump_ast")
                .long("dump-ast")
                .help("Dump the parsed abstract syntax tree"),
        )
        .arg(
            Arg::with_name("emit_pkgs")
                .long("emit-pkgs")
                .help("Dump VHDL packages for debugging"),
        )
        .arg(
            Arg::with_name("lib")
                .short("l")
                .long("lib")
                .value_name("LIB")
                .help("Name of the library to compile into")
                .takes_value(true)
                .number_of_values(1),
        )
        .arg(
            Arg::with_name("elaborate")
                .short("e")
                .long("elaborate")
                .value_name("ENTITY")
                .help("Elaborate an entity or module")
                .multiple(true)
                .takes_value(true)
                .number_of_values(1),
        )
        .arg(
            Arg::with_name("INPUT")
                .help("The input files to compile")
                .multiple(true)
                .required(true),
        )
        .get_matches();

    // Configure the logger.
    let verbose = matches.occurrences_of("verbosity") as usize + 1;
    let quiet = matches.is_present("quiet");
    let ts = matches
        .value_of("timestamp")
        .map(|v| {
            stderrlog::Timestamp::from_str(v).unwrap_or_else(|_| {
                clap::Error {
                    message: "invalid value for 'timestamp'".into(),
                    kind: clap::ErrorKind::InvalidValue,
                    info: None,
                }
                .exit()
            })
        })
        .unwrap_or(stderrlog::Timestamp::Off);

    stderrlog::new()
        .quiet(quiet)
        .verbosity(verbose)
        .timestamp(ts)
        .init()
        .unwrap();

    // Configure the session.
    let mut session = Session::new();
    session.opts.trace_scoreboard = matches.is_present("trace_scoreboard");
    for v in matches
        .values_of("verbosity-opts")
        .into_iter()
        .flat_map(|v| v)
    {
        session.opts.verbosity |= match v {
            "types" => Verbosity::TYPES,
            "expr-types" => Verbosity::EXPR_TYPES,
            "type-contexts" => Verbosity::TYPE_CONTEXTS,
            "typeck" => Verbosity::TYPECK,
            "names" => Verbosity::NAMES,
            _ => unreachable!(),
        };
    }

    // Invoke the compiler.
    score(&session, &matches);
}

fn score(sess: &Session, matches: &ArgMatches) {
    use crate::name::get_name_table;

    // Prepare a list of include paths.
    let include_paths: Vec<_> = match matches.values_of("inc") {
        Some(args) => args.map(|x| std::path::Path::new(x)).collect(),
        None => Vec::new(),
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
            Language::Vhdl => match vhdl::syntax::parse(source) {
                Ok(x) => asts.push(score::Ast::Vhdl(x)),
                Err(()) => failed = true,
            },
        }
    }
    if failed || sess.failed() {
        std::process::exit(1);
    }

    // Dump the AST if so requested.
    if matches.is_present("dump_ast") {
        println!("{:#?}", asts);
    }

    if matches.is_present("emit_pkgs") {
        vhdl::debug::emit_pkgs(
            sess,
            asts.iter()
                .flat_map(|ast| match *ast {
                    score::Ast::Vhdl(ref x) => x.iter(),
                    _ => [].iter(),
                })
                .collect(),
        );
    }

    // Create the scoreboard and add the initial map of libraries.
    let arenas = score::Arenas::new();
    let sb = ScoreBoard::new(&arenas);
    let vhdl_sb = vhdl::score::ScoreBoard::new(&arenas.vhdl);
    let svlog_arenas = svlog::GlobalArenas::default();
    let svlog_sb = svlog::GlobalContext::new(&sess, &svlog_arenas);

    // Elaborate the requested entities or modules.
    if let Some(names) = matches.values_of("elaborate") {
        let vhdl_phases = vhdl::lazy::LazyPhaseTable::new(&vhdl_sb);
        let ctx = ScoreContext {
            sess: sess,
            sb: &sb,
            vhdl: &vhdl_sb,
            vhdl_phases: &vhdl_phases,
            svlog: &svlog_sb,
        };
        let lib_id = ctx.add_library(lib, &asts);
        debug!("lib_id = {:?}", lib_id);
        debug!("{:?}", sb);
        for name in names {
            match elaborate_name(&ctx, lib_id, name) {
                Ok(_) => (),
                Err(_) => failed = true,
            };
        }
        if sess.failed() {
            failed = true;
        }
    }
    if failed || sess.failed() {
        std::process::exit(1);
    }

    // Extract the populated LLHD modules from the scoreboards and link them
    // together.
    let vhdl_module = vhdl_sb.llmod.into_inner();

    // Emit the module.
    {
        use llhd::visit::Visitor;
        let stdout = std::io::stdout();
        llhd::assembly::Writer::new(&mut stdout.lock()).visit_module(&vhdl_module);
    }

    if sess.failed() {
        std::process::exit(1);
    }
}

/// Resolve an entity/module specificaiton of the form `[lib.]entity[.arch]` for
/// elaboration.
fn elaborate_name(ctx: &ScoreContext, lib_id: score::LibRef, input_name: &str) -> Result<(), ()> {
    let (lib, name, arch) = parse_elaborate_name(input_name)?;
    debug!(
        "parsed `{}` into (lib: {:?}, name: {:?}, arch: {:?})",
        input_name, lib, name, arch
    );

    // Resolve the library name if one was provided.
    let lib = {
        if let Some(lib) = lib {
            let rid = ctx.sb.root;
            let defs = ctx.defs(score::ScopeRef::Root(rid))?;
            match defs.get(&lib) {
                Some(&score::Def::Lib(d)) => d,
                _ => {
                    let mut d = DiagBuilder2::error(format!("Library `{}` does not exist", lib))
                        .add_note("The following libraries do exist:");
                    let mut names: Vec<_> = defs.iter().map(|(&k, _)| k).collect();
                    names.sort(); // sorts by name ID, roughly equivalent to order of declaration
                    for name in names {
                        d = d.add_note(format!("- {}", name));
                    }
                    ctx.sess.emit(d);
                    return Err(());
                }
            }
        } else {
            lib_id
        }
    };
    debug!("using library {:?}", lib);

    // Resolve the entity name.
    // TODO: Make sure that the thing we resolve to actually is a VHDL entity or
    // a SystemVerilog module. Right we happily accept packages as well.
    #[derive(Debug)]
    enum Elaborate {
        VhdlEntity(vhdl::score::EntityRef, vhdl::score::ArchRef),
        VhdlPkg(vhdl::score::PkgDeclRef),
        Svlog(NodeId), // TODO: handle svlog case
    };
    let defs = ctx.defs(lib.into())?;
    let elab = match defs.get(&name) {
        Some(&score::Def::Vhdl(vhdl::score::Def::Entity(entity))) => {
            let archs = ctx
                .vhdl()
                .archs(vhdl::score::LibRef::new(lib.into()))?
                .by_entity
                .get(&entity)
                .unwrap();
            let arch_ref = if let Some(arch) = arch {
                match archs.by_name.get(&arch) {
                    Some(&id) => id,
                    None => {
                        ctx.sess.emit(DiagBuilder2::error(format!(
                            "`{}` is not an architecture of entity `{}`",
                            arch, name
                        )));
                        return Err(());
                    }
                }
            } else {
                match archs.ordered.last() {
                    Some(&id) => id,
                    None => {
                        ctx.sess.emit(DiagBuilder2::error(format!(
                            "Entity `{}` has no architecture defined",
                            name
                        )));
                        return Err(());
                    }
                }
            };
            Elaborate::VhdlEntity(entity, arch_ref)
        }
        Some(&score::Def::Vhdl(vhdl::score::Def::Pkg(p))) => Elaborate::VhdlPkg(p),
        Some(&score::Def::Svlog(e)) => Elaborate::Svlog(e),
        _ => {
            let mut d = DiagBuilder2::error(format!("Item `{}` does not exist", name))
                .add_note("The following items are defined:");
            let mut names: Vec<_> = defs.iter().map(|(&k, _)| k).collect();
            names.sort(); // sorts by name ID, roughly equivalent to order of declaration
            for name in names {
                d = d.add_note(format!("- {}", name));
            }
            ctx.sess.emit(d);
            return Err(());
        }
    };
    debug!("elaborating {:?}", elab);

    // Generate the LLHD definition for whatever we're elaborating.
    match elab {
        Elaborate::VhdlEntity(_entity, arch) => {
            // let decl = ctx.vhdl.lldecl(arch);
            // println!("Architecture declared as {:?}", decl);
            let def = ctx.vhdl().lldef(arch)?;
            eprintln!("Architecture declared as {:?}", def);
        }
        Elaborate::VhdlPkg(pkg) => {
            use moore::vhdl::typeck::{Typeck, TypeckContext};
            let sbc = ctx.vhdl();
            let tyc = TypeckContext::new(&sbc);
            tyc.typeck(pkg);
            // use moore::vhdl::codegen::Codegen;
            // ctx.vhdl().codegen(pkg, &mut ())?;
        }
        Elaborate::Svlog(m) => {
            let mut cg = svlog::CodeGenerator::new(ctx.svlog);
            cg.emit_module(m)?;
            let code = cg.finalize();
            use llhd::visit::Visitor;
            let stdout = std::io::stdout();
            llhd::assembly::Writer::new(&mut stdout.lock()).visit_module(&code);
        }
    }
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
            let (a, b) = name.split_at(pos);
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
                    let (a, b) = rest.split_at(pos);
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
                Some(&rest[1..rest.len() - 1])
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
