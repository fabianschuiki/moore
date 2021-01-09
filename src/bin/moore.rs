// Copyright (c) 2016-2020 Fabian Schuiki

//! A hardware description language compiler.

#[macro_use]
extern crate log;

use clap::{App, Arg, ArgMatches};
use llhd;
use llhd::opt::{Pass, PassContext};
use moore::common::score::NodeRef;
use moore::errors::*;
use moore::name::Name;
use moore::score::{ScoreBoard, ScoreContext};
use moore::svlog::{hir::Visitor as _, QueryDatabase as _};
use moore::*;
use std::path::Path;

#[derive(Debug)]
enum Language {
    Verilog,
    SystemVerilog,
    Vhdl,
}

fn main() {
    // Configure the logger.
    let mut builder = pretty_env_logger::formatted_builder();
    builder.parse_filters(
        std::env::var("MOORE_LOG")
            .ok()
            .as_ref()
            .map(|s| s.as_str())
            .unwrap_or("off"),
    );
    builder.try_init().unwrap();

    // Parse the command-line arguments.
    let matches = App::new(env!("CARGO_PKG_NAME"))
        .version(clap::crate_version!())
        .author(clap::crate_authors!())
        .about(clap::crate_description!())
        .arg(
            Arg::with_name("trace_scoreboard")
                .long("trace-scoreboard")
                .global(true),
        )
        .arg(
            Arg::with_name("verbosity-opts")
                .short("V")
                .help("Sets verbosity settings")
                .takes_value(true)
                .multiple(true)
                .number_of_values(1)
                .possible_values(&[
                    "types",
                    "expr-types",
                    "type-contexts",
                    "typeck",
                    "names",
                    "casts",
                    "ports",
                    "consts",
                    "insts",
                ])
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
            Arg::with_name("def")
                .short("D")
                .value_name("DEFINE")
                .help("Define a preprocesor macro")
                .multiple(true)
                .takes_value(true)
                .number_of_values(1),
        )
        .arg(
            Arg::with_name("preproc")
                .short("E")
                .help("Write preprocessed input files to stdout"),
        )
        .arg(
            Arg::with_name("dump-ast")
                .long("dump-ast")
                .help("Dump the parsed abstract syntax tree"),
        )
        .arg(
            Arg::with_name("check-syntax")
                .long("syntax")
                .help("Preprocess and check the input for syntax errors"),
        )
        .arg(
            Arg::with_name("emit_pkgs")
                .long("emit-pkgs")
                .help("Dump VHDL packages for debugging"),
        )
        .arg(
            Arg::with_name("opt-level")
                .short("O")
                .long("opt-level")
                .help("Sets optimization level applied to the output")
                .default_value("1")
                .takes_value(true)
                .number_of_values(1),
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
            Arg::with_name("output")
                .short("o")
                .long("output")
                .help("Output file (`-` for stdout)")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("output-format")
                .short("f")
                .long("format")
                .help("Output format")
                .takes_value(true)
                .possible_values(&["llhd", "mlir"]),
        )
        .arg(
            Arg::with_name("INPUT")
                .help("The input files to compile")
                .multiple(true)
                .required(true),
        )
        .get_matches();

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
            "casts" => Verbosity::CASTS,
            "ports" => Verbosity::PORTS,
            "consts" => Verbosity::CONSTS,
            "insts" => Verbosity::INSTS,
            _ => unreachable!(),
        };
    }
    session.opts.opt_level = matches.value_of("opt-level").unwrap().parse().unwrap();

    // Invoke the compiler.
    score(&session, &matches);
}

fn score(sess: &Session, matches: &ArgMatches) {
    use crate::name::get_name_table;
    let svlog_arenas = svlog::GlobalArenas::default();

    // Prepare a list of include paths.
    let include_paths: Vec<_> = match matches.values_of("inc") {
        Some(args) => args.map(|x| std::path::Path::new(x)).collect(),
        None => Vec::new(),
    };

    let defines: Vec<_> = match matches.values_of("def") {
        Some(args) => args
            .map(|x| {
                let mut iter = x.split("=");
                (iter.next().unwrap(), iter.next())
            })
            .collect(),
        None => Vec::new(),
    };

    // Establish into which library the entities will be compiled. Later on this
    // should be made configurable per entity.
    let lib = get_name_table().intern(matches.value_of("lib").unwrap_or("work"), true);

    // Parse the input files.
    let mut failed = false;
    let mut asts = Vec::new();
    for filename in matches.values_of("INPUT").unwrap() {
        if filename.is_empty() {
            continue;
        }

        // Detect the file type.
        let language = match Path::new(&filename).extension().and_then(|s| s.to_str()) {
            Some("sv") | Some("svh") => Language::SystemVerilog,
            Some("v") | Some("vh") => Language::Verilog,
            Some("vhd") | Some("vhdl") => Language::Vhdl,
            Some(ext) => {
                sess.emit(
                    DiagBuilder2::warning(format!("ignoring `{}`", filename)).add_note(format!(
                        "Cannot determine language from extension `.{}`",
                        ext
                    )),
                );
                continue;
            }
            None => {
                sess.emit(
                    DiagBuilder2::warning(format!("ignoring `{}`", filename)).add_note(format!(
                        "No file extension that can be used to guess language"
                    )),
                );
                continue;
            }
        };

        // Add the file to the source manager.
        let sm = source::get_source_manager();
        let source = match sm.open(&filename) {
            Some(s) => s,
            None => {
                sess.emit(DiagBuilder2::fatal(format!(
                    "unable to open `{}`",
                    filename
                )));
                continue;
            }
        };

        // Parse the file.
        match language {
            Language::SystemVerilog | Language::Verilog => {
                let preproc = svlog::preproc::Preprocessor::new(source, &include_paths, &defines);
                if matches.is_present("preproc") {
                    for token in preproc {
                        print!(
                            "{}",
                            match token {
                                Ok((_token, span)) => span.extract(),
                                Err(diag) => {
                                    sess.emit(diag);
                                    failed = true;
                                    continue;
                                }
                            }
                        );
                    }
                    continue;
                }

                let lexer = svlog::lexer::Lexer::new(preproc);
                match svlog::parser::parse(lexer, &svlog_arenas.ast) {
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
    if matches.is_present("preproc") {
        return;
    }

    // Dump the AST if so requested.
    if matches.is_present("dump-ast") {
        println!("{:#99?}", asts);
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

    // Stop processing if requested.
    if matches.is_present("check-syntax") {
        std::process::exit(0);
    }

    // Create the scoreboard and add the initial map of libraries.
    let arenas = score::Arenas::new();
    let sb = ScoreBoard::new(&arenas);
    let vhdl_sb = vhdl::score::ScoreBoard::new(&arenas.vhdl);
    let svlog_sb = svlog::GlobalContext::new(&sess, &svlog_arenas);

    // Elaborate the requested entities or modules.
    {
        let vhdl_phases = vhdl::lazy::LazyPhaseTable::new(&vhdl_sb);
        let ctx = ScoreContext {
            sess: sess,
            sb: &sb,
            vhdl: &vhdl_sb,
            vhdl_phases: &vhdl_phases,
            svlog: &svlog_sb,
        };
        let lib_id = ctx.add_library(lib, &asts);
        if let Some(names) = matches.values_of("elaborate") {
            debug!("lib_id = {:?}", lib_id);
            debug!("{:?}", sb);
            for name in names {
                match elaborate_name(matches, &ctx, lib_id, name) {
                    Ok(_) => (),
                    Err(_) => failed = true,
                };
            }
            if sess.failed() {
                failed = true;
            }
        }
    }
    if failed || sess.failed() {
        std::process::exit(1);
    }

    // Extract the populated LLHD modules from the scoreboards and link them
    // together.
    let _vhdl_module = vhdl_sb.llmod.into_inner();

    // Emit the module.
    // TODO: Re-enable this once the VHDL crate has been moved over to llhd v0.8.
    // llhd::assembly::write_module(&mut std::io::stdout().lock(), &vhdl_module);

    if sess.failed() {
        std::process::exit(1);
    }
}

/// Resolve an entity/module specificaiton of the form `[lib.]entity[.arch]` for
/// elaboration.
fn elaborate_name(
    matches: &ArgMatches,
    ctx: &ScoreContext,
    lib_id: score::LibRef,
    input_name: &str,
) -> Result<(), ()> {
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
            let def = ctx.vhdl().llunit(arch)?;
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
            // Emit the detailed type analysis if requested.
            if ctx.sess.has_verbosity(Verbosity::TYPES) {
                use svlog::Context;
                TypeVerbosityVisitor(ctx.svlog, ctx.svlog.default_param_env())
                    .visit_node_with_id(m, false);
            }

            // Emit the instantiation details if requested.
            if ctx.sess.has_verbosity(Verbosity::INSTS) {
                svlog::InstVerbosityVisitor::new(ctx.svlog).visit_node_with_id(m, false);
            }

            let mut cg = svlog::CodeGenerator::new(ctx.svlog);
            cg.emit_module(m)?;
            let mut module = cg.finalize();
            let pass_ctx = PassContext;
            if ctx.sess.opts.opt_level > 0 {
                llhd::pass::ConstFolding::run_on_module(&pass_ctx, &mut module);
                // llhd::pass::VarToPhiPromotion::run_on_module(&pass_ctx, &mut module); // broken in llhd 0.13
                llhd::pass::DeadCodeElim::run_on_module(&pass_ctx, &mut module);
                llhd::pass::GlobalCommonSubexprElim::run_on_module(&pass_ctx, &mut module);
                llhd::pass::InstSimplification::run_on_module(&pass_ctx, &mut module);
                llhd::pass::DeadCodeElim::run_on_module(&pass_ctx, &mut module);
            }

            // Decide what format to use for the output.
            emit_output(matches, ctx, &module)?;
        }
    }
    Ok(())
}

#[derive(Debug)]
enum OutputFormat {
    Llhd,
    Mlir,
}

fn emit_output(
    matches: &ArgMatches,
    ctx: &ScoreContext,
    module: &llhd::ir::Module,
) -> Result<(), ()> {
    // Check if the user has provided an explicit output format.
    let fmt = match matches.value_of("output-format") {
        Some("llhd") => Some(OutputFormat::Llhd),
        Some("mlir") => Some(OutputFormat::Mlir),
        Some(x) => {
            ctx.sess.emit(DiagBuilder2::fatal(format!(
                "unknown output format: `{}`",
                x
            )));
            return Err(());
        }
        _ => None,
    };

    // Check if the output format can be inferred from the output file suffix.
    let fmt = fmt.or_else(|| {
        match matches
            .value_of("output")
            .and_then(|x| Path::new(x).extension())
            .and_then(|x| x.to_str())
        {
            Some("llhd") => Some(OutputFormat::Llhd),
            Some("mlir") => Some(OutputFormat::Mlir),
            _ => None,
        }
    });

    // Otherwise fall back to the LLHD default output format.
    let fmt = fmt.unwrap_or(OutputFormat::Llhd);
    debug!("Using {:?} output format", fmt);

    // Open the output.
    let stdout = std::io::stdout();
    let output: Box<dyn std::io::Write> = match matches.value_of("output") {
        Some("-") | None => Box::new(stdout.lock()),
        Some(x) => Box::new(std::fs::File::create(x).map_err(|e| {
            ctx.sess.emit(
                DiagBuilder2::fatal(format!("unable to create file: `{}`", x))
                    .add_note(format!("{}", e)),
            );
            ()
        })?),
    };

    // Emit the appropriate output.
    match fmt {
        OutputFormat::Llhd => llhd::assembly::write_module(output, &module),
        OutputFormat::Mlir => llhd::mlir::write_module(output, &module),
    };
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

/// A visitor that emits detailed type information to stdout.
pub struct TypeVerbosityVisitor<'a, 'gcx>(&'a svlog::GlobalContext<'gcx>, svlog::ParamEnv);

impl<'a, 'gcx> svlog::hir::Visitor<'gcx> for TypeVerbosityVisitor<'a, 'gcx> {
    type Context = svlog::GlobalContext<'gcx>;

    fn context(&self) -> &Self::Context {
        self.0
    }

    fn visit_expr(&mut self, expr: &'gcx svlog::hir::Expr<'gcx>, lvalue: bool) {
        self.print(expr.id);
        svlog::hir::walk_expr(self, expr, lvalue);
    }

    fn visit_var_decl(&mut self, decl: &'gcx svlog::hir::VarDecl) {
        self.print(decl.id);
        svlog::hir::walk_var_decl(self, decl);
    }
}

impl<'a, 'gcx> TypeVerbosityVisitor<'a, 'gcx> {
    fn print(&mut self, id: NodeId) {
        use svlog::Context;
        let span = self.0.span(id);
        let ext = span.extract();
        let line = span.begin().human_line();

        // Report the type.
        if let Ok(ty) = self.0.type_of(id, self.1) {
            println!("{}: type({}) = {}", line, ext, ty);
        }

        // Report the cast type.
        if let Some(cast) = self.0.cast_type(id, self.1) {
            println!("{}: cast_type({}) = {}", line, ext, cast.ty);
            println!("{}: cast_chain({}) = {}", line, ext, cast);
        }

        // Report the self-determined type.
        if let Some(ty) = self.0.self_determined_type(id, self.1) {
            println!("{}: self_type({}) = {}", line, ext, ty);
        }

        // Report the operation type.
        if let Some(ty) = self.0.operation_type(id, self.1) {
            println!("{}: operation_type({}) = {}", line, ext, ty);
        }

        // Report the type context.
        if let Some(ty) = self.0.type_context(id, self.1) {
            println!(
                "{}: type_context({}) = {}",
                line,
                ext,
                match ty {
                    svlog::typeck::TypeContext::Type(ty) => format!("{}", ty),
                    svlog::typeck::TypeContext::Bool => "<bool>".to_string(),
                }
            );
        }
    }
}
