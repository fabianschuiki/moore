//! A SystemVerilog parser generator.

#[macro_use]
extern crate log;

pub mod ast;
pub mod codegen;
pub mod context;
pub mod factor;
pub mod ll;
pub mod opt;
pub mod parser;
pub mod populate;

use crate::context::{Context, ContextArena};
use anyhow::{anyhow, Result};
use clap::{App, Arg};
use std::{fs::File, io::Write};

fn main() -> Result<()> {
    let matches = App::new("svlog-pargen")
        .version(clap::crate_version!())
        .author(clap::crate_authors!())
        .about("A parser generator for SystemVerilog.")
        .arg(
            Arg::with_name("grammar")
                .takes_value(true)
                .required(true)
                .number_of_values(1),
        )
        .arg(
            Arg::with_name("dump-init")
                .short("d")
                .long("dump-init")
                .help("Dump the grammar after basic factorization.")
                .takes_value(true)
                .number_of_values(1),
        )
        .get_matches();

    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .init();

    let grammar = parse_grammar(&std::fs::read_to_string(
        matches.value_of("grammar").unwrap(),
    )?)?;

    // Parse the grammar and populate the context.
    let arena = ContextArena::default();
    let mut context = Context::new(&arena);
    populate::add_ast(&mut context, grammar);
    info!(
        "Grammar has {} productions, {} nonterminals, {} terminals",
        context.prods.values().flatten().count(),
        context.nonterms().count(),
        context.terms().count(),
    );

    // Perform initial minimization of the grammar to remove redundancies.
    context.minimize();

    // Perform basic LL(1) transformations.
    for i in 1.. {
        info!("Simplifying grammar (step {})", i);
        let mut modified = false;
        modified |= factor::remove_epsilon_derivation(&mut context);
        modified |= factor::remove_indirect_left_recursion(&mut context);
        modified |= factor::remove_direct_left_recursion(&mut context);
        context.minimize();
        if !modified {
            break;
        }
    }
    factor::left_factorize_simple(&mut context);
    context.minimize();
    info!(
        "Grammar has {} productions, {} nonterminals, {} terminals",
        context.prods.values().flatten().count(),
        context.nonterms().count(),
        context.terms().count(),
    );

    // Dump this initial grammar if requested.
    if let Some(path) = matches.value_of("dump-init") {
        info!("Dumping grammar to `{}`", path);
        let mut f = File::create(path)?;
        for ps in context.prods.values() {
            for p in ps {
                write!(f, "{}\n", p)?;
            }
        }
    }

    // Optimize the grammar.
    for i in 1..2 {
        info!("Optimizing grammar (step {})", i);
        opt::optimize(&mut context);
        context.minimize();
    }

    // ll::build_ll(&mut context);
    // ll::dump_ambiguities(&context);

    // debug!("LL(1) Table:");
    // for (nt, ts) in &context.ll_table {
    //     for (t, ps) in ts {
    //         for p in ps {
    //             debug!("  [{}, {}] = {}", nt, t, p);
    //         }
    //     }
    // }

    // codegen::codegen(&mut context);

    Ok(())
}

/// Parse a grammar string.
pub fn parse_grammar(input: impl AsRef<str>) -> Result<ast::Grammar> {
    parser::GrammarParser::new()
        .parse(input.as_ref())
        .map_err(|e| anyhow!("Grammar syntax error: {}", e))
}
