//! A SystemVerilog parser generator.

#[macro_use]
extern crate log;

mod ast;
mod context;
mod ll;
mod parser;
mod populate;

use crate::context::{Context, ContextArena};
use anyhow::{anyhow, Result};
use clap::{App, Arg};

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
        .get_matches();

    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .init();

    let grammar = parse_grammar(&std::fs::read_to_string(
        matches.value_of("grammar").unwrap(),
    )?)?;

    let arena = ContextArena::default();
    let mut context = Context::new(&arena);
    populate::add_ast(&mut context, grammar);

    info!(
        "Grammar has {} productions, {} nonterminals, {} terminals",
        context.prods.values().flatten().count(),
        context.nonterms().count(),
        context.terms().count(),
    );
    debug!("Grammar:");
    for ps in context.prods.values() {
        for p in ps {
            debug!("  {}", p);
        }
    }

    ll::build_ll(&mut context);

    Ok(())
}

/// Parse a grammar string.
pub fn parse_grammar(input: impl AsRef<str>) -> Result<ast::Grammar> {
    parser::GrammarParser::new()
        .parse(input.as_ref())
        .map_err(|e| anyhow!("Grammar syntax error: {}", e))
}
