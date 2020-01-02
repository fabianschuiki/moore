//! A SystemVerilog parser generator.

use anyhow::{anyhow, Result};
use clap::{App, Arg};

mod ast;
mod parser;

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

    let _context = Context {};
    let grammar = parse_grammar(&std::fs::read_to_string(
        matches.value_of("grammar").unwrap(),
    )?)?;

    println!("{:#?}", grammar);
    Ok(())
}

/// Parse a grammar string.
pub fn parse_grammar(input: impl AsRef<str>) -> Result<ast::Grammar> {
    parser::GrammarParser::new()
        .parse(input.as_ref())
        .map_err(|e| anyhow!("Grammar syntax error: {}", e))
}

struct Context {}
