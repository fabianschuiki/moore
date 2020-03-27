#[macro_use]
extern crate log;

use anyhow::{anyhow, bail, Result};
use clap::{App, Arg};
use moore_common::source::get_source_manager;
use moore_svlog_syntax::{lexer::Lexer, parser::pargen_parse, preproc::Preprocessor};

fn main() -> Result<()> {
    let matches = App::new("pargen-parse")
        .version(clap::crate_version!())
        .author(clap::crate_authors!())
        .arg(
            Arg::with_name("INPUT")
                .help("The input files to compile")
                .multiple(true)
                .required(true),
        )
        .get_matches();

    env_logger::Builder::from_default_env()
        .format_timestamp(None)
        .init();

    let mut failed = false;
    for input in matches.values_of("INPUT").into_iter().flatten() {
        info!("Parsing `{}`", input);
        let sm = get_source_manager();
        let source = match sm.open(&input) {
            Some(s) => s,
            None => bail!("Unable to open `{}`", input),
        };
        let preproc = Preprocessor::new(source, &[], &[]);
        let lexer = Lexer::new(preproc);
        match pargen_parse(lexer) {
            Ok(ast) => debug!("{:#?}", ast),
            Err(()) => failed = true,
        }
    }

    if failed {
        Err(anyhow!("Syntax errors occurred"))
    } else {
        Ok(())
    }
}
