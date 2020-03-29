#!/bin/bash
set -e
cd $(dirname ${BASH_SOURCE[0]})/pargen
env RUST_LOG="info" cargo run --release -- ../grammar.pg -d ../grammar.init.log -f ../grammar.final.log -s ../grammar.states.log -c ../grammar.conflicts.log -o ../grammar.rs
