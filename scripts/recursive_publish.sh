#!/bin/sh
set -e
(cd src/common && cargo publish "$@") &&
sleep 10 && (cargo install lazy_static > /dev/null 2>&1 || true)
(cd src/derive && cargo publish "$@") &&
sleep 10 && (cargo install lazy_static > /dev/null 2>&1 || true)
(cd src/svlog/syntax && cargo publish "$@") &&
sleep 10 && (cargo install lazy_static > /dev/null 2>&1 || true)
(cd src/svlog && cargo publish "$@") &&
sleep 10 && (cargo install lazy_static > /dev/null 2>&1 || true)
(cd src/vhdl/syntax && cargo publish "$@")
sleep 10 && (cargo install lazy_static > /dev/null 2>&1 || true)
(cd src/vhdl && cargo publish "$@")
sleep 10 && (cargo install lazy_static > /dev/null 2>&1 || true)
cargo publish "$@"
