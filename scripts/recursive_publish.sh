#!/bin/sh
set -e
(cd src/common && cargo publish "$@") &&
(cd src/derive && cargo publish "$@") &&
sleep 30 && (cargo install lazy_static > /dev/null 2>&1 || true)
(cd src/svlog/syntax && cargo publish "$@") &&
(cd src/vhdl/syntax && cargo publish "$@")
sleep 30 && (cargo install lazy_static > /dev/null 2>&1 || true)
(cd src/svlog && cargo publish "$@") &&
(cd src/vhdl && cargo publish "$@")
sleep 30 && (cargo install lazy_static > /dev/null 2>&1 || true)
cargo publish "$@"
