#!/bin/sh
set -e
(cd src/common && cargo publish "$@")
(cd src/svlog/syntax && cargo publish "$@")
(cd src/svlog && cargo publish "$@")
(cd src/vhdl/syntax && cargo publish "$@")
(cd src/vhdl && cargo publish "$@")
