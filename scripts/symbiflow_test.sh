#!/bin/bash
set -e

# Locate the release binary.
CRATE_DIR=$(cargo metadata --format-version 1 | sed -n 's/.*"workspace_root":"\([^"]*\)".*/\1/p')
TARGET_DIR=$(cargo metadata --format-version 1 | sed -n 's/.*"target_directory":"\([^"]*\)".*/\1/p')
GIT_REV=$(git rev-parse --short HEAD)
MOORE=$(readlink -f "$TARGET_DIR/release/moore")
if ! [ -e $MOORE ]; then
    cargo build --release
fi
if ! [ -e $MOORE ]; then
    echo "error: $MOORE does not exist" >&2
    exit 1
fi

# Print the current version.
echo "binary:   " $MOORE
echo "version:  " $($MOORE --version)

# Locate the sv-tests directory.
if [ $# -ge 1 ]; then
    SV_TESTS_DIR=$1
    shift
fi
if [ -z "$SV_TESTS_DIR" ]; then
    echo "error: SV_TESTS_DIR not set or provided" >&2
    echo "usage: $0 [SV_TESTS_DIR]" >&2
    echo "   or: env SV_TESTS_DIR=... $0" >&2
    exit 1
fi
if ! [ -d $SV_TESTS_DIR ]; then
    echo "error: $SV_TESTS_DIR does not exist" >&2
    exit 1
fi
echo "sv-tests: " $SV_TESTS_DIR

# Run the tests.
cd "$SV_TESTS_DIR"
export PATH="$(dirname $MOORE):$PATH"
SV_TESTS_BIN="make RUNNERS+=moore_parse RUNNERS+=moore"

$SV_TESTS_BIN versions -B
if [ $# -ge 1 ]; then
    for t in $@; do
        echo $t
        $SV_TESTS_BIN ./out//logs/moore_parse/$t.log ./out//logs/moore/$t.log -B
    done
else
    $SV_TESTS_BIN clean
    $SV_TESTS_BIN generate-tests -j$(nproc)
    $SV_TESTS_BIN tests -j$(nproc)
fi
$SV_TESTS_BIN report

LOG_FILE="`date +%Y-%m-%d-%H%M`-$GIT_REV.csv"
cp out/report/report.csv $CRATE_DIR/test/history/symbiflow/$LOG_FILE
