#!/bin/bash
set -e

# Locate the release binary.
TARGET_DIR=$(cargo metadata --format-version 1 | sed -n 's/.*"target_directory":"\([^"]*\)".*/\1/p')
MOORE=$(readlink -f "$TARGET_DIR/debug/examples/pargen-parse")
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

# Find the input files.
NUM_TESTS=0
NUM_PASS=0
CPASS=`tput setaf 2`
CFAIL=`tput setaf 1; tput bold`
CRST=`tput sgr0`

LOG_PASSED="symbiflow_pargen_passed.log"
LOG_FAILED="symbiflow_pargen_failed.log"
[ ! -e $LOG_PASSED ] || rm $LOG_PASSED
[ ! -e $LOG_FAILED ] || rm $LOG_FAILED

for f in $(find "$SV_TESTS_DIR/tests" -type f -iname "*.sv"); do
    n=${f#"$SV_TESTS_DIR/"}
    if grep -e ":should_fail: 1" -e ":should_fail_because:" $f -q; then
        continue
    fi
    NUM_TESTS=$((NUM_TESTS + 1))
    fs=$(grep ":files:" $f | cut -d" " -f2- || true)
    cmd="$MOORE $f $fs"
    if $cmd >/dev/null 2>&1; then
        NUM_PASS=$((NUM_PASS + 1))
        echo -n "  ${CPASS}passed${CRST}"
        log=$LOG_PASSED
    else
        echo -n "  ${CFAIL}FAILED${CRST}"
        log=$LOG_FAILED
    fi
    echo $cmd >> $log
    echo "  $n"
done

echo
echo "$((NUM_TESTS - NUM_PASS)) failed, $NUM_PASS passed, $NUM_TESTS total"
