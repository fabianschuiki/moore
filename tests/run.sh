#!/bin/bash
# Copyright (c) 2017-2018 Fabian Schuiki
# This script runs the source files in tests through the compiler.

set -e
CRST=`tput sgr0`
CBOLD=`tput bold`
CFAIL=`tput bold``tput setaf 1`
CPASS=`tput setaf 2`

TMPERR=`mktemp`
TMPOUT=`mktemp`
TMPDIFFEXP=`mktemp`
TMPDIFFACT=`mktemp`
TESTS_DIR="$(dirname "${BASH_SOURCE[0]}")"
# MOORE="cargo run --"
(cd "$TESTS_DIR/.." && cargo build)
MOORE="$TESTS_DIR/../target/debug/moore"

ALL=false
if [ "$1" = "--all" ] || [ "$1" = "-a" ]; then
	ALL=true
fi

status() {
	printf "${CBOLD}%12s${CRST}  %s" "$1" "$2"
}

check() {
	status "$1" "$2"
	if ! "${@:3}" >$TMPOUT 2>$TMPERR; then
		NUM_FAIL=$((NUM_FAIL+1))
		echo "  [${CFAIL}failed${CRST}]"
		cat $TMPOUT
		cat $TMPERR
	else
		NUM_PASS=$((NUM_PASS+1))
		echo "  [${CPASS}passed${CRST}]"
	fi
}

extract_comments() {
	sed -n 's#^\s*\(///*\|---*\)\s*\(.*\)#\2#p' | grep -v '^!'
}

extract_elabs() {
	sed -n 's#^@\s*elab\s*##p'
}

extract_output() {
	sed -nE 's#^\|\s?##p'
}

check_diff() {
	if ! diff -w $1 $2; then
		echo "===== ${CBOLD}expected code${CRST} ====="
		cat $1
		echo "===== ${CBOLD}actual code${CRST} ====="
		cat $2
		false
	fi
}

test_file() {
	SRCFILE="$1"
	ARGS=()
	TOPS=()
	for e in $(cat "$1" | extract_comments | extract_elabs); do
		ARGS+=(-e $e)
		TOPS+=($e)
	done
	cat "$1" | extract_comments | extract_output > $TMPDIFFEXP
	if [ ${#ARGS[@]} -gt 0 ]; then
		LOG="$SRCFILE(${TOPS[@]})"
		check elaborate "$LOG" $MOORE "${ARGS[@]}" $SRCFILE
		cp $TMPOUT $TMPDIFFACT
		if [ -s $TMPDIFFEXP ]; then
			check codegen "$LOG" check_diff $TMPDIFFEXP $TMPDIFFACT
		fi
	fi
}

NUM_PASS=0
NUM_FAIL=0
while read -d $'\0' SRCFILE; do
	if ! $ALL && grep -E '@exclude' $SRCFILE >/dev/null; then
		continue
	fi
	check parse $SRCFILE $MOORE $SRCFILE
	test_file $SRCFILE
done < <(find $TESTS_DIR -name "*.sv" -print0 -or -name "*.vhd" -print0 | sort -z)

echo
if [ $NUM_FAIL -gt 0 ]; then
	echo "  ${CBOLD}result: ${CFAIL}$NUM_FAIL/$((NUM_FAIL+NUM_PASS)) failed${CRST}"
else
	echo "  ${CBOLD}result: ${CPASS}$NUM_PASS passed${CRST}"
fi
echo
[ $NUM_FAIL = 0 ] # return non-zero exit code if anything failed
