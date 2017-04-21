#!/bin/bash
# Copyright (c) 2017 Fabian Schuiki
## This script runs the source files in tests through the compiler.

set -e
CRST=`tput sgr0`
CNAME=`tput bold`
CFAIL=`tput setaf 1`
CPASS=`tput setaf 2`

TMP=`mktemp`
TESTS_DIR="$(dirname "${BASH_SOURCE[0]}")"
MOORE="$TESTS_DIR/../target/debug/moore"

NUM_PASS=0
NUM_FAIL=0
while read -d $'\0' SRCFILE; do
	echo -n "testing ${CNAME}$SRCFILE${CRST} ..."
	[ ! -e .moore ] || rm .moore

	if ! $MOORE compile $SRCFILE &> $TMP; then
		echo " ${CFAIL}compilation failed${CRST}"
		cat $TMP
		COMPILE_RESULT=false
	else
		echo
		COMPILE_RESULT=true
	fi

	while read TOP; do
		echo -n "  elaborating ${CNAME}$TOP${CRST} ..."
		if ! $COMPILE_RESULT &> $TMP || ! $MOORE elaborate $TOP &> $TMP; then
			NUM_FAIL=$((NUM_FAIL+1))
			echo " ${CFAIL}failed${CRST}"
			cat $TMP
		else
			NUM_PASS=$((NUM_PASS+1))
			echo " ${CPASS}passed${CRST}"
		fi
	done < <(grep -o -E '@elab\s+.*' $SRCFILE | cut -f 2 -d " ")
done < <(find $TESTS_DIR -name "*.sv" -print0)

if [[ NUM_FAIL > 0 ]]; then
	echo
	echo "  ${CNAME}result: ${CFAIL}$NUM_FAIL/$((NUM_FAIL+NUM_PASS)) failed${CRST}"
	echo
else
	echo
	echo "  ${CNAME}result: ${CPASS}$NUM_PASS passed${CRST}"
	echo
fi
