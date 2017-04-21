#!/bin/bash
set -e
CRST=`tput sgr0`
CNAME=`tput bold`
CFAIL=`tput setaf 1`
CPASS=`tput setaf 2`
TMP=`mktemp`
TESTS_DIR="$(dirname "${BASH_SOURCE[0]}")"
MOORE="$TESTS_DIR/../target/debug/moore"
find $TESTS_DIR -name "*.sv" -print0 | while read -d $'\0' SRCFILE; do
	echo -n "testing ${CNAME}$SRCFILE${CRST} ..."
	[ ! -e .moore ] || rm .moore

	if ! $MOORE compile $SRCFILE &> $TMP; then
		echo " ${CFAIL}compilation failed${CRST}"
		cat $TMP
		continue
	else
		echo
	fi

	grep -o -E '@elab\s+.*' $SRCFILE | cut -f 2 -d " " | while read TOP; do
		echo -n "  elaborating ${CNAME}$TOP${CRST} ..."
		if ! $MOORE elaborate $TOP &> $TMP; then
			echo " ${CFAIL}failed${CRST}"
			cat $TMP
		else
			echo " ${CPASS}passed${CRST}"
		fi
	done
done
