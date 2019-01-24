#!/bin/sh
VERSION=$(sed -n 's/^version = "\(.*\)"$/\1/p' Cargo.toml)
TMP=`mktemp`
echo "Checking for version `tput bold`$VERSION`tput sgr0`"
for FILE in $(find . -name Cargo.toml | grep -v '/target/'); do
	if rg -e '^version = ' -e '^moore-[^\s]+ = ' "$FILE" | rg -v "version = \"$VERSION\"" > $TMP; then
		echo
		echo "`tput bold``tput setaf 1`${FILE#./}:`tput sgr0`"
		sed -E 's/([0-9]+(\.[0-9]+)*)/'`tput bold``tput setaf 3`'\1'`tput sgr0`'/g' $TMP
	fi
done
