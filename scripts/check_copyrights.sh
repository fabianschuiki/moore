#!/bin/bash
#
# This script checks the copyrights at the beginning of source files. Emits a
# patch to adjust the copyrights. Use as follows:
#
#     check_copyrights.sh | patch -p0

YEAR=$(date +%Y)
for FILE in $(find . -name "*.rs" -or -name "*.sh"); do
	sed -E "s/(Copyright \(c\) )[0-9]+(-[0-9]+)?/\12016-$YEAR/g" $FILE | diff -u $FILE -
done
