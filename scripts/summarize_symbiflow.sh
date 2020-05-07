#!/bin/bash
set -e

# Locate the log directory.
if [ $# -ge 1 ]; then
    LOG_DIR=$1
    shift
else
    echo "usage: $0 SV_TESTS_LOG_DIR" >&2
    exit1
fi

# Summarize and count the distinct error messages
find $LOG_DIR -name "*.log" | xargs grep --no-filename -E "^(error|fatal):" | sort | uniq -c | sort -rn | less
