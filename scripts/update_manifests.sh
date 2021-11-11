#!/bin/bash
set -e
regex='^[0-9]+(\.[0-9]+){2}$'
if ! [[ "$1" =~ $regex ]]; then
    echo "invalid version \"$1\"" >&2
    exit 1
fi
MANIFESTS=$(find . -name Cargo.toml)
sed -E "s/^((moore-.+?)?version = )\"[0-9.]+\"(.*$)/\1\"$1\"\3/" -i $MANIFESTS
