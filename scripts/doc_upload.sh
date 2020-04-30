#!/bin/bash
# Copyright (c) 2016-2020 Fabian Schuiki
# This script uploads the documentation in target/doc to the repo's
# GitHub pages. Requires the GH_TOKEN env var to be set.

set -e

# Generate documentaiton.
cargo doc

# Assemble comit message.
COMMIT=`git rev-parse --short HEAD`
MSG="Documentation for moore ($COMMIT)"

# Create redirect to moore documentation.
echo "<meta http-equiv=refresh content=0;url=moore/index.html>" > target/doc/index.html

# Clone ghp-import if needed and import target/doc directory.
[ -d ghp-import ] || git clone https://github.com/davisp/ghp-import
ghp-import/ghp_import.py -n -m "$MSG" target/doc

# Push to GitHub.
git push -fq https://${GH_TOKEN}@github.com/fabianschuiki/moore.git gh-pages
