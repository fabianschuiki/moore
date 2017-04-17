#!/bin/bash
set -e
cd pulpino
git init
git remote add origin https://github.com/pulp-platform/pulpino.git
git fetch --depth=1 origin
git checkout origin/master
./update-ips.py
