#!/bin/bash
set -e
git clone --depth 1 https://github.com/pulp-platform/pulpino.git
cd pulpino
./update-ips.py
