#!/bin/sh
echo `tput bold`"Versions:"`tput sgr0`
rg '^version = ' -g '*.toml'
echo
echo `tput bold`"Dependencies:"`tput sgr0`
rg '^moore-[^\s]+ = ' -g '*.toml'
