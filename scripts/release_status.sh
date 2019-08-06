#!/bin/sh
echo `tput bold`"Versions:"`tput sgr0`
rg '^version = ' -g '*.toml'
echo
echo `tput bold`"Dependencies (moore-*):"`tput sgr0`
rg '^moore-[^\s]+ = ' -g '*.toml'
echo
echo `tput bold`"Dependencies (llhd):"`tput sgr0`
rg '^llhd = ' -g '*.toml'
