#!/usr/bin/env python3
# This script analyzes regressions in sv-tests.

import os
import pandas as pd
from pathlib import Path
import argparse

# Parse the command line arguments.
parser = argparse.ArgumentParser()
parser.add_argument("-f", "--fixes", action="store_true", help="print a list of fixes")
parser.add_argument("-r", "--regressions", action="store_true", help="print a list of regressions")
args = parser.parse_args()

# Find the history CSVs.
history_dir = (Path(__file__).parent/".."/"test"/"history"/"symbiflow").resolve()
csv_paths = sorted(history_dir.glob("*.csv"))

# Read the CSVs.
csvs = list()
final = None
for csv_path in csv_paths:
    name = csv_path.stem
    df = pd.read_csv(csv_path).sort_values("name")
    final = df
    csvs.append((name, df))

# Analyze regressions
cred = "\x1b[31m"
cgreen = "\x1b[32m"
cbold = "\x1b[1m"
cnone = "\x1b[0m"
prev = None
for name, df in csvs:
    total = df.shape[0]
    passed_parse = df["moore_parse"].sum()
    passed_comp = df["moore"].sum()
    print(f"{cbold}{name}:{cnone}")

    if prev is not None:
        diff = prev.merge(df, on="name", how="outer")

        # Find transitions from failing to passing.
        new_pass_parse = pd.DataFrame(diff[(diff["moore_parse_x"] == False) & (diff["moore_parse_y"] != False)]["name"])
        new_pass_comp = pd.DataFrame(diff[(diff["moore_x"] == False) & (diff["moore_y"] != False)]["name"])
        new_pass_parse["moore_parse"] = True;
        new_pass_comp["moore"] = True;
        new_pass = new_pass_parse.merge(new_pass_comp, on="name", how="outer").merge(final, on="name", suffixes=("","_final"))

        # Find transitions from passing to failing.
        new_fail_parse = pd.DataFrame(diff[(diff["moore_parse_x"] != False) & (diff["moore_parse_y"] == False)]["name"])
        new_fail_comp = pd.DataFrame(diff[(diff["moore_x"] != False) & (diff["moore_y"] == False)]["name"])
        new_fail_parse["moore_parse"] = True;
        new_fail_comp["moore"] = True;
        new_fail = new_fail_parse.merge(new_fail_comp, on="name", how="outer").merge(final, on="name", suffixes=("","_final"))

        # Print fixes.
        fixes_comp = (new_pass["moore"] == True) & (new_pass["moore_final"] == True)
        fixes_parse = (new_pass["moore_parse"] == True) & (new_pass["moore"] != True) & (new_pass["moore_parse_final"] == True)
        if args.fixes:
            if fixes_comp.sum():
                print("  Compiler fixes:")
                for name in new_pass[fixes_comp]["name"]:
                    print(f"    {cgreen}{name}{cnone}")
            if fixes_parse.sum():
                print("  Parser fixes:")
                for name in new_pass[fixes_parse]["name"]:
                    print(f"    {cgreen}{name}{cnone}")

        # Print regressions.
        regrs_comp = (new_fail["moore"] == True) & (new_fail["moore_final"] != True)
        regrs_parse = (new_fail["moore_parse"] == True) & (new_fail["moore"] != True) & (new_fail["moore_parse_final"] != True)
        if args.regressions:
            if regrs_comp.sum():
                print("  Compiler regressions:")
                for name in new_fail[regrs_comp]["name"]:
                    print(f"    {cred}{name}{cnone}")
            if regrs_parse.sum():
                print("  Parser regressions:")
                for name in new_fail[regrs_parse]["name"]:
                    print(f"    {cred}{name}{cnone}")

        num_fixes_comp = fixes_comp.sum();
        num_fixes_parse = fixes_parse.sum();
        num_regrs_comp = regrs_comp.sum();
        num_regrs_parse = regrs_parse.sum();
        print(f"  Compiler: {cbold}{cgreen}{num_fixes_comp}{cnone} fixes, {cbold}{cred}{num_regrs_comp}{cnone} regressions")
        print(f"  Parser: {cbold}{cgreen}{num_fixes_parse}{cnone} fixes, {cbold}{cred}{num_regrs_parse}{cnone} regressions")

    print(f"  {passed_parse} parse / {passed_comp} compile / {total} total")
    prev = df
