#!/usr/bin/env python2
# Francesco Conti <f.conti@unibo.it>
# Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
#
# Copyright (C) 2016 ETH Zurich, University of Bologna.
# All rights reserved.

import sys, os, subprocess, ipstools, stat

ipdb = ipstools.IPDatabase(ips_dir="./ips", rtl_dir="./rtl", vsim_dir="./vsim")

def export_ip(ip):
	parts = list()
	for (s,subip) in ip.sub_ips.items():
		parts.append(export_subip(subip, "${SRC}/ips/"+ip.ip_path))
	return "\n\n".join([p for p in parts if p])

def export_subip(ip, path):
	if not ("all" in ip.targets or "rtl" in ip.targets):
		return ""
	files = ip.files
	flags = list()
	cmds = list()
	for i in ip.incdirs:
		flags.append("-I %s/%s" % (path,i))
	for f in files:
		cmd = list()
		cmd.append("${MOORE} ${MOORE_FLAGS}")
		cmd += flags
		cmd.append("%s/%s" % (path, f))
		cmds.append(" ".join(cmd))
	return "\n".join(cmds)

with open("compile_moore.sh", "wb") as f:
	f.write("# Pulpino compile script for moore\n")
	for (i,ip) in ipdb.ip_dic.items():
		f.write("\n# %s\n" % i)
		f.write(export_ip(ip))
		f.write("\n")
