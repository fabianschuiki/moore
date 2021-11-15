import re
import os
import subprocess
import lit.formats
import lit.llvm

lit.llvm.initialize(lit_config, config)
from lit.llvm import llvm_config

config.name = "Moore"
config.test_format = lit.formats.ShTest(True)
config.suffixes = [".v", ".sv", ".vhd", ".vhdl", ".mlir", ".llhd"]
config.excludes = ["third-party", "svlog", "vhdl"]
config.test_exec_root = "/tmp/moore-lit"

config.llvm_tools_dir = os.path.realpath(os.path.dirname(__file__)+"/../circt/llvm/build/bin")
config.moore_target_dir = re.search(r'"target_directory"\s*:\s*"(.*?)"', subprocess.check_output(["cargo", "metadata", "--format-version", "1"], universal_newlines=True)).group(1)

llvm_config.use_default_substitutions()
llvm_config.add_tool_substitutions(["moore"], [config.moore_target_dir+"/debug"])
