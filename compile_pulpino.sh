#!/bin/bash
# This script compiles the pulpino platform as a means to test the capabilities
# of the moore compiler.

MOORE="target/debug/moore compile"
MOORE_FLAGS=""
SRC=pulpino
RTL_SRC=${SRC}/rtl
RTL_FLAGS="-I ${RTL_SRC}/includes"
LIBFILE=".moore"
set -e

if [ -e "$LIBFILE" ]; then
	rm "$LIBFILE"
fi

echo "$(tput bold)compiling components...$(tput sgr0)"
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/cluster_clock_gating.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/cluster_clock_inverter.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/cluster_clock_mux2.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/pulp_clock_inverter.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/pulp_clock_mux2.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/generic_fifo.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/rstgen.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/sp_ram.sv

echo "$(tput bold)compiling rtl...$(tput sgr0)"
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/core_region.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/random_stalls.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/boot_rom_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/boot_code.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/instr_ram_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/sp_ram_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/ram_mux.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/axi_node_intf_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/top.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/peripherals.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/periph_bus_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/axi2apb_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/axi_spi_slave_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/axi_mem_if_SP_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/clk_rst_gen.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/axi_slice_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${RTL_SRC}/core2axi_wrap.sv

echo "$(tput bold)compiling ips...$(tput sgr0)"
if [ ! -e ${SRC}/compile_moore.sh ]; then
	pushd ${SRC}
	./generate_moore.py
	popd
fi
source ${SRC}/compile_moore.sh

echo "$(tput bold)elaborating...$(tput sgr0)"
target/debug/moore elaborate --ignore-duplicate-defs pulpino_top
