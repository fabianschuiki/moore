#!/bin/bash
# This script compiles the pulpino platform as a means to test the capabilities
# of the moore compiler.

# MOORE="cargo run --"
MOORE="target/debug/moore"
MOORE_FLAGS="-E"
SRC=pulpino/rtl
RTL_FLAGS="-I ${SRC}/includes"
set -e

${MOORE} ${MOORE_FLAGS} ${SRC}/components/cluster_clock_gating.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/components/cluster_clock_inverter.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/components/cluster_clock_mux2.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/components/pulp_clock_inverter.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/components/pulp_clock_mux2.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/components/generic_fifo.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/components/rstgen.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/components/sp_ram.sv

${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/core_region.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/random_stalls.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/boot_rom_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/boot_code.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/instr_ram_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/sp_ram_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/ram_mux.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/axi_node_intf_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/top.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/peripherals.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/periph_bus_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/axi2apb_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/axi_spi_slave_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/axi_mem_if_SP_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/clk_rst_gen.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/axi_slice_wrap.sv
${MOORE} ${MOORE_FLAGS} ${RTL_FLAGS} ${SRC}/core2axi_wrap.sv
