#!/bin/bash
# This script compiles the pulpino platform as a means to test the capabilities
# of the moore compiler.

MOORE="cargo run --"
SRC=pulpino/rtl
set -e

${MOORE} ${SRC}/components/cluster_clock_gating.sv
${MOORE} ${SRC}/components/cluster_clock_inverter.sv
${MOORE} ${SRC}/components/cluster_clock_mux2.sv
${MOORE} ${SRC}/components/pulp_clock_inverter.sv
${MOORE} ${SRC}/components/pulp_clock_mux2.sv
${MOORE} ${SRC}/components/generic_fifo.sv
${MOORE} ${SRC}/components/rstgen.sv
${MOORE} ${SRC}/components/sp_ram.sv

${MOORE} ${SRC}/core_region.sv
${MOORE} ${SRC}/random_stalls.sv

${MOORE} ${SRC}/boot_rom_wrap.sv
${MOORE} ${SRC}/boot_code.sv
${MOORE} ${SRC}/instr_ram_wrap.sv
${MOORE} ${SRC}/sp_ram_wrap.sv
${MOORE} ${SRC}/ram_mux.sv
${MOORE} ${SRC}/axi_node_intf_wrap.sv
${MOORE} ${SRC}/top.sv
${MOORE} ${SRC}/peripherals.sv
${MOORE} ${SRC}/periph_bus_wrap.sv
${MOORE} ${SRC}/axi2apb_wrap.sv
${MOORE} ${SRC}/axi_spi_slave_wrap.sv
${MOORE} ${SRC}/axi_mem_if_SP_wrap.sv
${MOORE} ${SRC}/clk_rst_gen.sv
${MOORE} ${SRC}/axi_slice_wrap.sv
${MOORE} ${SRC}/core2axi_wrap.sv
