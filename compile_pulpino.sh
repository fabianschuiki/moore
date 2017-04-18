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

${MOORE} ${MOORE_FLAGS} pulpino_fixes.sv

## components
echo "$(tput bold)compiling components...$(tput sgr0)"
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/cluster_clock_gating.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/cluster_clock_inverter.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/cluster_clock_mux2.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/pulp_clock_inverter.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/pulp_clock_mux2.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/generic_fifo.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/rstgen.sv
${MOORE} ${MOORE_FLAGS} ${RTL_SRC}/components/sp_ram.sv

## rtl
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

## ips
echo "$(tput bold)compiling ips...$(tput sgr0)"

# apb_gpio
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_gpio/apb_gpio.sv

# axi_slice_dc
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice_dc/axi_slice_dc_master.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice_dc/axi_slice_dc_slave.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice_dc/dc_data_buffer.v
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice_dc/dc_full_detector.v
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice_dc/dc_synchronizer.v
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice_dc/dc_token_ring_fifo_din.v
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice_dc/dc_token_ring_fifo_dout.v
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice_dc/dc_token_ring.v

# apb_event_unit
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/apb/apb_event_unit/./include/ ${SRC}/ips/apb/apb_event_unit/apb_event_unit.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/apb/apb_event_unit/./include/ ${SRC}/ips/apb/apb_event_unit/generic_service_unit.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/apb/apb_event_unit/./include/ ${SRC}/ips/apb/apb_event_unit/sleep_unit.sv

# axi_node
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/apb_regs_top.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_address_decoder_AR.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_address_decoder_AW.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_address_decoder_BR.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_address_decoder_BW.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_address_decoder_DW.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_AR_allocator.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_ArbitrationTree.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_AW_allocator.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_BR_allocator.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_BW_allocator.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_DW_allocator.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_FanInPrimitive_Req.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_multiplexer.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_node.sv
# ${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_node_wrap.sv
# ${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_node_wrap_with_slices.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_regs_top.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_request_block.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_response_block.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/axi/axi_node/. ${SRC}/ips/axi/axi_node/axi_RR_Flag_Req.sv

# riscv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/include/riscv_defines.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/include/riscv_tracer_defines.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/alu.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/alu_div.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/compressed_decoder.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/controller.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/cs_registers.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/debug_unit.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/decoder.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/exc_controller.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/ex_stage.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/hwloop_controller.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/hwloop_regs.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/id_stage.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/if_stage.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/load_store_unit.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/mult.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/prefetch_buffer.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/prefetch_L0_buffer.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/riscv_core.sv

${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/register_file.sv

${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/riscv_tracer.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/riscv/include ${SRC}/ips/riscv/riscv_simchecker.sv

# apb_pulpino
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_pulpino/apb_pulpino.sv

# axi_mem_if_DP
# ${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_mem_if_DP/axi_mem_if_MP_Hybrid_multi_bank.sv
# ${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_mem_if_DP/axi_mem_if_multi_bank.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_mem_if_DP/axi_mem_if_DP_hybr.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_mem_if_DP/axi_mem_if_DP.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_mem_if_DP/axi_mem_if_SP.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_mem_if_DP/axi_read_only_ctrl.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_mem_if_DP/axi_write_only_ctrl.sv

# apb_fll_if
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_fll_if/apb_fll_if.sv

# axi_slice
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice/axi_ar_buffer.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice/axi_aw_buffer.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice/axi_b_buffer.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice/axi_buffer.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice/axi_r_buffer.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice/axi_slice.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_slice/axi_w_buffer.sv

# apb_uart
# skipped ${SRC}/ips/apb/apb_uart/apb_uart.vhd
# skipped ${SRC}/ips/apb/apb_uart/slib_clock_div.vhd
# skipped ${SRC}/ips/apb/apb_uart/slib_counter.vhd
# skipped ${SRC}/ips/apb/apb_uart/slib_edge_detect.vhd
# skipped ${SRC}/ips/apb/apb_uart/slib_fifo.vhd
# skipped ${SRC}/ips/apb/apb_uart/slib_input_filter.vhd
# skipped ${SRC}/ips/apb/apb_uart/slib_input_sync.vhd
# skipped ${SRC}/ips/apb/apb_uart/slib_mv_filter.vhd
# skipped ${SRC}/ips/apb/apb_uart/uart_baudgen.vhd
# skipped ${SRC}/ips/apb/apb_uart/uart_interrupt.vhd
# skipped ${SRC}/ips/apb/apb_uart/uart_receiver.vhd
# skipped ${SRC}/ips/apb/apb_uart/uart_transmitter.vhd

# apb_spi_master
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_spi_master/apb_spi_master.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_spi_master/spi_master_apb_if.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_spi_master/spi_master_clkgen.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_spi_master/spi_master_controller.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_spi_master/spi_master_fifo.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_spi_master/spi_master_rx.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_spi_master/spi_master_tx.sv

# apb_timer
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_timer/apb_timer.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_timer/timer.sv

# axi2apb
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi2apb/AXI_2_APB.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi2apb/AXI_2_APB_32.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi2apb/axi2apb.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi2apb/axi2apb32.sv

# axi_spi_slave
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_slave/axi_spi_slave.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_slave/spi_slave_axi_plug.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_slave/spi_slave_cmd_parser.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_slave/spi_slave_controller.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_slave/spi_slave_dc_fifo.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_slave/spi_slave_regs.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_slave/spi_slave_rx.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_slave/spi_slave_syncro.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_slave/spi_slave_tx.sv

# apb_i2c
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/apb/apb_i2c/. ${SRC}/ips/apb/apb_i2c/apb_i2c.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/apb/apb_i2c/. ${SRC}/ips/apb/apb_i2c/i2c_master_bit_ctrl.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/apb/apb_i2c/. ${SRC}/ips/apb/apb_i2c/i2c_master_byte_ctrl.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/apb/apb_i2c/. ${SRC}/ips/apb/apb_i2c/i2c_master_defines.sv

# adv_dbg_if
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adbg_axi_biu.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adbg_axi_module.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adbg_crc32.v
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adbg_or1k_biu.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adbg_or1k_module.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adbg_or1k_status_reg.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adbg_top.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/bytefifo.v
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/syncflop.v
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/syncreg.v
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adbg_tap_top.v
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adv_dbg_if.sv
${MOORE} ${MOORE_FLAGS} -I ${SRC}/ips/adv_dbg_if/rtl ${SRC}/ips/adv_dbg_if/rtl/adbg_axionly_top.sv

# axi_spi_master
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_master/axi_spi_master.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_master/spi_master_axi_if.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_master/spi_master_clkgen.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_master/spi_master_controller.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_master/spi_master_fifo.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_master/spi_master_rx.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/axi_spi_master/spi_master_tx.sv

# core2axi
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/axi/core2axi/rtl/core2axi.sv

# apb_node
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_node/apb_node.sv
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb_node/apb_node_wrap.sv

# apb2per
${MOORE} ${MOORE_FLAGS} ${SRC}/ips/apb/apb2per/apb2per.sv

## elaborate
echo "$(tput bold)elaborating...$(tput sgr0)"
target/debug/moore elaborate --ignore-duplicate-defs pulpino_top
