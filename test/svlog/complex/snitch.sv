// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Description: Top-Level of Snitch Integer Core RV32E

// Copyright 2018 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Common register defines for RTL designs
`ifndef COMMON_CELLS_REGISTERS_SVH_
`define COMMON_CELLS_REGISTERS_SVH_

// Abridged Summary of available FF macros:
// `FF:      asynchronous active-low reset (implicit clock and reset)
// `FFAR:    asynchronous active-high reset
// `FFARN:   asynchronous active-low reset
// `FFSR:    synchronous active-high reset
// `FFSRN:   synchronous active-low reset
// `FFNR:    without reset
// `FFL:     load-enable and asynchronous active-low reset (implicit clock and reset)
// `FFLAR:   load-enable and asynchronous active-high reset
// `FFLARN:  load-enable and asynchronous active-low reset
// `FFLARNC: load-enable and asynchronous active-low reset and synchronous active-high clear
// `FFLSR:   load-enable and synchronous active-high reset
// `FFLSRN:  load-enable and synchronous active-low reset
// `FFLNR:   load-enable without reset


// Flip-Flop with asynchronous active-low reset (implicit clock and reset)
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// Implicit:
// clk_i: clock input
// rst_ni: reset input (asynchronous, active low)
`define FF(__q, __d, __reset_value)                  \
  always_ff @(posedge clk_i or negedge rst_ni) begin \
    if (!rst_ni) begin                               \
      __q <= (__reset_value);                        \
    end else begin                                   \
      __q <= (__d);                                  \
    end                                              \
  end

// Flip-Flop with asynchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst: asynchronous reset
`define FFAR(__q, __d, __reset_value, __clk, __arst)     \
  always_ff @(posedge (__clk) or posedge (__arst)) begin \
    if (__arst) begin                                    \
      __q <= (__reset_value);                            \
    end else begin                                       \
      __q <= (__d);                                      \
    end                                                  \
  end

// Flip-Flop with asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset
`define FFARN(__q, __d, __reset_value, __clk, __arst_n)    \
  always_ff @(posedge (__clk) or negedge (__arst_n)) begin \
    if (!__arst_n) begin                                   \
      __q <= (__reset_value);                              \
    end else begin                                         \
      __q <= (__d);                                        \
    end                                                    \
  end

// Flip-Flop with synchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_clk: reset input
`define FFSR(__q, __d, __reset_value, __clk, __reset_clk) \
  `ifndef VERILATOR                       \
  /``* synopsys sync_set_reset `"__reset_clk`" *``/       \
    `endif                        \
  always_ff @(posedge (__clk)) begin                      \
    __q <= (__reset_clk) ? (__reset_value) : (__d);       \
  end

// Flip-Flop with synchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_n_clk: reset input
`define FFSRN(__q, __d, __reset_value, __clk, __reset_n_clk) \
    `ifndef VERILATOR                       \
  /``* synopsys sync_set_reset `"__reset_n_clk`" *``/        \
    `endif                        \
  always_ff @(posedge (__clk)) begin                         \
    __q <= (!__reset_n_clk) ? (__reset_value) : (__d);       \
  end

// Always-enable Flip-Flop without reset
// __q: Q output of FF
// __d: D input of FF
// __clk: clock input
`define FFNR(__q, __d, __clk)        \
  always_ff @(posedge (__clk)) begin \
    __q <= (__d);                    \
  end

// Flip-Flop with load-enable and asynchronous active-low reset (implicit clock and reset)
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// Implicit:
// clk_i: clock input
// rst_ni: reset input (asynchronous, active low)
`define FFL(__q, __d, __load, __reset_value)         \
  always_ff @(posedge clk_i or negedge rst_ni) begin \
    if (!rst_ni) begin                               \
      __q <= (__reset_value);                        \
    end else begin                                   \
      __q <= (__load) ? (__d) : (__q);               \
    end                                              \
  end

// Flip-Flop with load-enable and asynchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst: asynchronous reset
`define FFLAR(__q, __d, __load, __reset_value, __clk, __arst) \
  always_ff @(posedge (__clk) or posedge (__arst)) begin      \
    if (__arst) begin                                         \
      __q <= (__reset_value);                                 \
    end else begin                                            \
      __q <= (__load) ? (__d) : (__q);                        \
    end                                                       \
  end

// Flip-Flop with load-enable and asynchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset
`define FFLARN(__q, __d, __load, __reset_value, __clk, __arst_n) \
  always_ff @(posedge (__clk) or negedge (__arst_n)) begin       \
    if (!__arst_n) begin                                         \
      __q <= (__reset_value);                                    \
    end else begin                                               \
      __q <= (__load) ? (__d) : (__q);                           \
    end                                                          \
  end

// Flip-Flop with load-enable and synchronous active-high reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_clk: reset input
`define FFLSR(__q, __d, __load, __reset_value, __clk, __reset_clk)       \
    `ifndef VERILATOR                       \
  /``* synopsys sync_set_reset `"__reset_clk`" *``/                      \
    `endif                        \
  always_ff @(posedge (__clk)) begin                                     \
    __q <= (__reset_clk) ? (__reset_value) : ((__load) ? (__d) : (__q)); \
  end

// Flip-Flop with load-enable and synchronous active-low reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __reset_n_clk: reset input
`define FFLSRN(__q, __d, __load, __reset_value, __clk, __reset_n_clk)       \
    `ifndef VERILATOR                       \
  /``* synopsys sync_set_reset `"__reset_n_clk`" *``/                       \
    `endif                        \
  always_ff @(posedge (__clk)) begin                                        \
    __q <= (!__reset_n_clk) ? (__reset_value) : ((__load) ? (__d) : (__q)); \
  end

// Flip-Flop with load-enable and asynchronous active-low reset and synchronous clear
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __clear: assign reset value into FF
// __reset_value: value assigned upon reset
// __clk: clock input
// __arst_n: asynchronous reset
`define FFLARNC(__q, __d, __load, __clear, __reset_value, __clk, __arst_n) \
    `ifndef VERILATOR                       \
  /``* synopsys sync_set_reset `"__clear`" *``/                       \
    `endif                        \
  always_ff @(posedge (__clk) or negedge (__arst_n)) begin                 \
    if (!__arst_n) begin                                                   \
      __q <= (__reset_value);                                              \
    end else begin                                                         \
      __q <= (__clear) ? (__reset_value) : (__load) ? (__d) : (__q);       \
    end                                                                    \
  end

// Load-enable Flip-Flop without reset
// __q: Q output of FF
// __d: D input of FF
// __load: load d value into FF
// __clk: clock input
`define FFLNR(__q, __d, __load, __clk) \
  always_ff @(posedge (__clk)) begin   \
    __q <= (__load) ? (__d) : (__q);   \
  end

`endif

/* Automatically generated by parse-opcodes */
package riscv_instr;
  localparam [31:0] BEQ                = 32'b?????????????????000?????1100011;
  localparam [31:0] BNE                = 32'b?????????????????001?????1100011;
  localparam [31:0] BLT                = 32'b?????????????????100?????1100011;
  localparam [31:0] BGE                = 32'b?????????????????101?????1100011;
  localparam [31:0] BLTU               = 32'b?????????????????110?????1100011;
  localparam [31:0] BGEU               = 32'b?????????????????111?????1100011;
  localparam [31:0] JALR               = 32'b?????????????????000?????1100111;
  localparam [31:0] JAL                = 32'b?????????????????????????1101111;
  localparam [31:0] LUI                = 32'b?????????????????????????0110111;
  localparam [31:0] AUIPC              = 32'b?????????????????????????0010111;
  localparam [31:0] ADDI               = 32'b?????????????????000?????0010011;
  localparam [31:0] SLLI               = 32'b000000???????????001?????0010011;
  localparam [31:0] SLTI               = 32'b?????????????????010?????0010011;
  localparam [31:0] SLTIU              = 32'b?????????????????011?????0010011;
  localparam [31:0] XORI               = 32'b?????????????????100?????0010011;
  localparam [31:0] SRLI               = 32'b000000???????????101?????0010011;
  localparam [31:0] SRAI               = 32'b010000???????????101?????0010011;
  localparam [31:0] ORI                = 32'b?????????????????110?????0010011;
  localparam [31:0] ANDI               = 32'b?????????????????111?????0010011;
  localparam [31:0] ADD                = 32'b0000000??????????000?????0110011;
  localparam [31:0] SUB                = 32'b0100000??????????000?????0110011;
  localparam [31:0] SLL                = 32'b0000000??????????001?????0110011;
  localparam [31:0] SLT                = 32'b0000000??????????010?????0110011;
  localparam [31:0] SLTU               = 32'b0000000??????????011?????0110011;
  localparam [31:0] XOR                = 32'b0000000??????????100?????0110011;
  localparam [31:0] SRL                = 32'b0000000??????????101?????0110011;
  localparam [31:0] SRA                = 32'b0100000??????????101?????0110011;
  localparam [31:0] OR                 = 32'b0000000??????????110?????0110011;
  localparam [31:0] AND                = 32'b0000000??????????111?????0110011;
  localparam [31:0] ADDIW              = 32'b?????????????????000?????0011011;
  localparam [31:0] SLLIW              = 32'b0000000??????????001?????0011011;
  localparam [31:0] SRLIW              = 32'b0000000??????????101?????0011011;
  localparam [31:0] SRAIW              = 32'b0100000??????????101?????0011011;
  localparam [31:0] ADDW               = 32'b0000000??????????000?????0111011;
  localparam [31:0] SUBW               = 32'b0100000??????????000?????0111011;
  localparam [31:0] SLLW               = 32'b0000000??????????001?????0111011;
  localparam [31:0] SRLW               = 32'b0000000??????????101?????0111011;
  localparam [31:0] SRAW               = 32'b0100000??????????101?????0111011;
  localparam [31:0] LB                 = 32'b?????????????????000?????0000011;
  localparam [31:0] LH                 = 32'b?????????????????001?????0000011;
  localparam [31:0] LW                 = 32'b?????????????????010?????0000011;
  localparam [31:0] LD                 = 32'b?????????????????011?????0000011;
  localparam [31:0] LBU                = 32'b?????????????????100?????0000011;
  localparam [31:0] LHU                = 32'b?????????????????101?????0000011;
  localparam [31:0] LWU                = 32'b?????????????????110?????0000011;
  localparam [31:0] SB                 = 32'b?????????????????000?????0100011;
  localparam [31:0] SH                 = 32'b?????????????????001?????0100011;
  localparam [31:0] SW                 = 32'b?????????????????010?????0100011;
  localparam [31:0] SD                 = 32'b?????????????????011?????0100011;
  localparam [31:0] FENCE              = 32'b?????????????????000?????0001111;
  localparam [31:0] FENCE_I            = 32'b?????????????????001?????0001111;
  localparam [31:0] MUL                = 32'b0000001??????????000?????0110011;
  localparam [31:0] MULH               = 32'b0000001??????????001?????0110011;
  localparam [31:0] MULHSU             = 32'b0000001??????????010?????0110011;
  localparam [31:0] MULHU              = 32'b0000001??????????011?????0110011;
  localparam [31:0] DIV                = 32'b0000001??????????100?????0110011;
  localparam [31:0] DIVU               = 32'b0000001??????????101?????0110011;
  localparam [31:0] REM                = 32'b0000001??????????110?????0110011;
  localparam [31:0] REMU               = 32'b0000001??????????111?????0110011;
  localparam [31:0] MULW               = 32'b0000001??????????000?????0111011;
  localparam [31:0] DIVW               = 32'b0000001??????????100?????0111011;
  localparam [31:0] DIVUW              = 32'b0000001??????????101?????0111011;
  localparam [31:0] REMW               = 32'b0000001??????????110?????0111011;
  localparam [31:0] REMUW              = 32'b0000001??????????111?????0111011;
  localparam [31:0] ANDN               = 32'b0100000??????????111?????0110011;
  localparam [31:0] ORN                = 32'b0100000??????????110?????0110011;
  localparam [31:0] XNOR               = 32'b0100000??????????100?????0110011;
  localparam [31:0] GREV               = 32'b0100000??????????001?????0110011;
  localparam [31:0] SLO                = 32'b0010000??????????001?????0110011;
  localparam [31:0] SRO                = 32'b0010000??????????101?????0110011;
  localparam [31:0] ROL                = 32'b0110000??????????001?????0110011;
  localparam [31:0] ROR                = 32'b0110000??????????101?????0110011;
  localparam [31:0] SBSET              = 32'b0010100??????????001?????0110011;
  localparam [31:0] SBCLR              = 32'b0100100??????????001?????0110011;
  localparam [31:0] SBINV              = 32'b0110100??????????001?????0110011;
  localparam [31:0] SBEXT              = 32'b0100100??????????101?????0110011;
  localparam [31:0] GREVI              = 32'b010000???????????001?????0010011;
  localparam [31:0] SLOI               = 32'b001000???????????001?????0010011;
  localparam [31:0] SROI               = 32'b001000???????????101?????0010011;
  localparam [31:0] RORI               = 32'b011000???????????101?????0010011;
  localparam [31:0] SBSETI             = 32'b001010???????????001?????0010011;
  localparam [31:0] SBCLRI             = 32'b010010???????????001?????0010011;
  localparam [31:0] SBINVI             = 32'b011010???????????001?????0010011;
  localparam [31:0] SBEXTI             = 32'b010010???????????101?????0010011;
  localparam [31:0] CMIX               = 32'b?????11??????????001?????0110011;
  localparam [31:0] CMOV               = 32'b?????11??????????101?????0110011;
  localparam [31:0] FSL                = 32'b?????10??????????001?????0110011;
  localparam [31:0] FSR                = 32'b?????10??????????101?????0110011;
  localparam [31:0] FSRI               = 32'b?????1???????????101?????0010011;
  localparam [31:0] CLZ                = 32'b011000000000?????001?????0010011;
  localparam [31:0] CTZ                = 32'b011000000001?????001?????0010011;
  localparam [31:0] PCNT               = 32'b011000000010?????001?????0010011;
  localparam [31:0] CRC32_B            = 32'b011000010000?????001?????0010011;
  localparam [31:0] CRC32_H            = 32'b011000010001?????001?????0010011;
  localparam [31:0] CRC32_W            = 32'b011000010010?????001?????0010011;
  localparam [31:0] CRC32C_B           = 32'b011000011000?????001?????0010011;
  localparam [31:0] CRC32C_H           = 32'b011000011001?????001?????0010011;
  localparam [31:0] CRC32C_W           = 32'b011000011010?????001?????0010011;
  localparam [31:0] CLMUL              = 32'b0000101??????????001?????0110011;
  localparam [31:0] CLMULR             = 32'b0000101??????????010?????0110011;
  localparam [31:0] CLMULH             = 32'b0000101??????????011?????0110011;
  localparam [31:0] MIN                = 32'b0000101??????????100?????0110011;
  localparam [31:0] MAX                = 32'b0000101??????????101?????0110011;
  localparam [31:0] MINU               = 32'b0000101??????????110?????0110011;
  localparam [31:0] MAXU               = 32'b0000101??????????111?????0110011;
  localparam [31:0] SHFL               = 32'b0000100??????????001?????0110011;
  localparam [31:0] UNSHFL             = 32'b0000100??????????101?????0110011;
  localparam [31:0] BDEP               = 32'b0000100??????????010?????0110011;
  localparam [31:0] BEXT               = 32'b0000100??????????110?????0110011;
  localparam [31:0] PACK               = 32'b0000100??????????100?????0110011;
  localparam [31:0] SHFLI              = 32'b000010???????????001?????0010011;
  localparam [31:0] UNSHFLI            = 32'b000010???????????101?????0010011;
  localparam [31:0] BMATFLIP           = 32'b011000000011?????001?????0010011;
  localparam [31:0] CRC32_D            = 32'b011000010011?????001?????0010011;
  localparam [31:0] CRC32C_D           = 32'b011000011011?????001?????0010011;
  localparam [31:0] BMATOR             = 32'b0000100??????????011?????0110011;
  localparam [31:0] BMATXOR            = 32'b0000100??????????111?????0110011;
  localparam [31:0] ADDIWU             = 32'b?????????????????100?????0011011;
  localparam [31:0] SLLIU_W            = 32'b000010???????????001?????0011011;
  localparam [31:0] ADDWU              = 32'b0000101??????????000?????0111011;
  localparam [31:0] SUBWU              = 32'b0100101??????????000?????0111011;
  localparam [31:0] ADDU_W             = 32'b0000100??????????000?????0111011;
  localparam [31:0] SUBU_W             = 32'b0100100??????????000?????0111011;
  localparam [31:0] GREVW              = 32'b0100000??????????001?????0111011;
  localparam [31:0] SLOW               = 32'b0010000??????????001?????0111011;
  localparam [31:0] SROW               = 32'b0010000??????????101?????0111011;
  localparam [31:0] ROLW               = 32'b0110000??????????001?????0111011;
  localparam [31:0] RORW               = 32'b0110000??????????101?????0111011;
  localparam [31:0] SBSETW             = 32'b0010100??????????001?????0111011;
  localparam [31:0] SBCLRW             = 32'b0100100??????????001?????0111011;
  localparam [31:0] SBINVW             = 32'b0110100??????????001?????0111011;
  localparam [31:0] SBEXTW             = 32'b0100100??????????101?????0111011;
  localparam [31:0] GREVIW             = 32'b0100000??????????001?????0011011;
  localparam [31:0] SLOIW              = 32'b0010000??????????001?????0011011;
  localparam [31:0] SROIW              = 32'b0010000??????????101?????0011011;
  localparam [31:0] RORIW              = 32'b0110000??????????101?????0011011;
  localparam [31:0] SBSETIW            = 32'b0010100??????????001?????0011011;
  localparam [31:0] SBCLRIW            = 32'b0100100??????????001?????0011011;
  localparam [31:0] SBINVIW            = 32'b0110100??????????001?????0011011;
  localparam [31:0] FSLW               = 32'b?????10??????????001?????0111011;
  localparam [31:0] FSRW               = 32'b?????10??????????101?????0111011;
  localparam [31:0] FSRIW              = 32'b?????10??????????101?????0011011;
  localparam [31:0] CLZW               = 32'b011000000000?????001?????0011011;
  localparam [31:0] CTZW               = 32'b011000000001?????001?????0011011;
  localparam [31:0] PCNTW              = 32'b011000000010?????001?????0011011;
  localparam [31:0] CLMULW             = 32'b0000101??????????001?????0111011;
  localparam [31:0] CLMULRW            = 32'b0000101??????????010?????0111011;
  localparam [31:0] CLMULHW            = 32'b0000101??????????011?????0111011;
  localparam [31:0] SHFLW              = 32'b0000100??????????001?????0111011;
  localparam [31:0] UNSHFLW            = 32'b0000100??????????101?????0111011;
  localparam [31:0] BDEPW              = 32'b0000100??????????010?????0111011;
  localparam [31:0] BEXTW              = 32'b0000100??????????110?????0111011;
  localparam [31:0] PACKW              = 32'b0000100??????????100?????0111011;
  localparam [31:0] AMOADD_W           = 32'b00000????????????010?????0101111;
  localparam [31:0] AMOXOR_W           = 32'b00100????????????010?????0101111;
  localparam [31:0] AMOOR_W            = 32'b01000????????????010?????0101111;
  localparam [31:0] AMOAND_W           = 32'b01100????????????010?????0101111;
  localparam [31:0] AMOMIN_W           = 32'b10000????????????010?????0101111;
  localparam [31:0] AMOMAX_W           = 32'b10100????????????010?????0101111;
  localparam [31:0] AMOMINU_W          = 32'b11000????????????010?????0101111;
  localparam [31:0] AMOMAXU_W          = 32'b11100????????????010?????0101111;
  localparam [31:0] AMOSWAP_W          = 32'b00001????????????010?????0101111;
  localparam [31:0] LR_W               = 32'b00010??00000?????010?????0101111;
  localparam [31:0] SC_W               = 32'b00011????????????010?????0101111;
  localparam [31:0] AMOADD_D           = 32'b00000????????????011?????0101111;
  localparam [31:0] AMOXOR_D           = 32'b00100????????????011?????0101111;
  localparam [31:0] AMOOR_D            = 32'b01000????????????011?????0101111;
  localparam [31:0] AMOAND_D           = 32'b01100????????????011?????0101111;
  localparam [31:0] AMOMIN_D           = 32'b10000????????????011?????0101111;
  localparam [31:0] AMOMAX_D           = 32'b10100????????????011?????0101111;
  localparam [31:0] AMOMINU_D          = 32'b11000????????????011?????0101111;
  localparam [31:0] AMOMAXU_D          = 32'b11100????????????011?????0101111;
  localparam [31:0] AMOSWAP_D          = 32'b00001????????????011?????0101111;
  localparam [31:0] LR_D               = 32'b00010??00000?????011?????0101111;
  localparam [31:0] SC_D               = 32'b00011????????????011?????0101111;
  localparam [31:0] ECALL              = 32'b00000000000000000000000001110011;
  localparam [31:0] EBREAK             = 32'b00000000000100000000000001110011;
  localparam [31:0] URET               = 32'b00000000001000000000000001110011;
  localparam [31:0] SRET               = 32'b00010000001000000000000001110011;
  localparam [31:0] MRET               = 32'b00110000001000000000000001110011;
  localparam [31:0] DRET               = 32'b01111011001000000000000001110011;
  localparam [31:0] SFENCE_VMA         = 32'b0001001??????????000000001110011;
  localparam [31:0] WFI                = 32'b00010000010100000000000001110011;
  localparam [31:0] CSRRW              = 32'b?????????????????001?????1110011;
  localparam [31:0] CSRRS              = 32'b?????????????????010?????1110011;
  localparam [31:0] CSRRC              = 32'b?????????????????011?????1110011;
  localparam [31:0] CSRRWI             = 32'b?????????????????101?????1110011;
  localparam [31:0] CSRRSI             = 32'b?????????????????110?????1110011;
  localparam [31:0] CSRRCI             = 32'b?????????????????111?????1110011;
  localparam [31:0] HFENCE_BVMA        = 32'b0010001??????????000000001110011;
  localparam [31:0] HFENCE_GVMA        = 32'b1010001??????????000000001110011;
  localparam [31:0] FADD_S             = 32'b0000000??????????????????1010011;
  localparam [31:0] FSUB_S             = 32'b0000100??????????????????1010011;
  localparam [31:0] FMUL_S             = 32'b0001000??????????????????1010011;
  localparam [31:0] FDIV_S             = 32'b0001100??????????????????1010011;
  localparam [31:0] FSGNJ_S            = 32'b0010000??????????000?????1010011;
  localparam [31:0] FSGNJN_S           = 32'b0010000??????????001?????1010011;
  localparam [31:0] FSGNJX_S           = 32'b0010000??????????010?????1010011;
  localparam [31:0] FMIN_S             = 32'b0010100??????????000?????1010011;
  localparam [31:0] FMAX_S             = 32'b0010100??????????001?????1010011;
  localparam [31:0] FSQRT_S            = 32'b010110000000?????????????1010011;
  localparam [31:0] FADD_D             = 32'b0000001??????????????????1010011;
  localparam [31:0] FSUB_D             = 32'b0000101??????????????????1010011;
  localparam [31:0] FMUL_D             = 32'b0001001??????????????????1010011;
  localparam [31:0] FDIV_D             = 32'b0001101??????????????????1010011;
  localparam [31:0] FSGNJ_D            = 32'b0010001??????????000?????1010011;
  localparam [31:0] FSGNJN_D           = 32'b0010001??????????001?????1010011;
  localparam [31:0] FSGNJX_D           = 32'b0010001??????????010?????1010011;
  localparam [31:0] FMIN_D             = 32'b0010101??????????000?????1010011;
  localparam [31:0] FMAX_D             = 32'b0010101??????????001?????1010011;
  localparam [31:0] FCVT_S_D           = 32'b010000000001?????????????1010011;
  localparam [31:0] FCVT_D_S           = 32'b010000100000?????????????1010011;
  localparam [31:0] FSQRT_D            = 32'b010110100000?????????????1010011;
  localparam [31:0] FADD_Q             = 32'b0000011??????????????????1010011;
  localparam [31:0] FSUB_Q             = 32'b0000111??????????????????1010011;
  localparam [31:0] FMUL_Q             = 32'b0001011??????????????????1010011;
  localparam [31:0] FDIV_Q             = 32'b0001111??????????????????1010011;
  localparam [31:0] FSGNJ_Q            = 32'b0010011??????????000?????1010011;
  localparam [31:0] FSGNJN_Q           = 32'b0010011??????????001?????1010011;
  localparam [31:0] FSGNJX_Q           = 32'b0010011??????????010?????1010011;
  localparam [31:0] FMIN_Q             = 32'b0010111??????????000?????1010011;
  localparam [31:0] FMAX_Q             = 32'b0010111??????????001?????1010011;
  localparam [31:0] FCVT_S_Q           = 32'b010000000011?????????????1010011;
  localparam [31:0] FCVT_Q_S           = 32'b010001100000?????????????1010011;
  localparam [31:0] FCVT_D_Q           = 32'b010000100011?????????????1010011;
  localparam [31:0] FCVT_Q_D           = 32'b010001100001?????????????1010011;
  localparam [31:0] FSQRT_Q            = 32'b010111100000?????????????1010011;
  localparam [31:0] FLE_S              = 32'b1010000??????????000?????1010011;
  localparam [31:0] FLT_S              = 32'b1010000??????????001?????1010011;
  localparam [31:0] FEQ_S              = 32'b1010000??????????010?????1010011;
  localparam [31:0] FLE_D              = 32'b1010001??????????000?????1010011;
  localparam [31:0] FLT_D              = 32'b1010001??????????001?????1010011;
  localparam [31:0] FEQ_D              = 32'b1010001??????????010?????1010011;
  localparam [31:0] FLE_Q              = 32'b1010011??????????000?????1010011;
  localparam [31:0] FLT_Q              = 32'b1010011??????????001?????1010011;
  localparam [31:0] FEQ_Q              = 32'b1010011??????????010?????1010011;
  localparam [31:0] FCVT_W_S           = 32'b110000000000?????????????1010011;
  localparam [31:0] FCVT_WU_S          = 32'b110000000001?????????????1010011;
  localparam [31:0] FCVT_L_S           = 32'b110000000010?????????????1010011;
  localparam [31:0] FCVT_LU_S          = 32'b110000000011?????????????1010011;
  localparam [31:0] FMV_X_W            = 32'b111000000000?????000?????1010011;
  localparam [31:0] FCLASS_S           = 32'b111000000000?????001?????1010011;
  localparam [31:0] FCVT_W_D           = 32'b110000100000?????????????1010011;
  localparam [31:0] FCVT_WU_D          = 32'b110000100001?????????????1010011;
  localparam [31:0] FCVT_L_D           = 32'b110000100010?????????????1010011;
  localparam [31:0] FCVT_LU_D          = 32'b110000100011?????????????1010011;
  localparam [31:0] FMV_X_D            = 32'b111000100000?????000?????1010011;
  localparam [31:0] FCLASS_D           = 32'b111000100000?????001?????1010011;
  localparam [31:0] FCVT_W_Q           = 32'b110001100000?????????????1010011;
  localparam [31:0] FCVT_WU_Q          = 32'b110001100001?????????????1010011;
  localparam [31:0] FCVT_L_Q           = 32'b110001100010?????????????1010011;
  localparam [31:0] FCVT_LU_Q          = 32'b110001100011?????????????1010011;
  localparam [31:0] FMV_X_Q            = 32'b111001100000?????000?????1010011;
  localparam [31:0] FCLASS_Q           = 32'b111001100000?????001?????1010011;
  localparam [31:0] FCVT_S_W           = 32'b110100000000?????????????1010011;
  localparam [31:0] FCVT_S_WU          = 32'b110100000001?????????????1010011;
  localparam [31:0] FCVT_S_L           = 32'b110100000010?????????????1010011;
  localparam [31:0] FCVT_S_LU          = 32'b110100000011?????????????1010011;
  localparam [31:0] FMV_W_X            = 32'b111100000000?????000?????1010011;
  localparam [31:0] FCVT_D_W           = 32'b110100100000?????????????1010011;
  localparam [31:0] FCVT_D_WU          = 32'b110100100001?????????????1010011;
  localparam [31:0] FCVT_D_L           = 32'b110100100010?????????????1010011;
  localparam [31:0] FCVT_D_LU          = 32'b110100100011?????????????1010011;
  localparam [31:0] FMV_D_X            = 32'b111100100000?????000?????1010011;
  localparam [31:0] FCVT_Q_W           = 32'b110101100000?????????????1010011;
  localparam [31:0] FCVT_Q_WU          = 32'b110101100001?????????????1010011;
  localparam [31:0] FCVT_Q_L           = 32'b110101100010?????????????1010011;
  localparam [31:0] FCVT_Q_LU          = 32'b110101100011?????????????1010011;
  localparam [31:0] FMV_Q_X            = 32'b111101100000?????000?????1010011;
  localparam [31:0] FLW                = 32'b?????????????????010?????0000111;
  localparam [31:0] FLD                = 32'b?????????????????011?????0000111;
  localparam [31:0] FLQ                = 32'b?????????????????100?????0000111;
  localparam [31:0] FSW                = 32'b?????????????????010?????0100111;
  localparam [31:0] FSD                = 32'b?????????????????011?????0100111;
  localparam [31:0] FSQ                = 32'b?????????????????100?????0100111;
  localparam [31:0] FMADD_S            = 32'b?????00??????????????????1000011;
  localparam [31:0] FMSUB_S            = 32'b?????00??????????????????1000111;
  localparam [31:0] FNMSUB_S           = 32'b?????00??????????????????1001011;
  localparam [31:0] FNMADD_S           = 32'b?????00??????????????????1001111;
  localparam [31:0] FMADD_D            = 32'b?????01??????????????????1000011;
  localparam [31:0] FMSUB_D            = 32'b?????01??????????????????1000111;
  localparam [31:0] FNMSUB_D           = 32'b?????01??????????????????1001011;
  localparam [31:0] FNMADD_D           = 32'b?????01??????????????????1001111;
  localparam [31:0] FMADD_Q            = 32'b?????11??????????????????1000011;
  localparam [31:0] FMSUB_Q            = 32'b?????11??????????????????1000111;
  localparam [31:0] FNMSUB_Q           = 32'b?????11??????????????????1001011;
  localparam [31:0] FNMADD_Q           = 32'b?????11??????????????????1001111;
  localparam [31:0] C_ADDI4SPN         = 32'b????????????????000???????????00;
  localparam [31:0] C_FLD              = 32'b????????????????001???????????00;
  localparam [31:0] C_LW               = 32'b????????????????010???????????00;
  localparam [31:0] C_FLW              = 32'b????????????????011???????????00;
  localparam [31:0] C_FSD              = 32'b????????????????101???????????00;
  localparam [31:0] C_SW               = 32'b????????????????110???????????00;
  localparam [31:0] C_FSW              = 32'b????????????????111???????????00;
  localparam [31:0] C_ADDI             = 32'b????????????????000???????????01;
  localparam [31:0] C_JAL              = 32'b????????????????001???????????01;
  localparam [31:0] C_LI               = 32'b????????????????010???????????01;
  localparam [31:0] C_LUI              = 32'b????????????????011???????????01;
  localparam [31:0] C_SRLI             = 32'b????????????????100?00????????01;
  localparam [31:0] C_SRAI             = 32'b????????????????100?01????????01;
  localparam [31:0] C_ANDI             = 32'b????????????????100?10????????01;
  localparam [31:0] C_SUB              = 32'b????????????????100011???00???01;
  localparam [31:0] C_XOR              = 32'b????????????????100011???01???01;
  localparam [31:0] C_OR               = 32'b????????????????100011???10???01;
  localparam [31:0] C_AND              = 32'b????????????????100011???11???01;
  localparam [31:0] C_SUBW             = 32'b????????????????100111???00???01;
  localparam [31:0] C_ADDW             = 32'b????????????????100111???01???01;
  localparam [31:0] C_J                = 32'b????????????????101???????????01;
  localparam [31:0] C_BEQZ             = 32'b????????????????110???????????01;
  localparam [31:0] C_BNEZ             = 32'b????????????????111???????????01;
  localparam [31:0] C_SLLI             = 32'b????????????????000???????????10;
  localparam [31:0] C_FLDSP            = 32'b????????????????001???????????10;
  localparam [31:0] C_LWSP             = 32'b????????????????010???????????10;
  localparam [31:0] C_FLWSP            = 32'b????????????????011???????????10;
  localparam [31:0] C_MV               = 32'b????????????????1000??????????10;
  localparam [31:0] C_ADD              = 32'b????????????????1001??????????10;
  localparam [31:0] C_FSDSP            = 32'b????????????????101???????????10;
  localparam [31:0] C_SWSP             = 32'b????????????????110???????????10;
  localparam [31:0] C_FSWSP            = 32'b????????????????111???????????10;
  localparam [31:0] C_NOP              = 32'b????????????????0000000000000001;
  localparam [31:0] C_ADDI16SP         = 32'b????????????????011?00010?????01;
  localparam [31:0] C_JR               = 32'b????????????????1000?????0000010;
  localparam [31:0] C_JALR             = 32'b????????????????1001?????0000010;
  localparam [31:0] C_EBREAK           = 32'b????????????????1001000000000010;
  localparam [31:0] C_LD               = 32'b????????????????011???????????00;
  localparam [31:0] C_SD               = 32'b????????????????111???????????00;
  localparam [31:0] C_ADDIW            = 32'b????????????????001???????????01;
  localparam [31:0] C_LDSP             = 32'b????????????????011???????????10;
  localparam [31:0] C_SDSP             = 32'b????????????????111???????????10;
  localparam [31:0] FREP               = 32'b?????????????????????????0001011;
  localparam [31:0] SLLI_RV32          = 32'b0000000??????????001?????0010011;
  localparam [31:0] SRLI_RV32          = 32'b0000000??????????101?????0010011;
  localparam [31:0] SRAI_RV32          = 32'b0100000??????????101?????0010011;
  localparam [31:0] FRFLAGS            = 32'b00000000000100000010?????1110011;
  localparam [31:0] FSFLAGS            = 32'b000000000001?????001?????1110011;
  localparam [31:0] FSFLAGSI           = 32'b000000000001?????101?????1110011;
  localparam [31:0] FRRM               = 32'b00000000001000000010?????1110011;
  localparam [31:0] FSRM               = 32'b000000000010?????001?????1110011;
  localparam [31:0] FSRMI              = 32'b000000000010?????101?????1110011;
  localparam [31:0] FSCSR              = 32'b000000000011?????001?????1110011;
  localparam [31:0] FRCSR              = 32'b00000000001100000010?????1110011;
  localparam [31:0] RDCYCLE            = 32'b11000000000000000010?????1110011;
  localparam [31:0] RDTIME             = 32'b11000000000100000010?????1110011;
  localparam [31:0] RDINSTRET          = 32'b11000000001000000010?????1110011;
  localparam [31:0] RDCYCLEH           = 32'b11001000000000000010?????1110011;
  localparam [31:0] RDTIMEH            = 32'b11001000000100000010?????1110011;
  localparam [31:0] RDINSTRETH         = 32'b11001000001000000010?????1110011;
  localparam [31:0] SCALL              = 32'b00000000000000000000000001110011;
  localparam [31:0] SBREAK             = 32'b00000000000100000000000001110011;
  localparam [31:0] FMV_X_S            = 32'b111000000000?????000?????1010011;
  localparam [31:0] FMV_S_X            = 32'b111100000000?????000?????1010011;
  localparam [31:0] FENCE_TSO          = 32'b100000110011?????000?????0001111;
  localparam [31:0] FLH                = 32'b?????????????????001?????0000111;
  localparam [31:0] FSH                = 32'b?????????????????001?????0100111;
  localparam [31:0] FMADD_H            = 32'b?????10??????????????????1000011;
  localparam [31:0] FMSUB_H            = 32'b?????10??????????????????1000111;
  localparam [31:0] FNMSUB_H           = 32'b?????10??????????????????1001011;
  localparam [31:0] FNMADD_H           = 32'b?????10??????????????????1001111;
  localparam [31:0] FADD_H             = 32'b0000010??????????????????1010011;
  localparam [31:0] FSUB_H             = 32'b0000110??????????????????1010011;
  localparam [31:0] FMUL_H             = 32'b0001010??????????????????1010011;
  localparam [31:0] FDIV_H             = 32'b0001110??????????????????1010011;
  localparam [31:0] FSQRT_H            = 32'b010111000000?????????????1010011;
  localparam [31:0] FSGNJ_H            = 32'b0010010??????????000?????1010011;
  localparam [31:0] FSGNJN_H           = 32'b0010010??????????001?????1010011;
  localparam [31:0] FSGNJX_H           = 32'b0010010??????????010?????1010011;
  localparam [31:0] FMIN_H             = 32'b0010110??????????000?????1010011;
  localparam [31:0] FMAX_H             = 32'b0010110??????????001?????1010011;
  localparam [31:0] FEQ_H              = 32'b1010010??????????010?????1010011;
  localparam [31:0] FLT_H              = 32'b1010010??????????001?????1010011;
  localparam [31:0] FLE_H              = 32'b1010010??????????000?????1010011;
  localparam [31:0] FCVT_W_H           = 32'b110001000000?????????????1010011;
  localparam [31:0] FCVT_WU_H          = 32'b110001000001?????????????1010011;
  localparam [31:0] FCVT_H_W           = 32'b110101000000?????????????1010011;
  localparam [31:0] FCVT_H_WU          = 32'b110101000001?????????????1010011;
  localparam [31:0] FMV_X_H            = 32'b111001000000?????000?????1010011;
  localparam [31:0] FCLASS_H           = 32'b111001000000?????001?????1010011;
  localparam [31:0] FMV_H_X            = 32'b111101000000?????000?????1010011;
  localparam [31:0] FCVT_L_H           = 32'b110001000010?????????????1010011;
  localparam [31:0] FCVT_LU_H          = 32'b110001000011?????????????1010011;
  localparam [31:0] FCVT_H_L           = 32'b110101000010?????????????1010011;
  localparam [31:0] FCVT_H_LU          = 32'b110101000011?????????????1010011;
  localparam [31:0] FCVT_S_H           = 32'b010000000010?????000?????1010011;
  localparam [31:0] FCVT_H_S           = 32'b010001000000?????????????1010011;
  localparam [31:0] FCVT_D_H           = 32'b010000100010?????000?????1010011;
  localparam [31:0] FCVT_H_D           = 32'b010001000001?????????????1010011;
  localparam [31:0] FLAH               = 32'b?????????????????001?????0000111;
  localparam [31:0] FSAH               = 32'b?????????????????001?????0100111;
  localparam [31:0] FMADD_AH           = 32'b?????10??????????101?????1000011;
  localparam [31:0] FMSUB_AH           = 32'b?????10??????????101?????1000111;
  localparam [31:0] FNMSUB_AH          = 32'b?????10??????????101?????1001011;
  localparam [31:0] FNMADD_AH          = 32'b?????10??????????101?????1001111;
  localparam [31:0] FADD_AH            = 32'b0000010??????????101?????1010011;
  localparam [31:0] FSUB_AH            = 32'b0000110??????????101?????1010011;
  localparam [31:0] FMUL_AH            = 32'b0001010??????????101?????1010011;
  localparam [31:0] FDIV_AH            = 32'b0001110??????????101?????1010011;
  localparam [31:0] FSQRT_AH           = 32'b010111000000?????101?????1010011;
  localparam [31:0] FSGNJ_AH           = 32'b0010010??????????100?????1010011;
  localparam [31:0] FSGNJN_AH          = 32'b0010010??????????101?????1010011;
  localparam [31:0] FSGNJX_AH          = 32'b0010010??????????110?????1010011;
  localparam [31:0] FMIN_AH            = 32'b0010110??????????100?????1010011;
  localparam [31:0] FMAX_AH            = 32'b0010110??????????101?????1010011;
  localparam [31:0] FEQ_AH             = 32'b1010010??????????110?????1010011;
  localparam [31:0] FLT_AH             = 32'b1010010??????????101?????1010011;
  localparam [31:0] FLE_AH             = 32'b1010010??????????100?????1010011;
  localparam [31:0] FCVT_W_AH          = 32'b110001000000?????101?????1010011;
  localparam [31:0] FCVT_WU_AH         = 32'b110001000001?????101?????1010011;
  localparam [31:0] FCVT_AH_W          = 32'b110101000000?????101?????1010011;
  localparam [31:0] FCVT_AH_WU         = 32'b110101000001?????101?????1010011;
  localparam [31:0] FMV_X_AH           = 32'b111001000000?????100?????1010011;
  localparam [31:0] FCLASS_AH          = 32'b111001000000?????101?????1010011;
  localparam [31:0] FMV_AH_X           = 32'b111101000000?????100?????1010011;
  localparam [31:0] FCVT_L_AH          = 32'b110001000010?????101?????1010011;
  localparam [31:0] FCVT_LU_AH         = 32'b110001000011?????101?????1010011;
  localparam [31:0] FCVT_AH_L          = 32'b110101000010?????101?????1010011;
  localparam [31:0] FCVT_AH_LU         = 32'b110101000011?????101?????1010011;
  localparam [31:0] FCVT_S_AH          = 32'b010000000110?????000?????1010011;
  localparam [31:0] FCVT_AH_S          = 32'b010001000000?????101?????1010011;
  localparam [31:0] FCVT_D_AH          = 32'b010000100110?????000?????1010011;
  localparam [31:0] FCVT_AH_D          = 32'b010001000001?????101?????1010011;
  localparam [31:0] FCVT_H_AH          = 32'b010001000110?????????????1010011;
  localparam [31:0] FCVT_AH_H          = 32'b010001000010?????101?????1010011;
  localparam [31:0] FLB                = 32'b?????????????????000?????0000111;
  localparam [31:0] FSB                = 32'b?????????????????000?????0100111;
  localparam [31:0] FMADD_B            = 32'b?????11??????????????????1000011;
  localparam [31:0] FMSUB_B            = 32'b?????11??????????????????1000111;
  localparam [31:0] FNMSUB_B           = 32'b?????11??????????????????1001011;
  localparam [31:0] FNMADD_B           = 32'b?????11??????????????????1001111;
  localparam [31:0] FADD_B             = 32'b0000011??????????????????1010011;
  localparam [31:0] FSUB_B             = 32'b0000111??????????????????1010011;
  localparam [31:0] FMUL_B             = 32'b0001011??????????????????1010011;
  localparam [31:0] FDIV_B             = 32'b0001111??????????????????1010011;
  localparam [31:0] FSQRT_B            = 32'b010111100000?????????????1010011;
  localparam [31:0] FSGNJ_B            = 32'b0010011??????????000?????1010011;
  localparam [31:0] FSGNJN_B           = 32'b0010011??????????001?????1010011;
  localparam [31:0] FSGNJX_B           = 32'b0010011??????????010?????1010011;
  localparam [31:0] FMIN_B             = 32'b0010111??????????000?????1010011;
  localparam [31:0] FMAX_B             = 32'b0010111??????????001?????1010011;
  localparam [31:0] FEQ_B              = 32'b1010011??????????010?????1010011;
  localparam [31:0] FLT_B              = 32'b1010011??????????001?????1010011;
  localparam [31:0] FLE_B              = 32'b1010011??????????000?????1010011;
  localparam [31:0] FCVT_W_B           = 32'b110001100000?????????????1010011;
  localparam [31:0] FCVT_WU_B          = 32'b110001100001?????????????1010011;
  localparam [31:0] FCVT_B_W           = 32'b110101100000?????????????1010011;
  localparam [31:0] FCVT_B_WU          = 32'b110101100001?????????????1010011;
  localparam [31:0] FMV_X_B            = 32'b111001100000?????000?????1010011;
  localparam [31:0] FCLASS_B           = 32'b111001100000?????001?????1010011;
  localparam [31:0] FMV_B_X            = 32'b111101100000?????000?????1010011;
  localparam [31:0] FCVT_L_B           = 32'b110001100010?????????????1010011;
  localparam [31:0] FCVT_LU_B          = 32'b110001100011?????????????1010011;
  localparam [31:0] FCVT_B_L           = 32'b110101100010?????????????1010011;
  localparam [31:0] FCVT_B_LU          = 32'b110101100011?????????????1010011;
  localparam [31:0] FCVT_S_B           = 32'b010000000011?????000?????1010011;
  localparam [31:0] FCVT_B_S           = 32'b010001100000?????????????1010011;
  localparam [31:0] FCVT_D_B           = 32'b010000100011?????000?????1010011;
  localparam [31:0] FCVT_B_D           = 32'b010001100001?????????????1010011;
  localparam [31:0] FCVT_H_B           = 32'b010001000011?????000?????1010011;
  localparam [31:0] FCVT_B_H           = 32'b010001100010?????????????1010011;
  localparam [31:0] FCVT_AH_B          = 32'b010001000011?????101?????1010011;
  localparam [31:0] FCVT_B_AH          = 32'b010001100110?????????????1010011;
  localparam [31:0] VFADD_S            = 32'b1000001??????????000?????0110011;
  localparam [31:0] VFADD_R_S          = 32'b1000001??????????100?????0110011;
  localparam [31:0] VFSUB_S            = 32'b1000010??????????000?????0110011;
  localparam [31:0] VFSUB_R_S          = 32'b1000010??????????100?????0110011;
  localparam [31:0] VFMUL_S            = 32'b1000011??????????000?????0110011;
  localparam [31:0] VFMUL_R_S          = 32'b1000011??????????100?????0110011;
  localparam [31:0] VFDIV_S            = 32'b1000100??????????000?????0110011;
  localparam [31:0] VFDIV_R_S          = 32'b1000100??????????100?????0110011;
  localparam [31:0] VFMIN_S            = 32'b1000101??????????000?????0110011;
  localparam [31:0] VFMIN_R_S          = 32'b1000101??????????100?????0110011;
  localparam [31:0] VFMAX_S            = 32'b1000110??????????000?????0110011;
  localparam [31:0] VFMAX_R_S          = 32'b1000110??????????100?????0110011;
  localparam [31:0] VFSQRT_S           = 32'b100011100000?????000?????0110011;
  localparam [31:0] VFMAC_S            = 32'b1001000??????????000?????0110011;
  localparam [31:0] VFMAC_R_S          = 32'b1001000??????????100?????0110011;
  localparam [31:0] VFMRE_S            = 32'b1001001??????????000?????0110011;
  localparam [31:0] VFMRE_R_S          = 32'b1001001??????????100?????0110011;
  localparam [31:0] VFCLASS_S          = 32'b100110000001?????000?????0110011;
  localparam [31:0] VFSGNJ_S           = 32'b1001101??????????000?????0110011;
  localparam [31:0] VFSGNJ_R_S         = 32'b1001101??????????100?????0110011;
  localparam [31:0] VFSGNJN_S          = 32'b1001110??????????000?????0110011;
  localparam [31:0] VFSGNJN_R_S        = 32'b1001110??????????100?????0110011;
  localparam [31:0] VFSGNJX_S          = 32'b1001111??????????000?????0110011;
  localparam [31:0] VFSGNJX_R_S        = 32'b1001111??????????100?????0110011;
  localparam [31:0] VFEQ_S             = 32'b1010000??????????000?????0110011;
  localparam [31:0] VFEQ_R_S           = 32'b1010000??????????100?????0110011;
  localparam [31:0] VFNE_S             = 32'b1010001??????????000?????0110011;
  localparam [31:0] VFNE_R_S           = 32'b1010001??????????100?????0110011;
  localparam [31:0] VFLT_S             = 32'b1010010??????????000?????0110011;
  localparam [31:0] VFLT_R_S           = 32'b1010010??????????100?????0110011;
  localparam [31:0] VFGE_S             = 32'b1010011??????????000?????0110011;
  localparam [31:0] VFGE_R_S           = 32'b1010011??????????100?????0110011;
  localparam [31:0] VFLE_S             = 32'b1010100??????????000?????0110011;
  localparam [31:0] VFLE_R_S           = 32'b1010100??????????100?????0110011;
  localparam [31:0] VFGT_S             = 32'b1010101??????????000?????0110011;
  localparam [31:0] VFGT_R_S           = 32'b1010101??????????100?????0110011;
  localparam [31:0] VFMV_X_S           = 32'b100110000000?????000?????0110011;
  localparam [31:0] VFMV_S_X           = 32'b100110000000?????100?????0110011;
  localparam [31:0] VFCVT_X_S          = 32'b100110000010?????000?????0110011;
  localparam [31:0] VFCVT_XU_S         = 32'b100110000010?????100?????0110011;
  localparam [31:0] VFCVT_S_X          = 32'b100110000011?????000?????0110011;
  localparam [31:0] VFCVT_S_XU         = 32'b100110000011?????100?????0110011;
  localparam [31:0] VFCPKA_S_S         = 32'b1011000??????????000?????0110011;
  localparam [31:0] VFCPKB_S_S         = 32'b1011000??????????100?????0110011;
  localparam [31:0] VFCPKC_S_S         = 32'b1011001??????????000?????0110011;
  localparam [31:0] VFCPKD_S_S         = 32'b1011001??????????100?????0110011;
  localparam [31:0] VFCPKA_S_D         = 32'b1011010??????????000?????0110011;
  localparam [31:0] VFCPKB_S_D         = 32'b1011010??????????100?????0110011;
  localparam [31:0] VFCPKC_S_D         = 32'b1011011??????????000?????0110011;
  localparam [31:0] VFCPKD_S_D         = 32'b1011011??????????100?????0110011;
  localparam [31:0] VFADD_H            = 32'b1000001??????????010?????0110011;
  localparam [31:0] VFADD_R_H          = 32'b1000001??????????110?????0110011;
  localparam [31:0] VFSUB_H            = 32'b1000010??????????010?????0110011;
  localparam [31:0] VFSUB_R_H          = 32'b1000010??????????110?????0110011;
  localparam [31:0] VFMUL_H            = 32'b1000011??????????010?????0110011;
  localparam [31:0] VFMUL_R_H          = 32'b1000011??????????110?????0110011;
  localparam [31:0] VFDIV_H            = 32'b1000100??????????010?????0110011;
  localparam [31:0] VFDIV_R_H          = 32'b1000100??????????110?????0110011;
  localparam [31:0] VFMIN_H            = 32'b1000101??????????010?????0110011;
  localparam [31:0] VFMIN_R_H          = 32'b1000101??????????110?????0110011;
  localparam [31:0] VFMAX_H            = 32'b1000110??????????010?????0110011;
  localparam [31:0] VFMAX_R_H          = 32'b1000110??????????110?????0110011;
  localparam [31:0] VFSQRT_H           = 32'b100011100000?????010?????0110011;
  localparam [31:0] VFMAC_H            = 32'b1001000??????????010?????0110011;
  localparam [31:0] VFMAC_R_H          = 32'b1001000??????????110?????0110011;
  localparam [31:0] VFMRE_H            = 32'b1001001??????????010?????0110011;
  localparam [31:0] VFMRE_R_H          = 32'b1001001??????????110?????0110011;
  localparam [31:0] VFCLASS_H          = 32'b100110000001?????010?????0110011;
  localparam [31:0] VFSGNJ_H           = 32'b1001101??????????010?????0110011;
  localparam [31:0] VFSGNJ_R_H         = 32'b1001101??????????110?????0110011;
  localparam [31:0] VFSGNJN_H          = 32'b1001110??????????010?????0110011;
  localparam [31:0] VFSGNJN_R_H        = 32'b1001110??????????110?????0110011;
  localparam [31:0] VFSGNJX_H          = 32'b1001111??????????010?????0110011;
  localparam [31:0] VFSGNJX_R_H        = 32'b1001111??????????110?????0110011;
  localparam [31:0] VFEQ_H             = 32'b1010000??????????010?????0110011;
  localparam [31:0] VFEQ_R_H           = 32'b1010000??????????110?????0110011;
  localparam [31:0] VFNE_H             = 32'b1010001??????????010?????0110011;
  localparam [31:0] VFNE_R_H           = 32'b1010001??????????110?????0110011;
  localparam [31:0] VFLT_H             = 32'b1010010??????????010?????0110011;
  localparam [31:0] VFLT_R_H           = 32'b1010010??????????110?????0110011;
  localparam [31:0] VFGE_H             = 32'b1010011??????????010?????0110011;
  localparam [31:0] VFGE_R_H           = 32'b1010011??????????110?????0110011;
  localparam [31:0] VFLE_H             = 32'b1010100??????????010?????0110011;
  localparam [31:0] VFLE_R_H           = 32'b1010100??????????110?????0110011;
  localparam [31:0] VFGT_H             = 32'b1010101??????????010?????0110011;
  localparam [31:0] VFGT_R_H           = 32'b1010101??????????110?????0110011;
  localparam [31:0] VFMV_X_H           = 32'b100110000000?????010?????0110011;
  localparam [31:0] VFMV_H_X           = 32'b100110000000?????110?????0110011;
  localparam [31:0] VFCVT_X_H          = 32'b100110000010?????010?????0110011;
  localparam [31:0] VFCVT_XU_H         = 32'b100110000010?????110?????0110011;
  localparam [31:0] VFCVT_H_X          = 32'b100110000011?????010?????0110011;
  localparam [31:0] VFCVT_H_XU         = 32'b100110000011?????110?????0110011;
  localparam [31:0] VFCPKA_H_S         = 32'b1011000??????????010?????0110011;
  localparam [31:0] VFCPKB_H_S         = 32'b1011000??????????110?????0110011;
  localparam [31:0] VFCPKC_H_S         = 32'b1011001??????????010?????0110011;
  localparam [31:0] VFCPKD_H_S         = 32'b1011001??????????110?????0110011;
  localparam [31:0] VFCPKA_H_D         = 32'b1011010??????????010?????0110011;
  localparam [31:0] VFCPKB_H_D         = 32'b1011010??????????110?????0110011;
  localparam [31:0] VFCPKC_H_D         = 32'b1011011??????????010?????0110011;
  localparam [31:0] VFCPKD_H_D         = 32'b1011011??????????110?????0110011;
  localparam [31:0] VFCVT_S_H          = 32'b100110000110?????000?????0110011;
  localparam [31:0] VFCVTU_S_H         = 32'b100110000110?????100?????0110011;
  localparam [31:0] VFCVT_H_S          = 32'b100110000100?????010?????0110011;
  localparam [31:0] VFCVTU_H_S         = 32'b100110000100?????110?????0110011;
  localparam [31:0] VFADD_AH           = 32'b1000001??????????001?????0110011;
  localparam [31:0] VFADD_R_AH         = 32'b1000001??????????101?????0110011;
  localparam [31:0] VFSUB_AH           = 32'b1000010??????????001?????0110011;
  localparam [31:0] VFSUB_R_AH         = 32'b1000010??????????101?????0110011;
  localparam [31:0] VFMUL_AH           = 32'b1000011??????????001?????0110011;
  localparam [31:0] VFMUL_R_AH         = 32'b1000011??????????101?????0110011;
  localparam [31:0] VFDIV_AH           = 32'b1000100??????????001?????0110011;
  localparam [31:0] VFDIV_R_AH         = 32'b1000100??????????101?????0110011;
  localparam [31:0] VFMIN_AH           = 32'b1000101??????????001?????0110011;
  localparam [31:0] VFMIN_R_AH         = 32'b1000101??????????101?????0110011;
  localparam [31:0] VFMAX_AH           = 32'b1000110??????????001?????0110011;
  localparam [31:0] VFMAX_R_AH         = 32'b1000110??????????101?????0110011;
  localparam [31:0] VFSQRT_AH          = 32'b100011100000?????001?????0110011;
  localparam [31:0] VFMAC_AH           = 32'b1001000??????????001?????0110011;
  localparam [31:0] VFMAC_R_AH         = 32'b1001000??????????101?????0110011;
  localparam [31:0] VFMRE_AH           = 32'b1001001??????????001?????0110011;
  localparam [31:0] VFMRE_R_AH         = 32'b1001001??????????101?????0110011;
  localparam [31:0] VFCLASS_AH         = 32'b100110000001?????001?????0110011;
  localparam [31:0] VFSGNJ_AH          = 32'b1001101??????????001?????0110011;
  localparam [31:0] VFSGNJ_R_AH        = 32'b1001101??????????101?????0110011;
  localparam [31:0] VFSGNJN_AH         = 32'b1001110??????????001?????0110011;
  localparam [31:0] VFSGNJN_R_AH       = 32'b1001110??????????101?????0110011;
  localparam [31:0] VFSGNJX_AH         = 32'b1001111??????????001?????0110011;
  localparam [31:0] VFSGNJX_R_AH       = 32'b1001111??????????101?????0110011;
  localparam [31:0] VFEQ_AH            = 32'b1010000??????????001?????0110011;
  localparam [31:0] VFEQ_R_AH          = 32'b1010000??????????101?????0110011;
  localparam [31:0] VFNE_AH            = 32'b1010001??????????001?????0110011;
  localparam [31:0] VFNE_R_AH          = 32'b1010001??????????101?????0110011;
  localparam [31:0] VFLT_AH            = 32'b1010010??????????001?????0110011;
  localparam [31:0] VFLT_R_AH          = 32'b1010010??????????101?????0110011;
  localparam [31:0] VFGE_AH            = 32'b1010011??????????001?????0110011;
  localparam [31:0] VFGE_R_AH          = 32'b1010011??????????101?????0110011;
  localparam [31:0] VFLE_AH            = 32'b1010100??????????001?????0110011;
  localparam [31:0] VFLE_R_AH          = 32'b1010100??????????101?????0110011;
  localparam [31:0] VFGT_AH            = 32'b1010101??????????001?????0110011;
  localparam [31:0] VFGT_R_AH          = 32'b1010101??????????101?????0110011;
  localparam [31:0] VFMV_X_AH          = 32'b100110000000?????001?????0110011;
  localparam [31:0] VFMV_AH_X          = 32'b100110000000?????101?????0110011;
  localparam [31:0] VFCVT_X_AH         = 32'b100110000010?????001?????0110011;
  localparam [31:0] VFCVT_XU_AH        = 32'b100110000010?????101?????0110011;
  localparam [31:0] VFCVT_AH_X         = 32'b100110000011?????001?????0110011;
  localparam [31:0] VFCVT_AH_XU        = 32'b100110000011?????101?????0110011;
  localparam [31:0] VFCPKA_AH_S        = 32'b1011000??????????001?????0110011;
  localparam [31:0] VFCPKB_AH_S        = 32'b1011000??????????101?????0110011;
  localparam [31:0] VFCPKC_AH_S        = 32'b1011001??????????001?????0110011;
  localparam [31:0] VFCPKD_AH_S        = 32'b1011001??????????101?????0110011;
  localparam [31:0] VFCPKA_AH_D        = 32'b1011010??????????001?????0110011;
  localparam [31:0] VFCPKB_AH_D        = 32'b1011010??????????101?????0110011;
  localparam [31:0] VFCPKC_AH_D        = 32'b1011011??????????001?????0110011;
  localparam [31:0] VFCPKD_AH_D        = 32'b1011011??????????101?????0110011;
  localparam [31:0] VFCVT_S_AH         = 32'b100110000101?????000?????0110011;
  localparam [31:0] VFCVTU_S_AH        = 32'b100110000101?????100?????0110011;
  localparam [31:0] VFCVT_AH_S         = 32'b100110000100?????001?????0110011;
  localparam [31:0] VFCVTU_AH_S        = 32'b100110000100?????101?????0110011;
  localparam [31:0] VFCVT_H_AH         = 32'b100110000101?????010?????0110011;
  localparam [31:0] VFCVTU_H_AH        = 32'b100110000101?????110?????0110011;
  localparam [31:0] VFCVT_AH_H         = 32'b100110000110?????001?????0110011;
  localparam [31:0] VFCVTU_AH_H        = 32'b100110000110?????101?????0110011;
  localparam [31:0] VFADD_B            = 32'b1000001??????????011?????0110011;
  localparam [31:0] VFADD_R_B          = 32'b1000001??????????111?????0110011;
  localparam [31:0] VFSUB_B            = 32'b1000010??????????011?????0110011;
  localparam [31:0] VFSUB_R_B          = 32'b1000010??????????111?????0110011;
  localparam [31:0] VFMUL_B            = 32'b1000011??????????011?????0110011;
  localparam [31:0] VFMUL_R_B          = 32'b1000011??????????111?????0110011;
  localparam [31:0] VFDIV_B            = 32'b1000100??????????011?????0110011;
  localparam [31:0] VFDIV_R_B          = 32'b1000100??????????111?????0110011;
  localparam [31:0] VFMIN_B            = 32'b1000101??????????011?????0110011;
  localparam [31:0] VFMIN_R_B          = 32'b1000101??????????111?????0110011;
  localparam [31:0] VFMAX_B            = 32'b1000110??????????011?????0110011;
  localparam [31:0] VFMAX_R_B          = 32'b1000110??????????111?????0110011;
  localparam [31:0] VFSQRT_B           = 32'b100011100000?????011?????0110011;
  localparam [31:0] VFMAC_B            = 32'b1001000??????????011?????0110011;
  localparam [31:0] VFMAC_R_B          = 32'b1001000??????????111?????0110011;
  localparam [31:0] VFMRE_B            = 32'b1001001??????????011?????0110011;
  localparam [31:0] VFMRE_R_B          = 32'b1001001??????????111?????0110011;
  localparam [31:0] VFSGNJ_B           = 32'b1001101??????????011?????0110011;
  localparam [31:0] VFSGNJ_R_B         = 32'b1001101??????????111?????0110011;
  localparam [31:0] VFSGNJN_B          = 32'b1001110??????????011?????0110011;
  localparam [31:0] VFSGNJN_R_B        = 32'b1001110??????????111?????0110011;
  localparam [31:0] VFSGNJX_B          = 32'b1001111??????????011?????0110011;
  localparam [31:0] VFSGNJX_R_B        = 32'b1001111??????????111?????0110011;
  localparam [31:0] VFEQ_B             = 32'b1010000??????????011?????0110011;
  localparam [31:0] VFEQ_R_B           = 32'b1010000??????????111?????0110011;
  localparam [31:0] VFNE_B             = 32'b1010001??????????011?????0110011;
  localparam [31:0] VFNE_R_B           = 32'b1010001??????????111?????0110011;
  localparam [31:0] VFLT_B             = 32'b1010010??????????011?????0110011;
  localparam [31:0] VFLT_R_B           = 32'b1010010??????????111?????0110011;
  localparam [31:0] VFGE_B             = 32'b1010011??????????011?????0110011;
  localparam [31:0] VFGE_R_B           = 32'b1010011??????????111?????0110011;
  localparam [31:0] VFLE_B             = 32'b1010100??????????011?????0110011;
  localparam [31:0] VFLE_R_B           = 32'b1010100??????????111?????0110011;
  localparam [31:0] VFGT_B             = 32'b1010101??????????011?????0110011;
  localparam [31:0] VFGT_R_B           = 32'b1010101??????????111?????0110011;
  localparam [31:0] VFMV_X_B           = 32'b100110000000?????011?????0110011;
  localparam [31:0] VFMV_B_X           = 32'b100110000000?????111?????0110011;
  localparam [31:0] VFCLASS_B          = 32'b100110000001?????011?????0110011;
  localparam [31:0] VFCVT_X_B          = 32'b100110000010?????011?????0110011;
  localparam [31:0] VFCVT_XU_B         = 32'b100110000010?????111?????0110011;
  localparam [31:0] VFCVT_B_X          = 32'b100110000011?????011?????0110011;
  localparam [31:0] VFCVT_B_XU         = 32'b100110000011?????111?????0110011;
  localparam [31:0] VFCPKA_B_S         = 32'b1011000??????????011?????0110011;
  localparam [31:0] VFCPKB_B_S         = 32'b1011000??????????111?????0110011;
  localparam [31:0] VFCPKC_B_S         = 32'b1011001??????????011?????0110011;
  localparam [31:0] VFCPKD_B_S         = 32'b1011001??????????111?????0110011;
  localparam [31:0] VFCPKA_B_D         = 32'b1011010??????????011?????0110011;
  localparam [31:0] VFCPKB_B_D         = 32'b1011010??????????111?????0110011;
  localparam [31:0] VFCPKC_B_D         = 32'b1011011??????????011?????0110011;
  localparam [31:0] VFCPKD_B_D         = 32'b1011011??????????111?????0110011;
  localparam [31:0] VFCVT_S_B          = 32'b100110000111?????000?????0110011;
  localparam [31:0] VFCVTU_S_B         = 32'b100110000111?????100?????0110011;
  localparam [31:0] VFCVT_B_S          = 32'b100110000100?????011?????0110011;
  localparam [31:0] VFCVTU_B_S         = 32'b100110000100?????111?????0110011;
  localparam [31:0] VFCVT_H_B          = 32'b100110000111?????010?????0110011;
  localparam [31:0] VFCVTU_H_B         = 32'b100110000111?????110?????0110011;
  localparam [31:0] VFCVT_B_H          = 32'b100110000110?????011?????0110011;
  localparam [31:0] VFCVTU_B_H         = 32'b100110000110?????111?????0110011;
  localparam [31:0] VFCVT_AH_B         = 32'b100110000111?????001?????0110011;
  localparam [31:0] VFCVTU_AH_B        = 32'b100110000111?????101?????0110011;
  localparam [31:0] VFCVT_B_AH         = 32'b100110000101?????011?????0110011;
  localparam [31:0] VFCVTU_B_AH        = 32'b100110000101?????111?????0110011;
  localparam [31:0] VFDOTP_S           = 32'b1001010??????????000?????0110011;
  localparam [31:0] VFDOTP_R_S         = 32'b1001010??????????100?????0110011;
  localparam [31:0] VFAVG_S            = 32'b1010110??????????000?????0110011;
  localparam [31:0] VFAVG_R_S          = 32'b1010110??????????100?????0110011;
  localparam [31:0] FMULEX_S_H         = 32'b0100110??????????????????1010011;
  localparam [31:0] FMACEX_S_H         = 32'b0101010??????????????????1010011;
  localparam [31:0] VFDOTP_H           = 32'b1001010??????????010?????0110011;
  localparam [31:0] VFDOTP_R_H         = 32'b1001010??????????110?????0110011;
  localparam [31:0] VFDOTPEX_S_H       = 32'b1001011??????????010?????0110011;
  localparam [31:0] VFDOTPEX_S_R_H     = 32'b1001011??????????110?????0110011;
  localparam [31:0] VFAVG_H            = 32'b1010110??????????010?????0110011;
  localparam [31:0] VFAVG_R_H          = 32'b1010110??????????110?????0110011;
  localparam [31:0] FMULEX_S_AH        = 32'b0100110??????????101?????1010011;
  localparam [31:0] FMACEX_S_AH        = 32'b0101010??????????101?????1010011;
  localparam [31:0] VFDOTP_AH          = 32'b1001010??????????001?????0110011;
  localparam [31:0] VFDOTP_R_AH        = 32'b1001010??????????101?????0110011;
  localparam [31:0] VFDOTPEX_S_AH      = 32'b1001011??????????001?????0110011;
  localparam [31:0] VFDOTPEX_S_R_AH    = 32'b1001011??????????101?????0110011;
  localparam [31:0] VFAVG_AH           = 32'b1010110??????????001?????0110011;
  localparam [31:0] VFAVG_R_AH         = 32'b1010110??????????101?????0110011;
  localparam [31:0] FMULEX_S_B         = 32'b0100111??????????????????1010011;
  localparam [31:0] FMACEX_S_B         = 32'b0101011??????????????????1010011;
  localparam [31:0] VFDOTP_B           = 32'b1001010??????????011?????0110011;
  localparam [31:0] VFDOTP_R_B         = 32'b1001010??????????111?????0110011;
  localparam [31:0] VFDOTPEX_S_B       = 32'b1001011??????????011?????0110011;
  localparam [31:0] VFDOTPEX_S_R_B     = 32'b1001011??????????111?????0110011;
  localparam [31:0] VFAVG_B            = 32'b1010110??????????011?????0110011;
  localparam [31:0] VFAVG_R_B          = 32'b1010110??????????111?????0110011;
  /* CSR Addresses */
  localparam logic [11:0] CSR_FFLAGS = 12'h1;
  localparam logic [11:0] CSR_FRM = 12'h2;
  localparam logic [11:0] CSR_FCSR = 12'h3;
  localparam logic [11:0] CSR_CYCLE = 12'hc00;
  localparam logic [11:0] CSR_TIME = 12'hc01;
  localparam logic [11:0] CSR_INSTRET = 12'hc02;
  localparam logic [11:0] CSR_HPMCOUNTER3 = 12'hc03;
  localparam logic [11:0] CSR_HPMCOUNTER4 = 12'hc04;
  localparam logic [11:0] CSR_HPMCOUNTER5 = 12'hc05;
  localparam logic [11:0] CSR_HPMCOUNTER6 = 12'hc06;
  localparam logic [11:0] CSR_HPMCOUNTER7 = 12'hc07;
  localparam logic [11:0] CSR_HPMCOUNTER8 = 12'hc08;
  localparam logic [11:0] CSR_HPMCOUNTER9 = 12'hc09;
  localparam logic [11:0] CSR_HPMCOUNTER10 = 12'hc0a;
  localparam logic [11:0] CSR_HPMCOUNTER11 = 12'hc0b;
  localparam logic [11:0] CSR_HPMCOUNTER12 = 12'hc0c;
  localparam logic [11:0] CSR_HPMCOUNTER13 = 12'hc0d;
  localparam logic [11:0] CSR_HPMCOUNTER14 = 12'hc0e;
  localparam logic [11:0] CSR_HPMCOUNTER15 = 12'hc0f;
  localparam logic [11:0] CSR_HPMCOUNTER16 = 12'hc10;
  localparam logic [11:0] CSR_HPMCOUNTER17 = 12'hc11;
  localparam logic [11:0] CSR_HPMCOUNTER18 = 12'hc12;
  localparam logic [11:0] CSR_HPMCOUNTER19 = 12'hc13;
  localparam logic [11:0] CSR_HPMCOUNTER20 = 12'hc14;
  localparam logic [11:0] CSR_HPMCOUNTER21 = 12'hc15;
  localparam logic [11:0] CSR_HPMCOUNTER22 = 12'hc16;
  localparam logic [11:0] CSR_HPMCOUNTER23 = 12'hc17;
  localparam logic [11:0] CSR_HPMCOUNTER24 = 12'hc18;
  localparam logic [11:0] CSR_HPMCOUNTER25 = 12'hc19;
  localparam logic [11:0] CSR_HPMCOUNTER26 = 12'hc1a;
  localparam logic [11:0] CSR_HPMCOUNTER27 = 12'hc1b;
  localparam logic [11:0] CSR_HPMCOUNTER28 = 12'hc1c;
  localparam logic [11:0] CSR_HPMCOUNTER29 = 12'hc1d;
  localparam logic [11:0] CSR_HPMCOUNTER30 = 12'hc1e;
  localparam logic [11:0] CSR_HPMCOUNTER31 = 12'hc1f;
  localparam logic [11:0] CSR_SSTATUS = 12'h100;
  localparam logic [11:0] CSR_SIE = 12'h104;
  localparam logic [11:0] CSR_STVEC = 12'h105;
  localparam logic [11:0] CSR_SCOUNTEREN = 12'h106;
  localparam logic [11:0] CSR_SSCRATCH = 12'h140;
  localparam logic [11:0] CSR_SEPC = 12'h141;
  localparam logic [11:0] CSR_SCAUSE = 12'h142;
  localparam logic [11:0] CSR_STVAL = 12'h143;
  localparam logic [11:0] CSR_SIP = 12'h144;
  localparam logic [11:0] CSR_SATP = 12'h180;
  localparam logic [11:0] CSR_BSSTATUS = 12'h200;
  localparam logic [11:0] CSR_BSIE = 12'h204;
  localparam logic [11:0] CSR_BSTVEC = 12'h205;
  localparam logic [11:0] CSR_BSSCRATCH = 12'h240;
  localparam logic [11:0] CSR_BSEPC = 12'h241;
  localparam logic [11:0] CSR_BSCAUSE = 12'h242;
  localparam logic [11:0] CSR_BSTVAL = 12'h243;
  localparam logic [11:0] CSR_BSIP = 12'h244;
  localparam logic [11:0] CSR_BSATP = 12'h280;
  localparam logic [11:0] CSR_HSTATUS = 12'ha00;
  localparam logic [11:0] CSR_HEDELEG = 12'ha02;
  localparam logic [11:0] CSR_HIDELEG = 12'ha03;
  localparam logic [11:0] CSR_HGATP = 12'ha80;
  localparam logic [11:0] CSR_UTVT = 12'h7;
  localparam logic [11:0] CSR_UNXTI = 12'h45;
  localparam logic [11:0] CSR_UINTSTATUS = 12'h46;
  localparam logic [11:0] CSR_USCRATCHCSW = 12'h48;
  localparam logic [11:0] CSR_USCRATCHCSWL = 12'h49;
  localparam logic [11:0] CSR_STVT = 12'h107;
  localparam logic [11:0] CSR_SNXTI = 12'h145;
  localparam logic [11:0] CSR_SINTSTATUS = 12'h146;
  localparam logic [11:0] CSR_SSCRATCHCSW = 12'h148;
  localparam logic [11:0] CSR_SSCRATCHCSWL = 12'h149;
  localparam logic [11:0] CSR_MTVT = 12'h307;
  localparam logic [11:0] CSR_MNXTI = 12'h345;
  localparam logic [11:0] CSR_MINTSTATUS = 12'h346;
  localparam logic [11:0] CSR_MSCRATCHCSW = 12'h348;
  localparam logic [11:0] CSR_MSCRATCHCSWL = 12'h349;
  localparam logic [11:0] CSR_MSTATUS = 12'h300;
  localparam logic [11:0] CSR_MISA = 12'h301;
  localparam logic [11:0] CSR_MEDELEG = 12'h302;
  localparam logic [11:0] CSR_MIDELEG = 12'h303;
  localparam logic [11:0] CSR_MIE = 12'h304;
  localparam logic [11:0] CSR_MTVEC = 12'h305;
  localparam logic [11:0] CSR_MCOUNTEREN = 12'h306;
  localparam logic [11:0] CSR_MSCRATCH = 12'h340;
  localparam logic [11:0] CSR_MEPC = 12'h341;
  localparam logic [11:0] CSR_MCAUSE = 12'h342;
  localparam logic [11:0] CSR_MTVAL = 12'h343;
  localparam logic [11:0] CSR_MIP = 12'h344;
  localparam logic [11:0] CSR_PMPCFG0 = 12'h3a0;
  localparam logic [11:0] CSR_PMPCFG1 = 12'h3a1;
  localparam logic [11:0] CSR_PMPCFG2 = 12'h3a2;
  localparam logic [11:0] CSR_PMPCFG3 = 12'h3a3;
  localparam logic [11:0] CSR_PMPADDR0 = 12'h3b0;
  localparam logic [11:0] CSR_PMPADDR1 = 12'h3b1;
  localparam logic [11:0] CSR_PMPADDR2 = 12'h3b2;
  localparam logic [11:0] CSR_PMPADDR3 = 12'h3b3;
  localparam logic [11:0] CSR_PMPADDR4 = 12'h3b4;
  localparam logic [11:0] CSR_PMPADDR5 = 12'h3b5;
  localparam logic [11:0] CSR_PMPADDR6 = 12'h3b6;
  localparam logic [11:0] CSR_PMPADDR7 = 12'h3b7;
  localparam logic [11:0] CSR_PMPADDR8 = 12'h3b8;
  localparam logic [11:0] CSR_PMPADDR9 = 12'h3b9;
  localparam logic [11:0] CSR_PMPADDR10 = 12'h3ba;
  localparam logic [11:0] CSR_PMPADDR11 = 12'h3bb;
  localparam logic [11:0] CSR_PMPADDR12 = 12'h3bc;
  localparam logic [11:0] CSR_PMPADDR13 = 12'h3bd;
  localparam logic [11:0] CSR_PMPADDR14 = 12'h3be;
  localparam logic [11:0] CSR_PMPADDR15 = 12'h3bf;
  localparam logic [11:0] CSR_TSELECT = 12'h7a0;
  localparam logic [11:0] CSR_TDATA1 = 12'h7a1;
  localparam logic [11:0] CSR_TDATA2 = 12'h7a2;
  localparam logic [11:0] CSR_TDATA3 = 12'h7a3;
  localparam logic [11:0] CSR_DCSR = 12'h7b0;
  localparam logic [11:0] CSR_DPC = 12'h7b1;
  localparam logic [11:0] CSR_DSCRATCH = 12'h7b2;
  localparam logic [11:0] CSR_MCYCLE = 12'hb00;
  localparam logic [11:0] CSR_MINSTRET = 12'hb02;
  localparam logic [11:0] CSR_MHPMCOUNTER3 = 12'hb03;
  localparam logic [11:0] CSR_MHPMCOUNTER4 = 12'hb04;
  localparam logic [11:0] CSR_MHPMCOUNTER5 = 12'hb05;
  localparam logic [11:0] CSR_MHPMCOUNTER6 = 12'hb06;
  localparam logic [11:0] CSR_MHPMCOUNTER7 = 12'hb07;
  localparam logic [11:0] CSR_MHPMCOUNTER8 = 12'hb08;
  localparam logic [11:0] CSR_MHPMCOUNTER9 = 12'hb09;
  localparam logic [11:0] CSR_MHPMCOUNTER10 = 12'hb0a;
  localparam logic [11:0] CSR_MHPMCOUNTER11 = 12'hb0b;
  localparam logic [11:0] CSR_MHPMCOUNTER12 = 12'hb0c;
  localparam logic [11:0] CSR_MHPMCOUNTER13 = 12'hb0d;
  localparam logic [11:0] CSR_MHPMCOUNTER14 = 12'hb0e;
  localparam logic [11:0] CSR_MHPMCOUNTER15 = 12'hb0f;
  localparam logic [11:0] CSR_MHPMCOUNTER16 = 12'hb10;
  localparam logic [11:0] CSR_MHPMCOUNTER17 = 12'hb11;
  localparam logic [11:0] CSR_MHPMCOUNTER18 = 12'hb12;
  localparam logic [11:0] CSR_MHPMCOUNTER19 = 12'hb13;
  localparam logic [11:0] CSR_MHPMCOUNTER20 = 12'hb14;
  localparam logic [11:0] CSR_MHPMCOUNTER21 = 12'hb15;
  localparam logic [11:0] CSR_MHPMCOUNTER22 = 12'hb16;
  localparam logic [11:0] CSR_MHPMCOUNTER23 = 12'hb17;
  localparam logic [11:0] CSR_MHPMCOUNTER24 = 12'hb18;
  localparam logic [11:0] CSR_MHPMCOUNTER25 = 12'hb19;
  localparam logic [11:0] CSR_MHPMCOUNTER26 = 12'hb1a;
  localparam logic [11:0] CSR_MHPMCOUNTER27 = 12'hb1b;
  localparam logic [11:0] CSR_MHPMCOUNTER28 = 12'hb1c;
  localparam logic [11:0] CSR_MHPMCOUNTER29 = 12'hb1d;
  localparam logic [11:0] CSR_MHPMCOUNTER30 = 12'hb1e;
  localparam logic [11:0] CSR_MHPMCOUNTER31 = 12'hb1f;
  localparam logic [11:0] CSR_MHPMEVENT3 = 12'h323;
  localparam logic [11:0] CSR_MHPMEVENT4 = 12'h324;
  localparam logic [11:0] CSR_MHPMEVENT5 = 12'h325;
  localparam logic [11:0] CSR_MHPMEVENT6 = 12'h326;
  localparam logic [11:0] CSR_MHPMEVENT7 = 12'h327;
  localparam logic [11:0] CSR_MHPMEVENT8 = 12'h328;
  localparam logic [11:0] CSR_MHPMEVENT9 = 12'h329;
  localparam logic [11:0] CSR_MHPMEVENT10 = 12'h32a;
  localparam logic [11:0] CSR_MHPMEVENT11 = 12'h32b;
  localparam logic [11:0] CSR_MHPMEVENT12 = 12'h32c;
  localparam logic [11:0] CSR_MHPMEVENT13 = 12'h32d;
  localparam logic [11:0] CSR_MHPMEVENT14 = 12'h32e;
  localparam logic [11:0] CSR_MHPMEVENT15 = 12'h32f;
  localparam logic [11:0] CSR_MHPMEVENT16 = 12'h330;
  localparam logic [11:0] CSR_MHPMEVENT17 = 12'h331;
  localparam logic [11:0] CSR_MHPMEVENT18 = 12'h332;
  localparam logic [11:0] CSR_MHPMEVENT19 = 12'h333;
  localparam logic [11:0] CSR_MHPMEVENT20 = 12'h334;
  localparam logic [11:0] CSR_MHPMEVENT21 = 12'h335;
  localparam logic [11:0] CSR_MHPMEVENT22 = 12'h336;
  localparam logic [11:0] CSR_MHPMEVENT23 = 12'h337;
  localparam logic [11:0] CSR_MHPMEVENT24 = 12'h338;
  localparam logic [11:0] CSR_MHPMEVENT25 = 12'h339;
  localparam logic [11:0] CSR_MHPMEVENT26 = 12'h33a;
  localparam logic [11:0] CSR_MHPMEVENT27 = 12'h33b;
  localparam logic [11:0] CSR_MHPMEVENT28 = 12'h33c;
  localparam logic [11:0] CSR_MHPMEVENT29 = 12'h33d;
  localparam logic [11:0] CSR_MHPMEVENT30 = 12'h33e;
  localparam logic [11:0] CSR_MHPMEVENT31 = 12'h33f;
  localparam logic [11:0] CSR_MVENDORID = 12'hf11;
  localparam logic [11:0] CSR_MARCHID = 12'hf12;
  localparam logic [11:0] CSR_MIMPID = 12'hf13;
  localparam logic [11:0] CSR_MHARTID = 12'hf14;
  localparam logic [11:0] CSR_CYCLEH = 12'hc80;
  localparam logic [11:0] CSR_TIMEH = 12'hc81;
  localparam logic [11:0] CSR_INSTRETH = 12'hc82;
  localparam logic [11:0] CSR_HPMCOUNTER3H = 12'hc83;
  localparam logic [11:0] CSR_HPMCOUNTER4H = 12'hc84;
  localparam logic [11:0] CSR_HPMCOUNTER5H = 12'hc85;
  localparam logic [11:0] CSR_HPMCOUNTER6H = 12'hc86;
  localparam logic [11:0] CSR_HPMCOUNTER7H = 12'hc87;
  localparam logic [11:0] CSR_HPMCOUNTER8H = 12'hc88;
  localparam logic [11:0] CSR_HPMCOUNTER9H = 12'hc89;
  localparam logic [11:0] CSR_HPMCOUNTER10H = 12'hc8a;
  localparam logic [11:0] CSR_HPMCOUNTER11H = 12'hc8b;
  localparam logic [11:0] CSR_HPMCOUNTER12H = 12'hc8c;
  localparam logic [11:0] CSR_HPMCOUNTER13H = 12'hc8d;
  localparam logic [11:0] CSR_HPMCOUNTER14H = 12'hc8e;
  localparam logic [11:0] CSR_HPMCOUNTER15H = 12'hc8f;
  localparam logic [11:0] CSR_HPMCOUNTER16H = 12'hc90;
  localparam logic [11:0] CSR_HPMCOUNTER17H = 12'hc91;
  localparam logic [11:0] CSR_HPMCOUNTER18H = 12'hc92;
  localparam logic [11:0] CSR_HPMCOUNTER19H = 12'hc93;
  localparam logic [11:0] CSR_HPMCOUNTER20H = 12'hc94;
  localparam logic [11:0] CSR_HPMCOUNTER21H = 12'hc95;
  localparam logic [11:0] CSR_HPMCOUNTER22H = 12'hc96;
  localparam logic [11:0] CSR_HPMCOUNTER23H = 12'hc97;
  localparam logic [11:0] CSR_HPMCOUNTER24H = 12'hc98;
  localparam logic [11:0] CSR_HPMCOUNTER25H = 12'hc99;
  localparam logic [11:0] CSR_HPMCOUNTER26H = 12'hc9a;
  localparam logic [11:0] CSR_HPMCOUNTER27H = 12'hc9b;
  localparam logic [11:0] CSR_HPMCOUNTER28H = 12'hc9c;
  localparam logic [11:0] CSR_HPMCOUNTER29H = 12'hc9d;
  localparam logic [11:0] CSR_HPMCOUNTER30H = 12'hc9e;
  localparam logic [11:0] CSR_HPMCOUNTER31H = 12'hc9f;
  localparam logic [11:0] CSR_MCYCLEH = 12'hb80;
  localparam logic [11:0] CSR_MINSTRETH = 12'hb82;
  localparam logic [11:0] CSR_MHPMCOUNTER3H = 12'hb83;
  localparam logic [11:0] CSR_MHPMCOUNTER4H = 12'hb84;
  localparam logic [11:0] CSR_MHPMCOUNTER5H = 12'hb85;
  localparam logic [11:0] CSR_MHPMCOUNTER6H = 12'hb86;
  localparam logic [11:0] CSR_MHPMCOUNTER7H = 12'hb87;
  localparam logic [11:0] CSR_MHPMCOUNTER8H = 12'hb88;
  localparam logic [11:0] CSR_MHPMCOUNTER9H = 12'hb89;
  localparam logic [11:0] CSR_MHPMCOUNTER10H = 12'hb8a;
  localparam logic [11:0] CSR_MHPMCOUNTER11H = 12'hb8b;
  localparam logic [11:0] CSR_MHPMCOUNTER12H = 12'hb8c;
  localparam logic [11:0] CSR_MHPMCOUNTER13H = 12'hb8d;
  localparam logic [11:0] CSR_MHPMCOUNTER14H = 12'hb8e;
  localparam logic [11:0] CSR_MHPMCOUNTER15H = 12'hb8f;
  localparam logic [11:0] CSR_MHPMCOUNTER16H = 12'hb90;
  localparam logic [11:0] CSR_MHPMCOUNTER17H = 12'hb91;
  localparam logic [11:0] CSR_MHPMCOUNTER18H = 12'hb92;
  localparam logic [11:0] CSR_MHPMCOUNTER19H = 12'hb93;
  localparam logic [11:0] CSR_MHPMCOUNTER20H = 12'hb94;
  localparam logic [11:0] CSR_MHPMCOUNTER21H = 12'hb95;
  localparam logic [11:0] CSR_MHPMCOUNTER22H = 12'hb96;
  localparam logic [11:0] CSR_MHPMCOUNTER23H = 12'hb97;
  localparam logic [11:0] CSR_MHPMCOUNTER24H = 12'hb98;
  localparam logic [11:0] CSR_MHPMCOUNTER25H = 12'hb99;
  localparam logic [11:0] CSR_MHPMCOUNTER26H = 12'hb9a;
  localparam logic [11:0] CSR_MHPMCOUNTER27H = 12'hb9b;
  localparam logic [11:0] CSR_MHPMCOUNTER28H = 12'hb9c;
  localparam logic [11:0] CSR_MHPMCOUNTER29H = 12'hb9d;
  localparam logic [11:0] CSR_MHPMCOUNTER30H = 12'hb9e;
  localparam logic [11:0] CSR_MHPMCOUNTER31H = 12'hb9f;
endpackage
// Copyright 2019 ETH Zurich and University of Bologna.
//
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Stefan Mach <smach@iis.ee.ethz.ch>

package fpnew_pkg;

  // ---------
  // FP TYPES
  // ---------
  // | Enumerator | Format           | Width  | EXP_BITS | MAN_BITS
  // |:----------:|------------------|-------:|:--------:|:--------:
  // | FP32       | IEEE binary32    | 32 bit | 8        | 23
  // | FP64       | IEEE binary64    | 64 bit | 11       | 52
  // | FP16       | IEEE binary16    | 16 bit | 5        | 10
  // | FP8        | binary8          |  8 bit | 5        | 2
  // | FP16ALT    | binary16alt      | 16 bit | 8        | 7
  // *NOTE:* Add new formats only at the end of the enumeration for backwards compatibilty!

  // Encoding for a format
  typedef struct packed {
    int unsigned exp_bits;
    int unsigned man_bits;
  } fp_encoding_t;

  localparam int unsigned NUM_FP_FORMATS = 5; // change me to add formats
  localparam int unsigned FP_FORMAT_BITS = $clog2(NUM_FP_FORMATS);

  // FP formats
  typedef enum logic [FP_FORMAT_BITS-1:0] {
    FP32    = 'd0,
    FP64    = 'd1,
    FP16    = 'd2,
    FP8     = 'd3,
    FP16ALT = 'd4
    // add new formats here
  } fp_format_e;

  // Encodings for supported FP formats
  localparam fp_encoding_t [0:NUM_FP_FORMATS-1] FP_ENCODINGS  = '{
    '{8,  23}, // IEEE binary32 (single)
    '{11, 52}, // IEEE binary64 (double)
    '{5,  10}, // IEEE binary16 (half)
    '{5,  2},  // custom binary8
    '{8,  7}   // custom binary16alt
    // add new formats here
  };

  typedef logic [0:NUM_FP_FORMATS-1]       fmt_logic_t;    // Logic indexed by FP format (for masks)
  typedef logic [0:NUM_FP_FORMATS-1][31:0] fmt_unsigned_t; // Unsigned indexed by FP format

  localparam fmt_logic_t CPK_FORMATS = 5'b11000; // FP32 and FP64 can provide CPK only

  // ---------
  // INT TYPES
  // ---------
  // | Enumerator | Width  |
  // |:----------:|-------:|
  // | INT8       |  8 bit |
  // | INT16      | 16 bit |
  // | INT32      | 32 bit |
  // | INT64      | 64 bit |
  // *NOTE:* Add new formats only at the end of the enumeration for backwards compatibilty!

  localparam int unsigned NUM_INT_FORMATS = 4; // change me to add formats
  localparam int unsigned INT_FORMAT_BITS = $clog2(NUM_INT_FORMATS);

  // Int formats
  typedef enum logic [INT_FORMAT_BITS-1:0] {
    INT8,
    INT16,
    INT32,
    INT64
    // add new formats here
  } int_format_e;

  // Returns the width of an INT format by index
  function automatic int unsigned int_width(int_format_e ifmt);
    unique case (ifmt)
      INT8:  return 8;
      INT16: return 16;
      INT32: return 32;
      INT64: return 64;
    endcase
  endfunction

  typedef logic [0:NUM_INT_FORMATS-1] ifmt_logic_t; // Logic indexed by INT format (for masks)

  // --------------
  // FP OPERATIONS
  // --------------
  localparam int unsigned NUM_OPGROUPS = 4;

  // Each FP operation belongs to an operation group
  typedef enum logic [1:0] {
    ADDMUL, DIVSQRT, NONCOMP, CONV
  } opgroup_e;

  localparam int unsigned OP_BITS = 4;

  typedef enum logic [OP_BITS-1:0] {
    FMADD, FNMSUB, ADD, MUL,     // ADDMUL operation group
    DIV, SQRT,                   // DIVSQRT operation group
    SGNJ, MINMAX, CMP, CLASSIFY, // NONCOMP operation group
    F2F, F2I, I2F, CPKAB, CPKCD  // CONV operation group
  } operation_e;

  // -------------------
  // RISC-V FP-SPECIFIC
  // -------------------
  // Rounding modes
  typedef enum logic [2:0] {
    RNE = 3'b000,
    RTZ = 3'b001,
    RDN = 3'b010,
    RUP = 3'b011,
    RMM = 3'b100,
    DYN = 3'b111
  } roundmode_e;

  // Status flags
  typedef struct packed {
    logic NV; // Invalid
    logic DZ; // Divide by zero
    logic OF; // Overflow
    logic UF; // Underflow
    logic NX; // Inexact
  } status_t;

  // Information about a floating point value
  typedef struct packed {
    logic is_normal;     // is the value normal
    logic is_subnormal;  // is the value subnormal
    logic is_zero;       // is the value zero
    logic is_inf;        // is the value infinity
    logic is_nan;        // is the value NaN
    logic is_signalling; // is the value a signalling NaN
    logic is_quiet;      // is the value a quiet NaN
    logic is_boxed;      // is the value properly NaN-boxed (RISC-V specific)
  } fp_info_t;

  // Classification mask
  typedef enum logic [9:0] {
    NEGINF     = 10'b00_0000_0001,
    NEGNORM    = 10'b00_0000_0010,
    NEGSUBNORM = 10'b00_0000_0100,
    NEGZERO    = 10'b00_0000_1000,
    POSZERO    = 10'b00_0001_0000,
    POSSUBNORM = 10'b00_0010_0000,
    POSNORM    = 10'b00_0100_0000,
    POSINF     = 10'b00_1000_0000,
    SNAN       = 10'b01_0000_0000,
    QNAN       = 10'b10_0000_0000
  } classmask_e;

  // ------------------
  // FPU configuration
  // ------------------
  // Pipelining registers can be inserted (at elaboration time) into operational units
  typedef enum logic [1:0] {
    BEFORE,     // registers are inserted at the inputs of the unit
    AFTER,      // registers are inserted at the outputs of the unit
    INSIDE,     // registers are inserted at predetermined (suboptimal) locations in the unit
    DISTRIBUTED // registers are evenly distributed, INSIDE >= AFTER >= BEFORE
  } pipe_config_t;

  // Arithmetic units can be arranged in parallel (per format), merged (multi-format) or not at all.
  typedef enum logic [1:0] {
    DISABLED, // arithmetic units are not generated
    PARALLEL, // arithmetic units are generated in prallel slices, one for each format
    MERGED    // arithmetic units are contained within a merged unit holding multiple formats
  } unit_type_t;

  // Array of unit types indexed by format
  typedef unit_type_t [0:NUM_FP_FORMATS-1] fmt_unit_types_t;

  // Array of format-specific unit types by opgroup
  typedef fmt_unit_types_t [0:NUM_OPGROUPS-1] opgrp_fmt_unit_types_t;
  // same with unsigned
  typedef fmt_unsigned_t [0:NUM_OPGROUPS-1] opgrp_fmt_unsigned_t;

  // FPU configuration: features
  typedef struct packed {
    int unsigned Width;
    logic        EnableVectors;
    logic        EnableNanBox;
    fmt_logic_t  FpFmtMask;
    ifmt_logic_t IntFmtMask;
  } fpu_features_t;

  localparam fpu_features_t RV64D = '{
    Width:         64,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11000,
    IntFmtMask:    4'b0011
  };

  localparam fpu_features_t RV32D = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11000,
    IntFmtMask:    4'b0010
  };

  localparam fpu_features_t RV32F = '{
    Width:         32,
    EnableVectors: 1'b0,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b10000,
    IntFmtMask:    4'b0010
  };

  localparam fpu_features_t RV64D_Xsflt = '{
    Width:         64,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b11111,
    IntFmtMask:    4'b1111
  };

  localparam fpu_features_t RV32F_Xsflt = '{
    Width:         32,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b10111,
    IntFmtMask:    4'b1110
  };

  localparam fpu_features_t RV32F_Xf16alt_Xfvec = '{
    Width:         32,
    EnableVectors: 1'b1,
    EnableNanBox:  1'b1,
    FpFmtMask:     5'b10001,
    IntFmtMask:    4'b0110
  };


  // FPU configuraion: implementation
  typedef struct packed {
    opgrp_fmt_unsigned_t   PipeRegs;
    opgrp_fmt_unit_types_t UnitTypes;
    pipe_config_t          PipeConfig;
  } fpu_implementation_t;

  localparam fpu_implementation_t DEFAULT_NOREGS = '{
    PipeRegs:   '{default: 0},
    UnitTypes:  '{'{default: PARALLEL}, // ADDMUL
                  '{default: MERGED},   // DIVSQRT
                  '{default: PARALLEL}, // NONCOMP
                  '{default: MERGED}},  // CONV
    PipeConfig: BEFORE
  };

  localparam fpu_implementation_t DEFAULT_SNITCH = '{
    PipeRegs:   '{default: 1},
    UnitTypes:  '{'{default: PARALLEL}, // ADDMUL
                  '{default: DISABLED}, // DIVSQRT
                  '{default: PARALLEL}, // NONCOMP
                  '{default: MERGED}},  // CONV
    PipeConfig: BEFORE
  };

  // -----------------------
  // Synthesis optimization
  // -----------------------
  localparam logic DONT_CARE = 1'b1; // the value to assign as don't care

  // -------------------------
  // General helper functions
  // -------------------------
  function automatic int minimum(int a, int b);
    return (a < b) ? a : b;
  endfunction

  function automatic int maximum(int a, int b);
    return (a > b) ? a : b;
  endfunction

  // -------------------------------------------
  // Helper functions for FP formats and values
  // -------------------------------------------
  // Returns the width of a FP format
  function automatic int unsigned fp_width(fp_format_e fmt);
    return FP_ENCODINGS[fmt].exp_bits + FP_ENCODINGS[fmt].man_bits + 1;
  endfunction

  // Returns the widest FP format present
  function automatic int unsigned max_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(maximum(res, fp_width(fp_format_e'(i))));
    return res;
  endfunction

  // Returns the narrowest FP format present
  function automatic int unsigned min_fp_width(fmt_logic_t cfg);
    automatic int unsigned res = max_fp_width(cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i])
        res = unsigned'(minimum(res, fp_width(fp_format_e'(i))));
    return res;
  endfunction

  // Returns the number of expoent bits for a format
  function automatic int unsigned exp_bits(fp_format_e fmt);
    return FP_ENCODINGS[fmt].exp_bits;
  endfunction

  // Returns the number of mantissa bits for a format
  function automatic int unsigned man_bits(fp_format_e fmt);
    return FP_ENCODINGS[fmt].man_bits;
  endfunction

  // Returns the bias value for a given format (as per IEEE 754-2008)
  function automatic int unsigned bias(fp_format_e fmt);
    return unsigned'(2**(FP_ENCODINGS[fmt].exp_bits-1)-1); // symmetrical bias
  endfunction

  function automatic fp_encoding_t super_format(fmt_logic_t cfg);
    automatic fp_encoding_t res;
    res = '0;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      if (cfg[fmt]) begin // only active format
        res.exp_bits = unsigned'(maximum(res.exp_bits, exp_bits(fp_format_e'(fmt))));
        res.man_bits = unsigned'(maximum(res.man_bits, man_bits(fp_format_e'(fmt))));
      end
    return res;
  endfunction

  // -------------------------------------------
  // Helper functions for INT formats and values
  // -------------------------------------------
  // Returns the widest INT format present
  function automatic int unsigned max_int_width(ifmt_logic_t cfg);
    automatic int unsigned res = 0;
    for (int ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++) begin
      if (cfg[ifmt]) res = maximum(res, int_width(int_format_e'(ifmt)));
    end
    return res;
  endfunction

  // --------------------------------------------------
  // Helper functions for operations and FPU structure
  // --------------------------------------------------
  // Returns the operation group of the given operation
  function automatic opgroup_e get_opgroup(operation_e op);
    unique case (op)
      FMADD, FNMSUB, ADD, MUL:     return ADDMUL;
      DIV, SQRT:                   return DIVSQRT;
      SGNJ, MINMAX, CMP, CLASSIFY: return NONCOMP;
      F2F, F2I, I2F, CPKAB, CPKCD: return CONV;
      default:                     return NONCOMP;
    endcase
  endfunction

  // Returns the number of operands by operation group
  function automatic int unsigned num_operands(opgroup_e grp);
    unique case (grp)
      ADDMUL:  return 3;
      DIVSQRT: return 2;
      NONCOMP: return 2;
      CONV:    return 3; // vectorial casts use 3 operands
      default: return 0;
    endcase
  endfunction

  // Returns the number of lanes according to width, format and vectors
  function automatic int unsigned num_lanes(int unsigned width, fp_format_e fmt, logic vec);
    return vec ? width / fp_width(fmt) : 1; // if no vectors, only one lane
  endfunction

  // Returns the maximum number of lanes in the FPU according to width, format config and vectors
  function automatic int unsigned max_num_lanes(int unsigned width, fmt_logic_t cfg, logic vec);
    return vec ? width / min_fp_width(cfg) : 1; // if no vectors, only one lane
  endfunction

  // Returns a mask of active FP formats that are present in lane lane_no of a multiformat slice
  function automatic fmt_logic_t get_lane_formats(int unsigned width,
                                                  fmt_logic_t cfg,
                                                  int unsigned lane_no);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format
      res[fmt] = cfg[fmt] & (width / fp_width(fp_format_e'(fmt)) > lane_no);
    return res;
  endfunction

  // Returns a mask of active INT formats that are present in lane lane_no of a multiformat slice
  function automatic ifmt_logic_t get_lane_int_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       ifmt_logic_t icfg,
                                                       int unsigned lane_no);
    automatic ifmt_logic_t res;
    automatic fmt_logic_t lanefmts;
    res = '0;
    lanefmts = get_lane_formats(width, cfg, lane_no);

    for (int unsigned ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++)
      for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
        // Mask active int formats with the width of the float formats
        if ((fp_width(fp_format_e'(fmt)) == int_width(int_format_e'(ifmt))))
          res[ifmt] |= icfg[ifmt] && lanefmts[fmt];
    return res;
  endfunction

  // Returns a mask of active FP formats that are present in lane lane_no of a CONV slice
  function automatic fmt_logic_t get_conv_lane_formats(int unsigned width,
                                                       fmt_logic_t cfg,
                                                       int unsigned lane_no);
    automatic fmt_logic_t res;
    for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
      // Mask active formats with the number of lanes for that format, CPK at least twice
      res[fmt] = cfg[fmt] && ((width / fp_width(fp_format_e'(fmt)) > lane_no) ||
                             (CPK_FORMATS[fmt] && (lane_no < 2)));
    return res;
  endfunction

  // Returns a mask of active INT formats that are present in lane lane_no of a CONV slice
  function automatic ifmt_logic_t get_conv_lane_int_formats(int unsigned width,
                                                            fmt_logic_t cfg,
                                                            ifmt_logic_t icfg,
                                                            int unsigned lane_no);
    automatic ifmt_logic_t res;
    automatic fmt_logic_t lanefmts;
    res = '0;
    lanefmts = get_conv_lane_formats(width, cfg, lane_no);

    for (int unsigned ifmt = 0; ifmt < NUM_INT_FORMATS; ifmt++)
      for (int unsigned fmt = 0; fmt < NUM_FP_FORMATS; fmt++)
        // Mask active int formats with the width of the float formats
        res[ifmt] |= icfg[ifmt] && lanefmts[fmt] &&
                     (fp_width(fp_format_e'(fmt)) == int_width(int_format_e'(ifmt)));
    return res;
  endfunction

  // Return whether any active format is set as MERGED
  function automatic logic any_enabled_multi(fmt_unit_types_t types, fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i] && types[i] == MERGED)
        return 1'b1;
      return 1'b0;
  endfunction

  // Return whether the given format is the first active one set as MERGED
  function automatic logic is_first_enabled_multi(fp_format_e fmt,
                                                  fmt_unit_types_t types,
                                                  fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++) begin
      if (cfg[i] && types[i] == MERGED) return (fp_format_e'(i) == fmt);
    end
    return 1'b0;
  endfunction

  // Returns the first format that is active and is set as MERGED
  function automatic fp_format_e get_first_enabled_multi(fmt_unit_types_t types, fmt_logic_t cfg);
    for (int unsigned i = 0; i < NUM_FP_FORMATS; i++)
      if (cfg[i] && types[i] == MERGED)
        return fp_format_e'(i);
      return fp_format_e'(0);
  endfunction

endpackage
/// Snitch Configuration.
package snitch_pkg;

  typedef struct packed {
    logic [63:0] BootAddress;
    int unsigned NrCores;
  } SnitchCfg;

  typedef struct packed {
    logic [31:0] addr;
    logic [3:0]  amo;
    logic        write;
    logic [63:0] data;
    logic [7:0]  strb;
  } dreq_t;

  typedef struct packed {
    logic [63:0] data;
    logic        error;
  } dresp_t;

  typedef struct packed {
    logic [31:0]   addr;
    logic [4:0]    id;
    logic [31:0]   data_op;
    logic [63:0]   data_arga;
    logic [63:0]   data_argb;
    logic [63:0]   data_argc;
  } acc_req_t;

  typedef struct packed {
    logic [4:0]    id;
    logic          error;
    logic [63:0]   data;
  } acc_resp_t;

  typedef struct packed {
    logic [31:0] addr;
    logic        write;
    logic [63:0] data;
    logic [7:0]  strb;
  } inst_req_t;

  localparam int NumFPOutstandingLoads = 4;
  localparam int NumIntOutstandingLoads = 1;
  // Number of instructions the sequencer can hold
  localparam int FPUSequencerInstr = 16;
  // SSRs
  localparam logic [31:0] SSR_ADDR_BASE = 32'h20_4800;
  localparam logic [31:0] SSR_ADDR_MASK = 32'hffff_fe00;
  localparam logic [11:0] CSR_SSR = 12'h7C0;
  localparam int SSRNrCredits = 4;
  // Registers which are used as SSRs
  localparam [4:0] FT0 = 5'b0;
  localparam [4:0] FT1 = 5'b1;
  localparam [1:0][4:0] SSRRegs = {FT1, FT0};
  function automatic logic is_ssr(logic [4:0] register);
    unique case (register)
      FT0, FT1: return 1'b1;
      default : return 0;
    endcase
  endfunction

  // FPU
  // Floating-point extensions configuration
  localparam bit RVF = 1'b1; // Is F extension enabled - MUST BE 1 IF D ENABLED!
  localparam bit RVD = 1'b1; // Is D extension enabled

  // Transprecision floating-point extensions configuration
  localparam bit XF16    = 1'b0; // Is half-precision float extension (Xf16) enabled
  localparam bit XF16ALT = 1'b0; // Is alt. half-precision float extension (Xf16alt) enabled
  localparam bit XF8     = 1'b0; // Is quarter-precision float extension (Xf8) enabled
  localparam bit XFVEC   = 1'b1; // Is vectorial float SIMD extension (Xfvec) enabled
  // ------------------
  // FPU Configuration
  // ------------------
  localparam bit FP_PRESENT = RVF | RVD | XF16 | XF16ALT | XF8;

  localparam FLEN = RVD     ? 64 : // D ext.
                    RVF     ? 32 : // F ext.
                    XF16    ? 16 : // Xf16 ext.
                    XF16ALT ? 16 : // Xf16alt ext.
                    XF8     ? 8 :  // Xf8 ext.
                    0;             // Unused in case of no FP

  localparam fpnew_pkg::fpu_features_t FPU_FEATURES = '{
    Width:         fpnew_pkg::maximum(FLEN, 32),
    EnableVectors: XFVEC,
    EnableNanBox:  1'b1,
    FpFmtMask:     {RVF, RVD, XF16, XF8, XF16ALT},
    IntFmtMask:    {XFVEC && XF8, XFVEC && (XF16 || XF16ALT), 1'b1, 1'b0}
  };

  // Latencies of FP ops (number of regs)
  localparam int unsigned LAT_COMP_FP32    = 'd3;
  localparam int unsigned LAT_COMP_FP64    = 'd3;
  localparam int unsigned LAT_COMP_FP16    = 'd2;
  localparam int unsigned LAT_COMP_FP16ALT = 'd2;
  localparam int unsigned LAT_COMP_FP8     = 'd1;
  localparam int unsigned LAT_DIVSQRT      = 'd1;
  localparam int unsigned LAT_NONCOMP      = 'd1;
  localparam int unsigned LAT_CONV         = 'd2;

  localparam fpnew_pkg::fpu_implementation_t FPU_IMPLEMENTATION = '{
    PipeRegs:  '{// FP32, FP64, FP16, FP8, FP16alt
                 '{LAT_COMP_FP32, LAT_COMP_FP64, LAT_COMP_FP16, LAT_COMP_FP8, LAT_COMP_FP16ALT}, // ADDMUL
                 '{default: LAT_DIVSQRT}, // DIVSQRT
                 '{default: LAT_NONCOMP}, // NONCOMP
                 '{default: LAT_CONV}},   // CONV
    UnitTypes: '{'{default: fpnew_pkg::MERGED},
                 // '{fpnew_pkg::PARALLEL, fpnew_pkg::PARALLEL, fpnew_pkg::MERGED, fpnew_pkg::MERGED, fpnew_pkg::MERGED}, // ADDMUL
                 '{default: fpnew_pkg::DISABLED}, // DIVSQRT
                 '{default: fpnew_pkg::PARALLEL}, // NONCOMP
                 '{default: fpnew_pkg::MERGED}},  // CONV
    PipeConfig: fpnew_pkg::BEFORE
    // PipeConfig: fpnew_pkg::DISTRIBUTED
  };

  // Amount of address bit which should be used for accesses from the SoC side.
  // This effectively determines the Address Space of a Snitch Cluster.
  localparam logic [31:0] SoCRequestAddrBits = 32;

  // Address Map
  // TCDM, everything below 0x4000_0000
  localparam logic [31:0] TCDMStartAddress = 32'h0000_0000;
  localparam logic [31:0] TCDMMask         = '1 << 28;

  // Slaves on Cluster AXI Bus
  typedef enum integer {
    TCDM               = 0,
    ClusterPeripherals = 1,
    SoC                = 2
  } cluster_slave_e;

  typedef enum integer {
    CoreReq = 0,
    ICache  = 1,
    AXISoC  = 2
  } cluster_master_e;

  localparam int unsigned NrSlaves = 3;
  localparam int unsigned NrMasters = 3;

  localparam int IdWidth = 2;
  localparam int IdWidthSlave = $clog2(NrMasters) + IdWidth;

  //                                                    3. SoC         2. Cluster Peripherals  3. TCDM
  localparam logic [NrSlaves-1:0][31:0] StartAddress = {32'h8000_0000, 32'h4000_0000,          TCDMStartAddress};
  localparam logic [NrSlaves-1:0][31:0] EndAddress   = {32'hFFFF_FFFF, 32'h5000_0000,          TCDMStartAddress + 32'h1000_0000};
  localparam logic [NrSlaves-1:0]       ValidRule    = {{NrSlaves}{1'b1}};

  // Cluster Peripheral Registers
  typedef enum logic [31:0] {
    TCDMStartAddressReg = 32'h4000_0000,
    TCDMEndAddressReg   = 32'h4000_0008,
    NrCoresReg          = 32'h4000_0010,
    FetchEnableReg      = 32'h4000_0018,
    ScratchReg          = 32'h4000_0020,
    WakeUpReg           = 32'h4000_0028,
    CycleCountReg       = 32'h4000_0030,
    BarrierReg          = 32'h4000_0038,
    TcdmAccessedReg     = 32'h4000_FFF0,
    TcdmCongestedReg    = 32'h4000_FFF8,
    PerfCounterBase     = 32'h4001_0000
  } cluster_peripheral_addr_e;

  // Offload to shared accelerator
  function automatic logic shared_offload (logic [31:0] instr);
    logic offload;
    unique casez (instr)
      riscv_instr::MUL,
      riscv_instr::MULH,
      riscv_instr::MULHSU,
      riscv_instr::MULHU,
      riscv_instr::DIV,
      riscv_instr::DIVU,
      riscv_instr::REM,
      riscv_instr::REMU,
      riscv_instr::MULW,
      riscv_instr::DIVW,
      riscv_instr::DIVUW,
      riscv_instr::REMW,
      riscv_instr::REMUW: offload = 1;
      default: offload = 0;
    endcase
    return offload;
  endfunction

  // Event strobes per core, counted by the performance counters in the cluster
  // peripherals.
  typedef struct packed {
    logic issue_fpu;          // core operations performed in the FPU
    logic issue_fpu_seq;      // includes load/store operations
    logic issue_core_to_fpu;  // instructions issued from core to FPU
    logic retired_insts;      // number of instructions retired by the core
  } core_events_t;

endpackage

// `SNITCH_ENABLE_PERF Enables mcycle, minstret performance counters (read only)

module snitch #(
  parameter logic [31:0] BootAddr  = 32'h0000_1000,
  parameter logic [31:0] MTVEC     = BootAddr, // Exception Base Address (see privileged spec 3.1.7)
  parameter bit          RVE       = 0,   // Reduced-register extension
  parameter bit          RVFD      = 1    // Enable F and D Extension
) (
  input  logic          clk_i,
  input  logic          rst_i,
  input  logic [31:0]   hart_id_i,
  // Instruction Refill Port
  output logic [31:0]   inst_addr_o,
  input  logic [31:0]   inst_data_i,
  output logic          inst_valid_o,
  input  logic          inst_ready_i,
`ifdef RISCV_FORMAL
  output logic [0:0]       rvfi_valid,
  output logic [0:0][63:0] rvfi_order,
  output logic [0:0][31:0] rvfi_insn,
  output logic [0:0]       rvfi_trap,
  output logic [0:0]       rvfi_halt,
  output logic [0:0]       rvfi_intr,
  output logic [0:0][1:0]  rvfi_mode,
  output logic [0:0][4:0]  rvfi_rs1_addr,
  output logic [0:0][4:0]  rvfi_rs2_addr,
  output logic [0:0][31:0] rvfi_rs1_rdata,
  output logic [0:0][31:0] rvfi_rs2_rdata,
  output logic [0:0][4:0]  rvfi_rd_addr,
  output logic [0:0][31:0] rvfi_rd_wdata,
  output logic [0:0][31:0] rvfi_pc_rdata,
  output logic [0:0][31:0] rvfi_pc_wdata,
  output logic [0:0][31:0] rvfi_mem_addr,
  output logic [0:0][3:0]  rvfi_mem_rmask,
  output logic [0:0][3:0]  rvfi_mem_wmask,
  output logic [0:0][31:0] rvfi_mem_rdata,
  output logic [0:0][31:0] rvfi_mem_wdata,
`endif
  /// Accelerator Interface - Master Port
  /// Independent channels for transaction request and read completion.
  /// AXI-like handshaking.
  /// Same IDs need to be handled in-order.
  output logic [31:0]   acc_qaddr_o,
  output logic [4:0]    acc_qid_o,
  output logic [31:0]   acc_qdata_op_o,
  output logic [63:0]   acc_qdata_arga_o,
  output logic [63:0]   acc_qdata_argb_o,
  output logic [63:0]   acc_qdata_argc_o,
  output logic          acc_qvalid_o,
  input  logic          acc_qready_i,
  input  logic [63:0]   acc_pdata_i,
  input  logic [4:0]    acc_pid_i,
  input  logic          acc_perror_i,
  input  logic          acc_pvalid_i,
  output logic          acc_pready_o,
  /// TCDM Data Interface
  /// Write transactions do not return data on the `P Channel`
  /// Transactions need to be handled strictly in-order.
  output logic [31:0]   data_qaddr_o,
  output logic          data_qwrite_o,
  output logic [3:0]    data_qamo_o,
  output logic [63:0]   data_qdata_o,
  output logic [7:0]    data_qstrb_o,
  output logic          data_qvalid_o,
  input  logic          data_qready_i,
  input  logic [63:0]   data_pdata_i,
  input  logic          data_perror_i,
  input  logic          data_pvalid_i,
  output logic          data_pready_o,
  input  logic          wake_up_sync_i, // synchronous wake-up interrupt
  // FPU **un-timed** Side-channel
  output fpnew_pkg::roundmode_e fpu_rnd_mode_o,
  input  fpnew_pkg::status_t    fpu_status_i,
  // Core event strobes
  output snitch_pkg::core_events_t core_events_o
);

  localparam int RegWidth = RVE ? 4 : 5;

  logic illegal_inst;
  logic zero_lsb;

  // Instruction fetch
  logic [31:0] pc_d, pc_q;
  logic wfi_d, wfi_q;
  logic [31:0] consec_pc;
  // Immediates
  logic [31:0] iimm, uimm, jimm, bimm, simm;
  /* verilator lint_off WIDTH */
  assign iimm = $signed({inst_data_i[31:20]});
  assign uimm = {inst_data_i[31:12], 12'b0};
  assign jimm = $signed({inst_data_i[31],
                                  inst_data_i[19:12], inst_data_i[20], inst_data_i[30:21], 1'b0});
  assign bimm = $signed({inst_data_i[31],
                                    inst_data_i[7], inst_data_i[30:25], inst_data_i[11:8], 1'b0});
  assign simm = $signed({inst_data_i[31:25], inst_data_i[11:7]});
  /* verilator lint_on WIDTH */

  logic [31:0] opa, opb;
  logic [32:0] adder_result;
  logic [31:0] alu_result;

  logic [RegWidth-1:0] rd, rs1, rs2;
  logic stall, lsu_stall;
  // Register connections
  logic [1:0][RegWidth-1:0] gpr_raddr;
  logic [1:0][31:0]         gpr_rdata;
  logic [0:0][RegWidth-1:0] gpr_waddr;
  logic [0:0][31:0]         gpr_wdata;
  logic [0:0]               gpr_we;
  logic [2**RegWidth-1:0]   sb_d, sb_q;

  // Load/Store Defines
  logic is_load, is_store, is_signed;

  enum logic [1:0] {
    Byte = 2'b00,
    HalfWord = 2'b01,
    Word = 2'b10
  } ls_size;

  enum logic [3:0] {
    AMONone = 4'h0,
    AMOSwap = 4'h1,
    AMOAdd  = 4'h2,
    AMOAnd  = 4'h3,
    AMOOr   = 4'h4,
    AMOXor  = 4'h5,
    AMOMax  = 4'h6,
    AMOMaxu = 4'h7,
    AMOMin  = 4'h8,
    AMOMinu = 4'h9,
    AMOLR   = 4'hA,
    AMOSC   = 4'hB
  } ls_amo;

  logic [63:0] ld_result;
  logic lsu_qready, lsu_qvalid;
  logic lsu_pvalid, lsu_pready;
  logic [RegWidth-1:0] lsu_rd;

  logic retire_load; // retire a load instruction
  logic retire_i; // retire the rest of the base instruction set
  logic retire_acc; // retire an instruction we offloaded

  logic acc_stall;
  logic valid_instr;

  // ALU Operations
  enum logic [3:0]  {
    Add, Sub,
    Slt, Sltu,
    Sll, Srl, Sra,
    LXor, LOr, LAnd, LNAnd,
    Eq, Neq, Ge, Geu,
    BypassA
  } alu_op;

  enum logic [3:0] {
    None, Reg, IImmediate, UImmediate, JImmediate, SImmediate, SFImmediate, PC, CSR, CSRImmmediate
  } opa_select, opb_select;

  logic write_rd; // write desitnation this cycle
  logic uses_rd;
  enum logic [1:0] {Consec, Alu, Exception} next_pc;

  enum logic [1:0] {RdAlu, RdConsecPC, RdBypass} rd_select;
  logic [31:0] rd_bypass;

  logic is_branch;

  logic [31:0] csr_rvalue;
  logic csr_en;

  typedef struct packed {
    fpnew_pkg::roundmode_e frm;
    fpnew_pkg::status_t    fflags;
  } fcsr_t;
  fcsr_t fcsr_d, fcsr_q;

  assign fpu_rnd_mode_o = fcsr_q.frm;

  // Registers
  `FFSR(pc_q, pc_d, BootAddr, clk_i, rst_i)
  `FFSR(wfi_q, wfi_d, '0, clk_i, rst_i)
  `FFSR(sb_q, sb_d, '0, clk_i, rst_i)
  `FFSR(fcsr_q, fcsr_d, '0, clk_i, rst_i)

  // performance counter
  `ifdef SNITCH_ENABLE_PERF
  logic [63:0] cycle_q;
  logic [63:0] instret_q;
  `FFSR(cycle_q, cycle_q + 1, '0, clk_i, rst_i);
  `FFLSR(instret_q, instret_q + 1, !stall, '0, clk_i, rst_i);
  `endif

  always_comb begin
    core_events_o = '0;
    core_events_o.retired_insts = ~stall;
  end

  // accelerator offloading interface
  // register int destination in scoreboard
  logic  acc_register_rd;

  assign acc_qaddr_o = hart_id_i;
  assign acc_qid_o = rd;
  assign acc_qdata_op_o = inst_data_i;
  assign acc_qdata_arga_o = {{32{gpr_rdata[0][31]}}, gpr_rdata[0]};
  assign acc_qdata_argb_o = {{32{gpr_rdata[1][31]}}, gpr_rdata[1]};
  assign acc_qdata_argc_o = {32'b0, alu_result};

  // instruction fetch interface
  assign inst_addr_o = pc_q;
  assign inst_valid_o = ~wfi_q;

  // --------------------
  // Control
  // --------------------
  // Scoreboard: Keep track of rd dependencies (only loads at the moment)
  logic operands_ready;
  logic dst_ready;
  logic opa_ready, opb_ready;

  always_comb begin
    sb_d = sb_q;
    if (retire_load) sb_d[lsu_rd] = 1'b0;
    // only place the reservation if we actually executed the load or offload instruction
    if ((is_load | acc_register_rd) && !stall) sb_d[rd] = 1'b1;
    if (retire_acc) sb_d[acc_pid_i[RegWidth-1:0]] = 1'b0;
    sb_d[0] = 1'b0;
  end
  // TODO(zarubaf): This can probably be described a bit more efficient
  assign opa_ready = (opa_select != Reg) | ~sb_q[rs1];
  assign opb_ready = (opb_select != Reg & opb_select != SImmediate) | ~sb_q[rs2];
  assign operands_ready = opa_ready & opb_ready;
  assign dst_ready = uses_rd & ~sb_q[rd];

  assign valid_instr = (inst_ready_i & inst_valid_o) & operands_ready & dst_ready;
  // the accelerator interface stalled us
  assign acc_stall = (acc_qvalid_o & ~acc_qready_i);
  // the LSU Interface didn't accept our request yet
  assign lsu_stall = (lsu_qvalid & ~lsu_qready);
  // Stall the stage if we either didn't get a valid instruction or the LSU/Accelerator is not ready
  assign stall = ~valid_instr | lsu_stall | acc_stall;

  // --------------------
  // Instruction Frontend
  // --------------------
  assign consec_pc = pc_q + ((is_branch & alu_result[0]) ? bimm : 'd4);

  always_comb begin
    pc_d = pc_q;
    // if we got a valid instruction word increment the PC unless we are waiting for an event
    if (!stall && !wfi_q) begin
      casez (next_pc)
        Consec: pc_d = consec_pc;
        Alu: pc_d = alu_result & {{31{1'b1}}, ~zero_lsb};
        Exception: pc_d = MTVEC;
      endcase
    end
  end

  // --------------------
  // Decoder
  // --------------------
  assign rd = inst_data_i[7 + RegWidth - 1:7];
  assign rs1 = inst_data_i[15 + RegWidth - 1:15];
  assign rs2 = inst_data_i[20 + RegWidth - 1:20];

  always_comb begin
    illegal_inst = 1'b0;
    alu_op = Add;
    opa_select = None;
    opb_select = None;

    next_pc = Consec;

    rd_select = RdAlu;
    write_rd = 1'b1;
    // if we are writing the field this cycle we need
    // an int destination register
    uses_rd = write_rd;

    rd_bypass = '0;
    zero_lsb = 1'b0;
    is_branch = 1'b0;
    // LSU interface
    is_load = 1'b0;
    is_store = 1'b0;
    is_signed = 1'b0;
    ls_size = Byte;
    ls_amo = AMONone;

    acc_qvalid_o = 1'b0;
    acc_register_rd = 1'b0;

    csr_en = 1'b0;
    wfi_d = (wake_up_sync_i) ? 1'b0 : wfi_q;

    unique casez (inst_data_i)
      riscv_instr::ADD: begin
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::ADDI: begin
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SUB: begin
        alu_op = Sub;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::XOR: begin
        opa_select = Reg;
        opb_select = Reg;
        alu_op = LXor;
      end
      riscv_instr::XORI: begin
        alu_op = LXor;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::OR: begin
        opa_select = Reg;
        opb_select = Reg;
        alu_op = LOr;
      end
      riscv_instr::ORI: begin
        alu_op = LOr;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::AND: begin
        alu_op = LAnd;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::ANDI: begin
        alu_op = LAnd;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SLT: begin
        alu_op = Slt;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SLTI: begin
        alu_op = Slt;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SLTU: begin
        alu_op = Sltu;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SLTIU: begin
        alu_op = Sltu;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SLL: begin
        alu_op = Sll;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SRL: begin
        alu_op = Srl;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SRA: begin
        alu_op = Sra;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SLLI: begin
        alu_op = Sll;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SRLI: begin
        alu_op = Srl;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::SRAI: begin
        alu_op = Sra;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LUI: begin
        opa_select = None;
        opb_select = None;
        rd_select = RdBypass;
        rd_bypass = uimm;
      end
      riscv_instr::AUIPC: begin
        opa_select = UImmediate;
        opb_select = PC;
      end
      riscv_instr::JAL: begin
        rd_select = RdConsecPC;
        opa_select = JImmediate;
        opb_select = PC;
        next_pc = Alu;
      end
      riscv_instr::JALR: begin
        rd_select = RdConsecPC;
        opa_select = Reg;
        opb_select = IImmediate;
        next_pc = Alu;
        zero_lsb = 1'b1;
      end
      // use the ALU for comparisons
      riscv_instr::BEQ: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Eq;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BNE: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Neq;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BLT: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Slt;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BLTU: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Sltu;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BGE: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Ge;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::BGEU: begin
        is_branch = 1'b1;
        write_rd = 1'b0;
        alu_op = Geu;
        opa_select = Reg;
        opb_select = Reg;
      end
      // Load/Stores
      riscv_instr::SB: begin
        write_rd = 1'b0;
        is_store = 1'b1;
        opa_select = Reg;
        opb_select = SImmediate;
      end
      riscv_instr::SH: begin
        write_rd = 1'b0;
        is_store = 1'b1;
        ls_size = HalfWord;
        opa_select = Reg;
        opb_select = SImmediate;
      end
      riscv_instr::SW: begin
        write_rd = 1'b0;
        is_store = 1'b1;
        ls_size = Word;
        opa_select = Reg;
        opb_select = SImmediate;
      end
      riscv_instr::LB: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LH: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = HalfWord;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LW: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LBU: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      riscv_instr::LHU: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        ls_size = HalfWord;
        opa_select = Reg;
        opb_select = IImmediate;
      end
      // CSR Instructions
      riscv_instr::CSRRW: begin // Atomic Read/Write CSR
        opa_select = Reg;
        opb_select = None;
        rd_select = RdBypass;
        rd_bypass = csr_rvalue;
        csr_en = 1'b1;
      end
      riscv_instr::CSRRWI: begin
        opa_select = CSRImmmediate;
        opb_select = None;
        rd_select = RdBypass;
        rd_bypass = csr_rvalue;
        csr_en = 1'b1;
      end
      riscv_instr::CSRRS: begin  // Atomic Read and Set Bits in CSR
          alu_op = LOr;
          opa_select = Reg;
          opb_select = CSR;
          rd_select = RdBypass;
          rd_bypass = csr_rvalue;
          csr_en = 1'b1;
      end
      riscv_instr::CSRRSI: begin
        // offload CSR enable to FP SS
        if (inst_data_i[31:20] != snitch_pkg::CSR_SSR) begin
          alu_op = LOr;
          opa_select = CSRImmmediate;
          opb_select = CSR;
          rd_select = RdBypass;
          rd_bypass = csr_rvalue;
          csr_en = 1'b1;
        end else begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end
      end
      riscv_instr::CSRRC: begin // Atomic Read and Clear Bits in CSR
        alu_op = LNAnd;
        opa_select = Reg;
        opb_select = CSR;
        rd_select = RdBypass;
        rd_bypass = csr_rvalue;
        csr_en = 1'b1;
      end
      riscv_instr::CSRRCI: begin
        if (inst_data_i[31:20] != snitch_pkg::CSR_SSR) begin
          alu_op = LNAnd;
          opa_select = CSRImmmediate;
          opb_select = CSR;
          rd_select = RdBypass;
          rd_bypass = csr_rvalue;
          csr_en = 1'b1;
        end else begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end
      end
      riscv_instr::ECALL,
      riscv_instr::EBREAK: begin
        // TODO(zarubaf): Trap to precise address
        write_rd = 1'b0;
      end
      // NOP Instructions
      riscv_instr::FENCE: begin
        write_rd = 1'b0;
      end
      riscv_instr::WFI: begin
        wfi_d = 1'b1;
      end
      // Atomics
      riscv_instr::AMOADD_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOAdd;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOXOR_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOXor;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOOR_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOOr;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOAND_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOAnd;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOMIN_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMinu;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOMAX_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMax;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOMINU_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMinu;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOMAXU_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOMaxu;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::AMOSWAP_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOSwap;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::LR_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOLR;
        opa_select = Reg;
        opb_select = Reg;
      end
      riscv_instr::SC_W: begin
        alu_op = BypassA;
        write_rd = 1'b0;
        uses_rd = 1'b1;
        is_load = 1'b1;
        is_signed = 1'b1;
        ls_size = Word;
        ls_amo = AMOSC;
        opa_select = Reg;
        opb_select = Reg;
      end
      // Off-load to shared multiplier
      riscv_instr::MUL,
      riscv_instr::MULH,
      riscv_instr::MULHSU,
      riscv_instr::MULHU,
      riscv_instr::DIV,
      riscv_instr::DIVU,
      riscv_instr::REM,
      riscv_instr::REMU,
      riscv_instr::MULW,
      riscv_instr::DIVW,
      riscv_instr::DIVUW,
      riscv_instr::REMW,
      riscv_instr::REMUW: begin
        write_rd = 1'b0;
        uses_rd = 1'b1;
        acc_qvalid_o = valid_instr;
        opa_select = Reg;
        opb_select = Reg;
        acc_register_rd = 1'b1;
      end
      // Offload FP-FP Instructions - fire and forget
      // TODO (smach): Check legal rounding modes and issue illegal isn if needed
      // Single Precision Floating-Point
      riscv_instr::FADD_S,
      riscv_instr::FSUB_S,
      riscv_instr::FMUL_S,
      riscv_instr::FDIV_S,
      riscv_instr::FSGNJ_S,
      riscv_instr::FSGNJN_S,
      riscv_instr::FSGNJX_S,
      riscv_instr::FMIN_S,
      riscv_instr::FMAX_S,
      riscv_instr::FSQRT_S,
      riscv_instr::FMADD_S,
      riscv_instr::FMSUB_S,
      riscv_instr::FNMSUB_S,
      riscv_instr::FNMADD_S: begin
        if (snitch_pkg::RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFADD_S,
      riscv_instr::VFADD_R_S,
      riscv_instr::VFSUB_S,
      riscv_instr::VFSUB_R_S,
      riscv_instr::VFMUL_S,
      riscv_instr::VFMUL_R_S,
      riscv_instr::VFDIV_S,
      riscv_instr::VFDIV_R_S,
      riscv_instr::VFMIN_S,
      riscv_instr::VFMIN_R_S,
      riscv_instr::VFMAX_S,
      riscv_instr::VFMAX_R_S,
      riscv_instr::VFSQRT_S,
      riscv_instr::VFMAC_S,
      riscv_instr::VFMAC_R_S,
      riscv_instr::VFMRE_S,
      riscv_instr::VFMRE_R_S,
      riscv_instr::VFSGNJ_S,
      riscv_instr::VFSGNJ_R_S,
      riscv_instr::VFSGNJN_S,
      riscv_instr::VFSGNJN_R_S,
      riscv_instr::VFSGNJX_S,
      riscv_instr::VFSGNJX_R_S,
      riscv_instr::VFCPKA_S_S,
      riscv_instr::VFCPKA_S_D: begin
        if (snitch_pkg::XFVEC && snitch_pkg::RVF && snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Double Precision Floating-Point
      riscv_instr::FADD_D,
      riscv_instr::FSUB_D,
      riscv_instr::FMUL_D,
      riscv_instr::FDIV_D,
      riscv_instr::FSGNJ_D,
      riscv_instr::FSGNJN_D,
      riscv_instr::FSGNJX_D,
      riscv_instr::FMIN_D,
      riscv_instr::FMAX_D,
      riscv_instr::FSQRT_D,
      riscv_instr::FMADD_D,
      riscv_instr::FMSUB_D,
      riscv_instr::FNMSUB_D,
      riscv_instr::FNMADD_D: begin
        if (snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_S_D,
      riscv_instr::FCVT_D_S: begin
        if (snitch_pkg::RVF && snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // [Alt] Half Precision Floating-Point
      riscv_instr::FADD_H,
      riscv_instr::FSUB_H,
      riscv_instr::FMUL_H,
      riscv_instr::FDIV_H,
      riscv_instr::FSQRT_H,
      riscv_instr::FMADD_H,
      riscv_instr::FMSUB_H,
      riscv_instr::FNMSUB_H,
      riscv_instr::FNMADD_H: begin
        if ((snitch_pkg::XF16 && inst_data_i[14:12] inside {[3'b000:3'b100], 3'b111}) ||
            (snitch_pkg::XF16ALT && inst_data_i[14:12] == 3'b101)) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Half Precision Floating-Point
      riscv_instr::FSGNJ_H,
      riscv_instr::FSGNJN_H,
      riscv_instr::FSGNJX_H,
      riscv_instr::FMIN_H,
      riscv_instr::FMAX_H: begin
        if (snitch_pkg::XF16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_S_H,
      riscv_instr::FCVT_H_S: begin
        if (snitch_pkg::RVF) begin
          if ((snitch_pkg::XF16 && inst_data_i[14:12] inside {[3'b000:3'b100], 3'b111}) ||
              (snitch_pkg::XF16ALT && inst_data_i[14:12] == 3'b101)) begin
            write_rd = 1'b0;
            acc_qvalid_o = valid_instr;
          end else begin
            illegal_inst = 1'b1;
          end
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_D_H,
      riscv_instr::FCVT_H_D: begin
        if (snitch_pkg::RVD) begin
          if ((snitch_pkg::XF16 && inst_data_i[14:12] inside {[3'b000:3'b100], 3'b111}) ||
              (snitch_pkg::XF16ALT && inst_data_i[14:12] == 3'b101)) begin
            write_rd = 1'b0;
            acc_qvalid_o = valid_instr;
          end else begin
            illegal_inst = 1'b1;
          end
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFADD_H,
      riscv_instr::VFADD_R_H,
      riscv_instr::VFSUB_H,
      riscv_instr::VFSUB_R_H,
      riscv_instr::VFMUL_H,
      riscv_instr::VFMUL_R_H,
      riscv_instr::VFDIV_H,
      riscv_instr::VFDIV_R_H,
      riscv_instr::VFMIN_H,
      riscv_instr::VFMIN_R_H,
      riscv_instr::VFMAX_H,
      riscv_instr::VFMAX_R_H,
      riscv_instr::VFSQRT_H,
      riscv_instr::VFMAC_H,
      riscv_instr::VFMAC_R_H,
      riscv_instr::VFMRE_H,
      riscv_instr::VFMRE_R_H,
      riscv_instr::VFSGNJ_H,
      riscv_instr::VFSGNJ_R_H,
      riscv_instr::VFSGNJN_H,
      riscv_instr::VFSGNJN_R_H,
      riscv_instr::VFSGNJX_H,
      riscv_instr::VFSGNJX_R_H,
      riscv_instr::VFCPKA_H_S: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16 && snitch_pkg::RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCVT_S_H,
      riscv_instr::VFCVTU_S_H,
      riscv_instr::VFCVT_H_S,
      riscv_instr::VFCVTU_H_S,
      riscv_instr::VFCPKB_H_S,
      riscv_instr::VFCPKA_H_D,
      riscv_instr::VFCPKB_H_D: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16 && snitch_pkg::RVF && snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Alternate Half Precision Floating-Point
      riscv_instr::FSGNJ_AH,
      riscv_instr::FSGNJN_AH,
      riscv_instr::FSGNJX_AH,
      riscv_instr::FMIN_AH,
      riscv_instr::FMAX_AH: begin
        if (snitch_pkg::XF16ALT) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_S_AH: begin
        if (snitch_pkg::RVF && snitch_pkg::XF16ALT) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_D_AH: begin
        if (snitch_pkg::RVD && snitch_pkg::XF16ALT) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_H_AH,
      riscv_instr::FCVT_AH_H: begin
        if (snitch_pkg::XF16 && snitch_pkg::XF16ALT) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFADD_AH,
      riscv_instr::VFADD_R_AH,
      riscv_instr::VFSUB_AH,
      riscv_instr::VFSUB_R_AH,
      riscv_instr::VFMUL_AH,
      riscv_instr::VFMUL_R_AH,
      riscv_instr::VFDIV_AH,
      riscv_instr::VFDIV_R_AH,
      riscv_instr::VFMIN_AH,
      riscv_instr::VFMIN_R_AH,
      riscv_instr::VFMAX_AH,
      riscv_instr::VFMAX_R_AH,
      riscv_instr::VFSQRT_AH,
      riscv_instr::VFMAC_AH,
      riscv_instr::VFMAC_R_AH,
      riscv_instr::VFMRE_AH,
      riscv_instr::VFMRE_R_AH,
      riscv_instr::VFSGNJ_AH,
      riscv_instr::VFSGNJ_R_AH,
      riscv_instr::VFSGNJN_AH,
      riscv_instr::VFSGNJN_R_AH,
      riscv_instr::VFSGNJX_AH,
      riscv_instr::VFSGNJX_R_AH,
      riscv_instr::VFCPKA_AH_S: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16ALT && snitch_pkg::RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCVT_S_AH,
      riscv_instr::VFCVTU_S_AH,
      riscv_instr::VFCVT_AH_S,
      riscv_instr::VFCVTU_AH_S,
      riscv_instr::VFCPKB_AH_S,
      riscv_instr::VFCPKA_AH_D,
      riscv_instr::VFCPKB_AH_D: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16ALT && snitch_pkg::RVF && snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCVT_H_AH,
      riscv_instr::VFCVTU_H_AH,
      riscv_instr::VFCVT_AH_H,
      riscv_instr::VFCVTU_AH_H: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16ALT && snitch_pkg::XF16 && snitch_pkg::RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Quarter Precision Floating-Point
      riscv_instr::FADD_B,
      riscv_instr::FSUB_B,
      riscv_instr::FMUL_B,
      riscv_instr::FDIV_B,
      riscv_instr::FSGNJ_B,
      riscv_instr::FSGNJN_B,
      riscv_instr::FSGNJX_B,
      riscv_instr::FMIN_B,
      riscv_instr::FMAX_B,
      riscv_instr::FSQRT_B,
      riscv_instr::FMADD_B,
      riscv_instr::FMSUB_B,
      riscv_instr::FNMSUB_B,
      riscv_instr::FNMADD_B: begin
        if (snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_S_B,
      riscv_instr::FCVT_B_S: begin
        if (snitch_pkg::RVF && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_D_B,
      riscv_instr::FCVT_B_D: begin
        if (snitch_pkg::RVD && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_H_B,
      riscv_instr::FCVT_B_H: begin
        if (snitch_pkg::XF16 && snitch_pkg::XF8) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FCVT_AH_B,
      riscv_instr::FCVT_B_AH: begin
        if (snitch_pkg::RVF && snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFADD_B,
      riscv_instr::VFADD_R_B,
      riscv_instr::VFSUB_B,
      riscv_instr::VFSUB_R_B,
      riscv_instr::VFMUL_B,
      riscv_instr::VFMUL_R_B,
      riscv_instr::VFDIV_B,
      riscv_instr::VFDIV_R_B,
      riscv_instr::VFMIN_B,
      riscv_instr::VFMIN_R_B,
      riscv_instr::VFMAX_B,
      riscv_instr::VFMAX_R_B,
      riscv_instr::VFSQRT_B,
      riscv_instr::VFMAC_B,
      riscv_instr::VFMAC_R_B,
      riscv_instr::VFMRE_B,
      riscv_instr::VFMRE_R_B,
      riscv_instr::VFSGNJ_B,
      riscv_instr::VFSGNJ_R_B,
      riscv_instr::VFSGNJN_B,
      riscv_instr::VFSGNJN_R_B,
      riscv_instr::VFSGNJX_B,
      riscv_instr::VFSGNJX_R_B: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF8 && snitch_pkg::FLEN >= 16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCPKA_B_S,
      riscv_instr::VFCPKB_B_S: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF8 && snitch_pkg::RVF) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCVT_S_B,
      riscv_instr::VFCVTU_S_B,
      riscv_instr::VFCVT_B_S,
      riscv_instr::VFCVTU_B_S: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF8 && snitch_pkg::RVF && snitch_pkg::FLEN >= 64) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCPKC_B_S,
      riscv_instr::VFCPKD_B_S,
      riscv_instr::VFCPKA_B_D,
      riscv_instr::VFCPKB_B_D,
      riscv_instr::VFCPKC_B_D,
      riscv_instr::VFCPKD_B_D: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF8 && snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCVT_H_B,
      riscv_instr::VFCVTU_H_B,
      riscv_instr::VFCVT_B_H,
      riscv_instr::VFCVTU_B_H: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF8 && snitch_pkg::XF16 && snitch_pkg::FLEN >= 32) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFCVT_AH_B,
      riscv_instr::VFCVTU_AH_B,
      riscv_instr::VFCVT_B_AH,
      riscv_instr::VFCVTU_B_AH: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF8 && snitch_pkg::XF16ALT && snitch_pkg::FLEN >= 32) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Offload FP-Int Instructions - fire and forget
      // Single Precision Floating-Point
      riscv_instr::FLE_S,
      riscv_instr::FLT_S,
      riscv_instr::FEQ_S,
      riscv_instr::FCLASS_S,
      riscv_instr::FCVT_W_S,
      riscv_instr::FCVT_WU_S,
      riscv_instr::FMV_X_W: begin
        if (snitch_pkg::RVF) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFEQ_S,
      riscv_instr::VFEQ_R_S,
      riscv_instr::VFNE_S,
      riscv_instr::VFNE_R_S,
      riscv_instr::VFLT_S,
      riscv_instr::VFLT_R_S,
      riscv_instr::VFGE_S,
      riscv_instr::VFGE_R_S,
      riscv_instr::VFLE_S,
      riscv_instr::VFLE_R_S,
      riscv_instr::VFGT_S,
      riscv_instr::VFGT_R_S,
      riscv_instr::VFCLASS_S: begin
        if (snitch_pkg::XFVEC && snitch_pkg::RVF && snitch_pkg::FLEN >= 64) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Double Precision Floating-Point
      riscv_instr::FLE_D,
      riscv_instr::FLT_D,
      riscv_instr::FEQ_D,
      riscv_instr::FCLASS_D,
      riscv_instr::FCVT_W_D,
      riscv_instr::FCVT_WU_D: begin
        if (snitch_pkg::RVD) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Half Precision Floating-Point
      riscv_instr::FLE_H,
      riscv_instr::FLT_H,
      riscv_instr::FEQ_H,
      riscv_instr::FCLASS_H,
      riscv_instr::FCVT_W_H,
      riscv_instr::FCVT_WU_H,
      riscv_instr::FMV_X_H: begin
        if ((snitch_pkg::XF16 && inst_data_i[14:12] inside {[3'b000:3'b100], 3'b111}) ||
              (snitch_pkg::XF16ALT && inst_data_i[14:12] == 3'b101)) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFEQ_H,
      riscv_instr::VFEQ_R_H,
      riscv_instr::VFNE_H,
      riscv_instr::VFNE_R_H,
      riscv_instr::VFLT_H,
      riscv_instr::VFLT_R_H,
      riscv_instr::VFGE_H,
      riscv_instr::VFGE_R_H,
      riscv_instr::VFLE_H,
      riscv_instr::VFLE_R_H,
      riscv_instr::VFGT_H,
      riscv_instr::VFGT_R_H,
      riscv_instr::VFCLASS_H: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16 && snitch_pkg::FLEN >= 32) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFMV_X_H,
      riscv_instr::VFCVT_X_H,
      riscv_instr::VFCVT_XU_H: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16 && snitch_pkg::FLEN >= 32 && ~snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Alternate Half Precision Floating-Point
      riscv_instr::FLE_AH,
      riscv_instr::FLT_AH,
      riscv_instr::FEQ_AH,
      riscv_instr::FCLASS_AH,
      riscv_instr::FMV_X_AH: begin
        if (snitch_pkg::XF16ALT) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFEQ_AH,
      riscv_instr::VFEQ_R_AH,
      riscv_instr::VFNE_AH,
      riscv_instr::VFNE_R_AH,
      riscv_instr::VFLT_AH,
      riscv_instr::VFLT_R_AH,
      riscv_instr::VFGE_AH,
      riscv_instr::VFGE_R_AH,
      riscv_instr::VFLE_AH,
      riscv_instr::VFLE_R_AH,
      riscv_instr::VFGT_AH,
      riscv_instr::VFGT_R_AH,
      riscv_instr::VFCLASS_AH: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16ALT && snitch_pkg::FLEN >= 32) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFMV_X_AH,
      riscv_instr::VFCVT_X_AH,
      riscv_instr::VFCVT_XU_AH: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16ALT && snitch_pkg::FLEN >= 32 && ~snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Quarter Precision Floating-Point
      riscv_instr::FLE_B,
      riscv_instr::FLT_B,
      riscv_instr::FEQ_B,
      riscv_instr::FCLASS_B,
      riscv_instr::FCVT_W_B,
      riscv_instr::FCVT_WU_B,
      riscv_instr::FMV_X_B: begin
        if (snitch_pkg::XF8) begin
          write_rd = 1'b0;
          uses_rd = 1'b1;
          acc_qvalid_o = valid_instr;
          acc_register_rd = 1'b1; // No RS in GPR but RD in GPR, register in int scoreboard
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFEQ_B,
      riscv_instr::VFEQ_R_B,
      riscv_instr::VFNE_B,
      riscv_instr::VFNE_R_B,
      riscv_instr::VFLT_B,
      riscv_instr::VFLT_R_B,
      riscv_instr::VFGE_B,
      riscv_instr::VFGE_R_B,
      riscv_instr::VFLE_B,
      riscv_instr::VFLE_R_B,
      riscv_instr::VFGT_B,
      riscv_instr::VFGT_R_B: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF8 && snitch_pkg::FLEN >= 16) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::VFMV_X_B,
      riscv_instr::VFCLASS_B,
      riscv_instr::VFCVT_X_B,
      riscv_instr::VFCVT_XU_B: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF8 && snitch_pkg::FLEN >= 16 && ~snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Offload Int-FP Instructions - fire and forget
      // Single Precision Floating-Point
      riscv_instr::FMV_W_X,
      riscv_instr::FCVT_S_W,
      riscv_instr::FCVT_S_WU: begin
        if (snitch_pkg::RVF) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Double Precision Floating-Point
      riscv_instr::FCVT_D_W,
      riscv_instr::FCVT_D_WU: begin
        if (snitch_pkg::RVD) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Half Precision Floating-Point
      riscv_instr::FMV_H_X,
      riscv_instr::FCVT_H_W,
      riscv_instr::FCVT_H_WU: begin
        if (snitch_pkg::XF16) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFMV_H_X,
      riscv_instr::VFCVT_H_X,
      riscv_instr::VFCVT_H_XU: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16 && snitch_pkg::FLEN >= 32 && ~snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Alternate Half Precision Floating-Point
      riscv_instr::FMV_AH_X: begin
        if (snitch_pkg::XF16ALT) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFMV_AH_X,
      riscv_instr::VFCVT_AH_X,
      riscv_instr::VFCVT_AH_XU: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF16ALT && snitch_pkg::FLEN >= 32 && ~snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Quarter Precision Floating-Point
      riscv_instr::FMV_B_X,
      riscv_instr::FCVT_B_W,
      riscv_instr::FCVT_B_WU: begin
        if (snitch_pkg::XF8) begin
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Vectors
      riscv_instr::VFMV_B_X,
      riscv_instr::VFCVT_B_X,
      riscv_instr::VFCVT_B_XU: begin
        if (snitch_pkg::XFVEC && snitch_pkg::XF8 && snitch_pkg::FLEN >= 16 && ~snitch_pkg::RVD) begin
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // FP Sequencer
      riscv_instr::FREP: begin
        if (snitch_pkg::FP_PRESENT)
          opa_select = Reg;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
      end
      // Floating-Point Load/Store
      // Single Precision Floating-Point
      riscv_instr::FLW: begin
        if (snitch_pkg::RVF) begin
          opa_select = Reg;
          opb_select = IImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FSW: begin
        if (snitch_pkg::RVF) begin
          opa_select = Reg;
          opb_select = SFImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Double Precision Floating-Point
      riscv_instr::FLD: begin
        if (snitch_pkg::RVD || snitch_pkg::XFVEC) begin
          opa_select = Reg;
          opb_select = IImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FSD: begin
        if (snitch_pkg::RVD || snitch_pkg::XFVEC) begin
          opa_select = Reg;
          opb_select = SFImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Half Precision Floating-Point
      riscv_instr::FLH: begin
        if (snitch_pkg::XF16 || snitch_pkg::XF16ALT) begin
          opa_select = Reg;
          opb_select = IImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FSH: begin
        if (snitch_pkg::XF16 || snitch_pkg::XF16ALT) begin
          opa_select = Reg;
          opb_select = SFImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Quarter Precision Floating-Point
      riscv_instr::FLB: begin
        if (snitch_pkg::XF8) begin
          opa_select = Reg;
          opb_select = IImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      riscv_instr::FSB: begin
        if (snitch_pkg::XF8) begin
          opa_select = Reg;
          opb_select = SFImmediate;
          write_rd = 1'b0;
          acc_qvalid_o = valid_instr;
        end else begin
          illegal_inst = 1'b1;
        end
      end
      // Offload Multiply Instructions
      // TODO(zarubaf): Illegal Instructions
      default: begin
        illegal_inst = 1'b1;
      end
    endcase

    // Sanitize illegal instructions
    if (illegal_inst) begin
     write_rd = 1'b0;
     uses_rd = 1'b0;
     next_pc = Exception;
    end
  end

  // CSR logic
  always_comb begin
    csr_rvalue = '0;
    // registers
    fcsr_d = fcsr_q;
    fcsr_d.fflags = fcsr_q.fflags | fpu_status_i;

    // TODO(zarubaf): Needs some more input handling, like illegal instruction exceptions.
    // Right now we skip this due to simplicity.
    if (csr_en) begin
      unique case (inst_data_i[31:20])
        riscv_instr::CSR_MHARTID: begin
          csr_rvalue = hart_id_i;
        end
        `ifdef SNITCH_ENABLE_PERF
        riscv_instr::CSR_MCYCLE: begin
          csr_rvalue = cycle_q[31:0];
        end
        riscv_instr::CSR_MINSTRET: begin
          csr_rvalue = instret_q[31:0];
        end
        riscv_instr::CSR_MCYCLEH: begin
          csr_rvalue = cycle_q[63:32];
        end
        riscv_instr::CSR_MINSTRETH: begin
          csr_rvalue = instret_q[63:32];
        end
        `endif
        riscv_instr::CSR_FFLAGS: begin
          csr_rvalue = {27'b0, fcsr_q.fflags};
          fcsr_d.fflags = fpnew_pkg::status_t'(alu_result[4:0]);
        end
        riscv_instr::CSR_FRM: begin
          csr_rvalue = {29'b0, fcsr_q.frm};
          fcsr_d.frm = fpnew_pkg::roundmode_e'(alu_result[2:0]);
        end
        riscv_instr::CSR_FCSR: begin
          csr_rvalue = {24'b0, fcsr_q};
          fcsr_d = fcsr_t'(alu_result[7:0]);
        end
        default: csr_rvalue = '0;
      endcase
    end
  end

  snitch_regfile #(
    .DATA_WIDTH     ( 32       ),
    .NR_READ_PORTS  ( 2        ),
    .NR_WRITE_PORTS ( 1        ),
    .ZERO_REG_ZERO  ( 1        ),
    .ADDR_WIDTH     ( RegWidth )
  ) i_snitch_regfile (
    .clk_i,
    .raddr_i   ( gpr_raddr ),
    .rdata_o   ( gpr_rdata ),
    .waddr_i   ( gpr_waddr ),
    .wdata_i   ( gpr_wdata ),
    .we_i      ( gpr_we    )
  );

  // --------------------
  // Operand Select
  // --------------------
  always_comb begin
    unique case (opa_select)
      None: opa = '0;
      Reg: opa = gpr_rdata[0];
      UImmediate: opa = uimm;
      JImmediate: opa = jimm;
      CSRImmmediate: opa = {{{32-RegWidth}{1'b0}}, rs1};
      default: opa = '0;
    endcase
  end

  always_comb begin
    unique case (opb_select)
      None: opb = '0;
      Reg: opb = gpr_rdata[1];
      IImmediate: opb = iimm;
      SFImmediate, SImmediate: opb = simm;
      PC: opb = pc_q;
      CSR: opb = csr_rvalue;
      default: opb = '0;
    endcase
  end

  assign gpr_raddr[0] = rs1;
  assign gpr_raddr[1] = rs2;

  // --------------------
  // ALU
  // --------------------
  // Main Shifter
  logic [31:0] shift_opa, shift_opa_reversed;
  logic [31:0] shift_right_result, shift_left_result;
  logic [32:0] shift_opa_ext, shift_right_result_ext;
  logic shift_left, shift_arithmetic; // shift control
  for (genvar i = 0; i < 32; i++) begin : gen_reverse_opa
    assign shift_opa_reversed[i] = opa[31-i];
    assign shift_left_result[i] = shift_right_result[31-i];
  end
  assign shift_opa = shift_left ? shift_opa_reversed : opa;
  assign shift_opa_ext = {shift_opa[31] & shift_arithmetic, shift_opa};
  assign shift_right_result_ext = $unsigned($signed(shift_opa_ext) >>> opb[4:0]);
  assign shift_right_result = shift_right_result_ext[31:0];

  // Main Adder
  logic [32:0] alu_opa, alu_opb;
  assign adder_result = alu_opa + alu_opb;

  // ALU
  /* verilator lint_off WIDTH */
  always_comb begin
    alu_opa = $signed(opa);
    alu_opb = $signed(opb);

    alu_result = adder_result[31:0];
    shift_left = 1'b0;
    shift_arithmetic = 1'b0;

    unique case (alu_op)
      Sub: alu_opb = -$signed(opb);
      Slt: begin
        alu_opb = -$signed(opb);
        alu_result = {30'b0, adder_result[32]};
      end
      Ge: begin
        alu_opb = -$signed(opb);
        alu_result = {30'b0, ~adder_result[32]};
      end
      Sltu: begin
        alu_opa = $unsigned(opa);
        alu_opb = -$unsigned(opb);
        alu_result = {30'b0, adder_result[32]};
      end
      Geu: begin
        alu_opa = $unsigned(opa);
        alu_opb = -$unsigned(opb);
        alu_result = {30'b0, ~adder_result[32]};
      end
      Sll: begin
        shift_left = 1'b1;
        alu_result = shift_left_result;
      end
      Srl: alu_result = shift_right_result;
      Sra: begin
        shift_arithmetic = 1'b1;
        alu_result = shift_right_result;
      end
      LXor: alu_result = opa ^ opb;
      LAnd: alu_result = opa & opb;
      LNAnd: alu_result = (~opa) & opb;
      LOr: alu_result = opa | opb;
      Eq: begin
        alu_opb = -$signed(opb);
        alu_result = ~|adder_result;
      end
      Neq: begin
        alu_opb = -$signed(opb);
        alu_result = |adder_result;
      end
      BypassA: begin
        alu_result = opa;
      end
      default: alu_result = adder_result[31:0];
    endcase
  end
  /* verilator lint_on WIDTH */

  // --------------------
  // LSU
  // --------------------
  snitch_lsu #(
    .tag_t               ( logic[RegWidth-1:0]                ),
    .NumOutstandingLoads ( snitch_pkg::NumIntOutstandingLoads )
  ) i_snitch_lsu (
    .clk_i                                ,
    .rst_i                                ,
    .lsu_qtag_i   ( rd                    ),
    .lsu_qwrite   ( is_store              ),
    .lsu_qsigned  ( is_signed             ),
    .lsu_qaddr_i  ( alu_result            ),
    .lsu_qdata_i  ( {32'b0, gpr_rdata[1]} ),
    .lsu_qsize_i  ( ls_size               ),
    .lsu_qamo_i   ( ls_amo                ),
    .lsu_qvalid_i ( lsu_qvalid            ),
    .lsu_qready_o ( lsu_qready            ),
    .lsu_pdata_o  ( ld_result             ),
    .lsu_ptag_o   ( lsu_rd                ),
    .lsu_perror_o (                       ), // ignored for the moment
    .lsu_pvalid_o ( lsu_pvalid            ),
    .lsu_pready_i ( lsu_pready            ),
    .data_qaddr_o                          ,
    .data_qwrite_o                         ,
    .data_qdata_o                          ,
    .data_qamo_o                           ,
    .data_qstrb_o                          ,
    .data_qvalid_o                         ,
    .data_qready_i                         ,
    .data_pdata_i                          ,
    .data_perror_i                         ,
    .data_pvalid_i                         ,
    .data_pready_o
  );

  assign lsu_qvalid = valid_instr & (is_load | is_store);

  // we can retire if we are not stalling and if the instruction is writing a register
  assign retire_i = write_rd & valid_instr & (rd != 0);

  // --------------------
  // Write-Back
  // --------------------
  // Write-back data, can come from:
  // 1. ALU/Jump Target/Bypass
  // 2. LSU
  // 3. Accelerator Bus
  logic [31:0] alu_writeback;
  always_comb begin
    casez (rd_select)
      RdAlu: alu_writeback = alu_result;
      RdConsecPC: alu_writeback = consec_pc;
      RdBypass: alu_writeback = rd_bypass;
      default: alu_writeback = alu_result;
    endcase
  end

  always_comb begin
    gpr_we[0] = 1'b0;
    gpr_waddr[0] = rd;
    gpr_wdata[0] = alu_writeback;
    // external interfaces
    lsu_pready = 1'b0;
    acc_pready_o = 1'b0;
    retire_acc = 1'b0;
    retire_load = 1'b0;

    if (retire_i) begin
      gpr_we[0] = 1'b1;
    // if we are not retiring another instruction retire the load now
    end else if (lsu_pvalid) begin
      retire_load = 1'b1;
      gpr_we[0] = 1'b1;
      gpr_waddr[0] = lsu_rd;
      gpr_wdata[0] = ld_result[31:0];
      lsu_pready = 1'b1;
    end else if (acc_pvalid_i) begin
      retire_acc = 1'b1;
      gpr_we[0] = 1'b1;
      gpr_waddr[0] = acc_pid_i;
      gpr_wdata[0] = acc_pdata_i[31:0];
      acc_pready_o = 1'b1;
    end
  end

  // --------------------------
  // RISC-V Formal Interface
  // --------------------------
  `ifdef RISCV_FORMAL
    logic instr_addr_misaligned;
    logic ls_misaligned;
    logic ld_addr_misaligned;
    logic ld_addr_misaligned_q;
    logic st_addr_misaligned;
    // check that the instruction is a control transfer instruction
    assign instr_addr_misaligned = (inst_data_i inside {
      riscv_instr::JAL,
      riscv_instr::JALR,
      riscv_instr::BEQ,
      riscv_instr::BNE,
      riscv_instr::BLT,
      riscv_instr::BLTU,
      riscv_instr::BGE,
      riscv_instr::BGEU
    }) && (pc_d[1:0] != 2'b0);
    // unaligned access check
    always_comb begin
      ls_misaligned = 1'b0;
      unique case (ls_size)
        HalfWord: if (adder_result[0] != 1'b0) ls_misaligned = 1'b1;
        Word: if (adder_result[1:0] != 2'b00) ls_misaligned = 1'b1;
        default: ls_misaligned = 1'b0;
      endcase
    end
    assign st_addr_misaligned = ls_misaligned & is_store;
    assign ld_addr_misaligned = ls_misaligned & is_load;

    // retire an instruction and increase ordering bit
    `FFLSR(rvfi_order[0], rvfi_order[0] + 1, rvfi_valid[0], '0, clk_i, rst_i)

    logic [31:0] ld_instr_q;
    logic [31:0] ld_addr_q;
    logic [4:0]  rs1_q;
    logic [31:0] rs1_data_q;
    logic [31:0] pc_qq;
    // we need to latch the load
    `FFLSR(ld_instr_q, inst_data_i, latch_load, '0, clk_i, rst_i)
    `FFLSR(ld_addr_q, data_qaddr_o, latch_load, '0, clk_i, rst_i)
    `FFLSR(rs1_q, rs1, latch_load, '0, clk_i, rst_i)
    `FFLSR(rs1_data_q, gpr_rdata[0], latch_load, '0, clk_i, rst_i)
    `FFLSR(pc_qq, pc_d, latch_load, '0, clk_i, rst_i)
    `FFLSR(ld_addr_misaligned_q, ld_addr_misaligned, latch_load, '0, clk_i, rst_i)

    // in case we don't retire another instruction on port 1 we can use it for loads
    logic retire_load_port1;

    assign retire_load_port1 = retire_load & stall;
    // NRET: 1
    assign rvfi_halt[0] = 1'b0;
    assign rvfi_mode[0] = 2'b11;
    assign rvfi_intr[0] = 1'b0;
    assign rvfi_valid[0] = !stall | retire_load;
    assign rvfi_insn[0] = retire_load_port1 ? ld_instr_q : (is_load ? '0 : inst_data_i);
    assign rvfi_trap[0] = retire_load_port1 ? ld_addr_misaligned_q : illegal_inst
                                                                   | instr_addr_misaligned
                                                                   | st_addr_misaligned;
    assign rvfi_rs1_addr[0]  = (retire_load_port1) ? rs1_q : rs1;
    assign rvfi_rs1_rdata[0] = (retire_load_port1) ? rs1_data_q : gpr_rdata[0];
    assign rvfi_rs2_addr[0]  = (retire_load_port1) ? '0 : rs2;
    assign rvfi_rs2_rdata[0] = (retire_load_port1) ? '0 : gpr_rdata[1];
    assign rvfi_rd_addr[0]   = (retire_load_port1) ? lsu_rd : ((gpr_we[0] && write_rd) ? rd : '0);
    assign rvfi_rd_wdata[0]  = (retire_load_port1) ? (lsu_rd != 0 ? ld_result[31:0] : '0) : (rd != 0 && gpr_we[0] && write_rd) ? gpr_wdata[0] : 0;
    assign rvfi_pc_rdata[0]  = (retire_load_port1) ? pc_qq : pc_q;
    assign rvfi_pc_wdata[0]  = (retire_load_port1) ? (pc_qq + 4) : pc_d;
    assign rvfi_mem_addr[0]  = (retire_load_port1) ? ld_addr_q : data_qaddr_o;
    assign rvfi_mem_wmask[0] = (retire_load_port1) ? '0 : ((data_qvalid_o && data_qready_i) ? data_qstrb_o[3:0] : '0);
    assign rvfi_mem_rmask[0] = (retire_load_port1) ? 4'hf : '0;
    assign rvfi_mem_rdata[0] = (retire_load_port1) ? data_pdata_i[31:0] : '0;
    assign rvfi_mem_wdata[0] = (retire_load_port1) ? '0 : data_qdata_o[31:0];
  `endif
endmodule
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Description: Variable Register File
module snitch_regfile #(
  parameter DATA_WIDTH     = 32,
  parameter NR_READ_PORTS  = 2,
  parameter NR_WRITE_PORTS = 1,
  parameter ZERO_REG_ZERO  = 0,
  parameter ADDR_WIDTH     = 4
) (
  // clock and reset
  input  logic                                      clk_i,
  // read port
  input  logic [NR_READ_PORTS-1:0][ADDR_WIDTH-1:0]  raddr_i,
  output logic [NR_READ_PORTS-1:0][DATA_WIDTH-1:0]  rdata_o,
  // write port
  input  logic [NR_WRITE_PORTS-1:0][ADDR_WIDTH-1:0] waddr_i,
  input  logic [NR_WRITE_PORTS-1:0][DATA_WIDTH-1:0] wdata_i,
  input  logic [NR_WRITE_PORTS-1:0]                 we_i
);

  localparam    NUM_WORDS  = 2**ADDR_WIDTH;

  logic [NUM_WORDS-1:0][DATA_WIDTH-1:0]     mem;
  logic [NR_WRITE_PORTS-1:0][NUM_WORDS-1:0] we_dec;


    always_comb begin : we_decoder
      for (int unsigned j = 0; j < NR_WRITE_PORTS; j++) begin
        for (int unsigned i = 0; i < NUM_WORDS; i++) begin
          if (waddr_i[j] == i) we_dec[j][i] = we_i[j];
          else we_dec[j][i] = 1'b0;
        end
      end
    end

    // loop from 1 to NUM_WORDS-1 as R0 is nil
    always_ff @(posedge clk_i) begin : register_write_behavioral
      for (int unsigned j = 0; j < NR_WRITE_PORTS; j++) begin
        for (int unsigned i = 0; i < NUM_WORDS; i++) begin
          if (we_dec[j][i]) begin
            mem[i] <= wdata_i[j];
          end
        end
        if (ZERO_REG_ZERO) begin
          mem[0] <= '0;
        end
      end
    end

  for (genvar i = 0; i < NR_READ_PORTS; i++) begin
    assign rdata_o[i] = mem[raddr_i[i]];
  end

endmodule// Copyright 2019 ETH Zurich
// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
// Description: Load Store Unit (can handle `NumOutstandingLoads` outstanding loads) and
//              optionally NaNBox if used in a floating-point setting.
//              It expects its memory sub-system to keep order (as if issued with a single ID).
module snitch_lsu #(
  parameter type tag_t                       = logic [4:0],
  parameter int unsigned NumOutstandingLoads = 1,
  parameter bit NaNBox                       = 0
) (
  input  logic          clk_i,
  input  logic          rst_i,
  // request channel
  input  tag_t          lsu_qtag_i,
  input  logic          lsu_qwrite,
  input  logic          lsu_qsigned,
  input  logic [31:0]   lsu_qaddr_i,
  input  logic [63:0]   lsu_qdata_i,
  input  logic [1:0]    lsu_qsize_i,
  input  logic [3:0]    lsu_qamo_i,
  input  logic          lsu_qvalid_i,
  output logic          lsu_qready_o,
  // response channel
  output logic [63:0]   lsu_pdata_o,
  output tag_t          lsu_ptag_o,
  output logic          lsu_perror_o,
  output logic          lsu_pvalid_o,
  input  logic          lsu_pready_i,
  // Memory Interface Channel
  output logic [31:0]   data_qaddr_o,
  output logic          data_qwrite_o,
  output logic [3:0]    data_qamo_o,
  output logic [63:0]   data_qdata_o,
  output logic [7:0]    data_qstrb_o,
  output logic          data_qvalid_o,
  input  logic          data_qready_i,
  input  logic [63:0]   data_pdata_i,
  input  logic          data_perror_i,
  input  logic          data_pvalid_i,
  output logic          data_pready_o
);

  logic [63:0] ld_result;

  typedef struct packed {
    tag_t       tag;
    logic       sign_ext;
    logic [2:0] offset;
    logic [1:0] size;
  } laq_t;

  // load adress queue (LAQ)
  laq_t laq_in, laq_out;
  logic laq_full;
  logic laq_push;

  fifo_v3 #(
    .FALL_THROUGH ( 1'b0                ),
    .DEPTH        ( NumOutstandingLoads ),
    .dtype        ( laq_t               )
  ) i_fifo_laq (
    .clk_i,
    .rst_ni    ( ~rst_i                        ),
    .flush_i   ( 1'b0                          ),
    .testmode_i( 1'b0                          ),
    .full_o    ( laq_full                      ),
    .empty_o   ( /* open */                    ),
    .usage_o   ( /* open */                    ),
    .data_i    ( laq_in                        ),
    .push_i    ( laq_push                      ),
    .data_o    ( laq_out                       ),
    .pop_i     ( data_pvalid_i & data_pready_o )
  );

  assign laq_in = '{
    tag:      lsu_qtag_i,
    sign_ext: lsu_qsigned,
    offset:   lsu_qaddr_i[2:0],
    size:     lsu_qsize_i
  };

  // only make a request when we got a valid request and if it is a load
  // also check that we can actuall store the necessary information to process
  // it in the upcoming cycle(s).
  assign data_qvalid_o = (lsu_qvalid_i) & (lsu_qwrite | ~laq_full);
  assign data_qwrite_o = lsu_qwrite;
  assign data_qaddr_o = {lsu_qaddr_i[31:3], 3'b0};
  assign data_qamo_o  = lsu_qamo_i;
  // generate byte enable mask
  always_comb begin
    unique case (lsu_qsize_i)
      2'b00: data_qstrb_o = (8'b1 << lsu_qaddr_i[2:0]);
      2'b01: data_qstrb_o = (8'b11 << lsu_qaddr_i[2:0]);
      2'b10: data_qstrb_o = (8'b1111 << lsu_qaddr_i[2:0]);
      2'b11: data_qstrb_o = '1;
      default: data_qstrb_o = '0;
    endcase
  end

  // re-align write data
  /* verilator lint_off WIDTH */
  always_comb begin
    unique case (lsu_qaddr_i[2:0])
      3'b000: data_qdata_o = lsu_qdata_i;
      3'b001: data_qdata_o = {lsu_qdata_i[55:0], lsu_qdata_i[63:56]};
      3'b010: data_qdata_o = {lsu_qdata_i[47:0], lsu_qdata_i[63:48]};
      3'b011: data_qdata_o = {lsu_qdata_i[39:0], lsu_qdata_i[63:40]};
      3'b100: data_qdata_o = {lsu_qdata_i[31:0], lsu_qdata_i[63:32]};
      3'b101: data_qdata_o = {lsu_qdata_i[23:0], lsu_qdata_i[63:24]};
      3'b110: data_qdata_o = {lsu_qdata_i[15:0], lsu_qdata_i[63:16]};
      3'b111: data_qdata_o = {lsu_qdata_i[7:0],  lsu_qdata_i[63:8]};
      default: data_qdata_o = lsu_qdata_i;
    endcase
  end
  /* verilator lint_on WIDTH */

  // the interface didn't accept our request yet
  assign lsu_qready_o = ~(data_qvalid_o & ~data_qready_i) & ~laq_full;
  assign laq_push = data_qready_i & data_qvalid_o & ~laq_full;

  // Return Path
  // shift the load data back
  logic [63:0] shifted_data;
  assign shifted_data = data_pdata_i >> {laq_out.offset, 3'b000};
  always_comb begin
    unique case (laq_out.size)
      2'b00: ld_result = {{56{shifted_data[7] & laq_out.sign_ext}}, shifted_data[7:0]};
      2'b01: ld_result = {{48{shifted_data[15] & laq_out.sign_ext}}, shifted_data[15:0]};
      2'b10: ld_result = {{32{(shifted_data[31] | NaNBox) & laq_out.sign_ext}}, shifted_data[31:0]};
      2'b11: ld_result = shifted_data;
      default: ld_result = shifted_data;
    endcase
  end

  assign lsu_perror_o = data_perror_i;
  assign lsu_pdata_o = ld_result;
  assign lsu_ptag_o = laq_out.tag;
  assign lsu_pvalid_o = data_pvalid_i;
  assign data_pready_o = lsu_pready_i;
endmodule
// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>

module fifo_v3 #(
    parameter bit          FALL_THROUGH = 1'b0, // fifo is in fall-through mode
    parameter int unsigned DATA_WIDTH   = 32,   // default data width if the fifo is of type logic
    parameter int unsigned DEPTH        = 8,    // depth can be arbitrary from 0 to 2**32
    parameter type dtype                = logic [DATA_WIDTH-1:0],
    // DO NOT OVERWRITE THIS PARAMETER
    parameter int unsigned ADDR_DEPTH   = (DEPTH > 1) ? $clog2(DEPTH) : 1
)(
    input  logic  clk_i,            // Clock
    input  logic  rst_ni,           // Asynchronous reset active low
    input  logic  flush_i,          // flush the queue
    input  logic  testmode_i,       // test_mode to bypass clock gating
    // status flags
    output logic  full_o,           // queue is full
    output logic  empty_o,          // queue is empty
    output logic  [ADDR_DEPTH-1:0] usage_o,  // fill pointer
    // as long as the queue is not full we can push new data
    input  dtype  data_i,           // data to push into the queue
    input  logic  push_i,           // data is valid and can be pushed to the queue
    // as long as the queue is not empty we can pop new elements
    output dtype  data_o,           // output data
    input  logic  pop_i             // pop head from queue
);
    // local parameter
    // FIFO depth - handle the case of pass-through, synthesizer will do constant propagation
    localparam int unsigned FIFO_DEPTH = (DEPTH > 0) ? DEPTH : 1;
    // clock gating control
    logic gate_clock;
    // pointer to the read and write section of the queue
    logic [ADDR_DEPTH - 1:0] read_pointer_n, read_pointer_q, write_pointer_n, write_pointer_q;
    // keep a counter to keep track of the current queue status
    logic [ADDR_DEPTH:0] status_cnt_n, status_cnt_q; // this integer will be truncated by the synthesis tool
    // actual memory
    dtype [FIFO_DEPTH - 1:0] mem_n, mem_q;

    assign usage_o = status_cnt_q[ADDR_DEPTH-1:0];

    if (DEPTH == 0) begin
        assign empty_o     = ~push_i;
        assign full_o      = ~pop_i;
    end else begin
        assign full_o       = (status_cnt_q == FIFO_DEPTH[ADDR_DEPTH:0]);
        assign empty_o      = (status_cnt_q == 0) & ~(FALL_THROUGH & push_i);
    end
    // status flags

    // read and write queue logic
    always_comb begin : read_write_comb
        // default assignment
        read_pointer_n  = read_pointer_q;
        write_pointer_n = write_pointer_q;
        status_cnt_n    = status_cnt_q;
        data_o          = (DEPTH == 0) ? data_i : mem_q[read_pointer_q];
        mem_n           = mem_q;
        gate_clock      = 1'b1;

        // push a new element to the queue
        if (push_i && ~full_o) begin
            // push the data onto the queue
            mem_n[write_pointer_q] = data_i;
            // un-gate the clock, we want to write something
            gate_clock = 1'b0;
            // increment the write counter
            if (write_pointer_q == FIFO_DEPTH[ADDR_DEPTH-1:0] - 1)
                write_pointer_n = '0;
            else
                write_pointer_n = write_pointer_q + 1;
            // increment the overall counter
            status_cnt_n    = status_cnt_q + 1;
        end

        if (pop_i && ~empty_o) begin
            // read from the queue is a default assignment
            // but increment the read pointer...
            if (read_pointer_n == FIFO_DEPTH[ADDR_DEPTH-1:0] - 1)
                read_pointer_n = '0;
            else
                read_pointer_n = read_pointer_q + 1;
            // ... and decrement the overall count
            status_cnt_n   = status_cnt_q - 1;
        end

        // keep the count pointer stable if we push and pop at the same time
        if (push_i && pop_i &&  ~full_o && ~empty_o)
            status_cnt_n   = status_cnt_q;

        // FIFO is in pass through mode -> do not change the pointers
        if (FALL_THROUGH && (status_cnt_q == 0) && push_i) begin
            data_o = data_i;
            if (pop_i) begin
                status_cnt_n = status_cnt_q;
                read_pointer_n = read_pointer_q;
                write_pointer_n = write_pointer_q;
            end
        end
    end

    // sequential process
    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            read_pointer_q  <= '0;
            write_pointer_q <= '0;
            status_cnt_q    <= '0;
        end else begin
            if (flush_i) begin
                read_pointer_q  <= '0;
                write_pointer_q <= '0;
                status_cnt_q    <= '0;
             end else begin
                read_pointer_q  <= read_pointer_n;
                write_pointer_q <= write_pointer_n;
                status_cnt_q    <= status_cnt_n;
            end
        end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
            mem_q <= '0;
        end else if (!gate_clock) begin
            mem_q <= mem_n;
        end
    end

// pragma translate_off
`ifndef VERILATOR
    initial begin
        assert (DEPTH > 0)             else $error("DEPTH must be greater than 0.");
    end

    full_write : assert property(
        @(posedge clk_i) disable iff (~rst_ni) (full_o |-> ~push_i))
        else $fatal (1, "Trying to push new data although the FIFO is full.");

    empty_read : assert property(
        @(posedge clk_i) disable iff (~rst_ni) (empty_o |-> ~pop_i))
        else $fatal (1, "Trying to pop data although the FIFO is empty.");
`endif
// pragma translate_on

endmodule // fifo_v3
