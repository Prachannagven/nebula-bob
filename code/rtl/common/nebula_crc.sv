/**
 * CRC Generator and Checker
 * 
 * Implements CRC-32 (IEEE 802.3) using parallel LFSR for high-speed operation.
 * Supports both generation and checking modes.
 * 
 * Features:
 * - CRC-32 IEEE 802.3 polynomial (0x04C11DB7)
 * - Parallel processing for high throughput
 * - Configurable data width
 * - Generate and check modes
 */

import nebula_pkg::*;

module nebula_crc #(
  parameter int DATA_WIDTH = FLIT_WIDTH,
  parameter int CRC_WIDTH = 32,
  parameter logic [CRC_WIDTH-1:0] CRC_POLYNOMIAL = 32'h04C11DB7
)(
  input  logic                      clk,
  input  logic                      rst_n,
  
  // Control
  input  logic                      enable,
  input  logic                      clear,
  
  // Data input
  input  logic [DATA_WIDTH-1:0]     data_in,
  input  logic                      data_valid,
  
  // CRC output
  output logic [CRC_WIDTH-1:0]      crc_out,
  output logic                      crc_valid
);

  // CRC register
  logic [CRC_WIDTH-1:0] crc_reg;
  logic [CRC_WIDTH-1:0] crc_next;
  
  // CRC computation using parallel LFSR
  always_comb begin
    crc_next = crc_reg;
    
    if (enable && data_valid) begin
      // Process each bit of input data
      for (int i = DATA_WIDTH-1; i >= 0; i--) begin
        logic msb = crc_next[CRC_WIDTH-1];
        crc_next = {crc_next[CRC_WIDTH-2:0], 1'b0};  // Shift left
        if (msb ^ data_in[i]) begin
          crc_next = crc_next ^ CRC_POLYNOMIAL;
        end
      end
    end
  end
  
  // CRC register update
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      crc_reg <= '1;  // Initialize to all 1s (standard practice)
      crc_valid <= 1'b0;
    end else if (clear) begin
      crc_reg <= '1;
      crc_valid <= 1'b0;
    end else if (enable && data_valid) begin
      crc_reg <= crc_next;
      crc_valid <= 1'b1;
    end else begin
      crc_valid <= 1'b0;
    end
  end
  
  // Output assignment (inverted per IEEE standard)
  assign crc_out = ~crc_reg;

endmodule

/**
 * CRC Checker Module
 * Verifies CRC integrity of received data
 */
module nebula_crc_checker #(
  parameter int DATA_WIDTH = FLIT_WIDTH,
  parameter int CRC_WIDTH = 32
)(
  input  logic                      clk,
  input  logic                      rst_n,
  
  // Data and CRC input
  input  logic [DATA_WIDTH-1:0]     data_in,
  input  logic [CRC_WIDTH-1:0]      crc_in,
  input  logic                      check_enable,
  
  // Check result
  output logic                      crc_ok,
  output logic                      check_valid
);

  // Expected CRC generation
  logic [CRC_WIDTH-1:0] expected_crc;
  logic                 crc_gen_valid;
  logic                 check_enable_r;
  logic                 check_start;
  // Clear/data pulses to ensure crc_gen is computed from a fresh state for each check
  logic                 clear_pulse;
  logic                 data_pulse;
  
  // Register check_enable and generate a clear pulse then a data-valid pulse
  // to guarantee the internal CRC generator starts from the known initial state
  // for each check. Sequence: check_start -> clear_pulse (same cycle) ->
  // data_pulse (next cycle). The crc_gen sees clear first, then data_valid.
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      check_enable_r <= 1'b0;
      check_start <= 1'b0;
      clear_pulse <= 1'b0;
      data_pulse <= 1'b0;
    end else begin
      check_enable_r <= check_enable;
      // Pulse when check_enable rises
      check_start <= check_enable && !check_enable_r;
      // Assert clear for one cycle when a check starts
      clear_pulse <= check_start;
      // Assert data_valid one cycle after clear so crc_gen computes from fresh state
      data_pulse <= clear_pulse;
    end
  end
  
  // Debug prints
  `ifndef SYNTHESIS
  always @(posedge clk) begin
    if (check_enable || check_enable_r || check_start || clear_pulse || data_pulse || crc_gen_valid) begin
      $display("[%0t] CRC_CHECKER: check_enable=%b, check_enable_r=%b, check_start=%b, clear_pulse=%b, data_pulse=%b, crc_gen_valid=%b", 
               $time, check_enable, check_enable_r, check_start, clear_pulse, data_pulse, crc_gen_valid);
    end
  end
  `endif
  
  nebula_crc #(
    .DATA_WIDTH(DATA_WIDTH),
    .CRC_WIDTH(CRC_WIDTH)
  ) crc_gen (
    .clk(clk),
    .rst_n(rst_n),
    .enable(1'b1),  // Always enabled
  .clear(clear_pulse),
  .data_in(data_in),
  .data_valid(data_pulse),  // data_valid asserted one cycle after clear_pulse
    .crc_out(expected_crc),
    .crc_valid(crc_gen_valid)
  );
  
  // Compare generated CRC with received CRC
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      crc_ok <= 1'b0;
      check_valid <= 1'b0;
    end else if (crc_gen_valid) begin
  crc_ok <= (expected_crc == crc_in);
  check_valid <= 1'b1;
`ifndef SYNTHESIS
  $display("[%0t] CRC_CHECKER: expected=0x%h, provided=0x%h, cmp=%b", $time, expected_crc, crc_in, (expected_crc == crc_in));
`endif
    end else begin
      check_valid <= 1'b0;
    end
  end
  
  // Assertions for verification
  `ifdef ASSERT_ON
    property check_timing;
      @(posedge clk) disable iff (!rst_n)
      check_valid |-> $past(check_enable);
    endproperty
    assert property (check_timing) else $error("CRC check timing violation");
  `endif

endmodule
