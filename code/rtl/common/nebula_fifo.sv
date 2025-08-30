/**
 * Parameterizable FIFO Buffer
 * 
 * A synchronous FIFO with configurable data width and depth.
 * Includes full/empty flags, data count, and optional almost_full/almost_empty.
 * 
 * Features:
 * - Parameterizable width and depth
 * - Full/empty flag generation
 * - Data count output
 * - Optional programmable almost_full/almost_empty thresholds
 */

import nebula_pkg::*;

module nebula_fifo #(
  parameter int DATA_WIDTH = FLIT_WIDTH,
  parameter int DEPTH = VC_DEPTH,
  parameter int ALMOST_FULL_THRESH = DEPTH - 2,
  parameter int ALMOST_EMPTY_THRESH = 2
)(
  input  logic                        clk,
  input  logic                        rst_n,
  
  // Write interface
  input  logic                        wr_en,
  input  logic [DATA_WIDTH-1:0]       wr_data,
  output logic                        full,
  output logic                        almost_full,
  
  // Read interface
  input  logic                        rd_en,
  output logic [DATA_WIDTH-1:0]       rd_data,
  output logic                        empty,
  output logic                        almost_empty,
  
  // Status
  output logic [$clog2(DEPTH+1)-1:0] count
);

  // Internal memory array
  logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];
  
  // Pointers
  logic [$clog2(DEPTH)-1:0] wr_ptr, rd_ptr;
  logic [$clog2(DEPTH):0]   count_int;  // Extra bit to distinguish full/empty
  
  // Full and empty generation
  assign full  = (count_int == DEPTH);
  assign empty = (count_int == 0);
  assign almost_full  = (count_int >= ALMOST_FULL_THRESH);
  assign almost_empty = (count_int <= ALMOST_EMPTY_THRESH);
  assign count = count_int[$clog2(DEPTH+1)-1:0];
  
  // Write operation
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      wr_ptr <= '0;
    end else if (wr_en && !full) begin
      mem[wr_ptr] <= wr_data;
      wr_ptr <= (wr_ptr == DEPTH-1) ? '0 : wr_ptr + 1;
    end
  end
  
  // Read operation - show-ahead mode (data available without read enable)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      rd_ptr <= '0;
    end else if (rd_en && !empty) begin
      rd_ptr <= (rd_ptr == DEPTH-1) ? '0 : rd_ptr + 1;
    end
  end
  
  // Continuous assignment for read data - show-ahead mode
  assign rd_data = empty ? '0 : mem[rd_ptr];
  
  // Count tracking
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      count_int <= '0;
    end else begin
      case ({wr_en && !full, rd_en && !empty})
        2'b01: count_int <= count_int - 1;  // Read only
        2'b10: count_int <= count_int + 1;  // Write only
        default: ; // No change for 00 (no op) or 11 (read+write)
      endcase
    end
  end
  
  // Assertions for verification
  `ifdef ASSERT_ON
    // Check for overflow/underflow
    property no_overflow;
      @(posedge clk) disable iff (!rst_n)
      wr_en |-> !full;
    endproperty
    assert property (no_overflow) else $error("FIFO write when full");
    
    property no_underflow;
      @(posedge clk) disable iff (!rst_n)
      rd_en |-> !empty;
    endproperty
    assert property (no_underflow) else $error("FIFO read when empty");
    
    // Check count consistency
    property count_consistency;
      @(posedge clk) disable iff (!rst_n)
      (count_int >= 0) && (count_int <= DEPTH);
    endproperty
    assert property (count_consistency) else $error("FIFO count out of range");
  `endif

endmodule
