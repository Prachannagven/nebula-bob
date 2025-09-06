/**
 * Simplified Nebula AXI-NoC Bridge Module
 * 
 * This is a simplified version focusing on basic AXI-to-NoC translation
 * without complex reorder buffer management for initial implementation.
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: August 2025
 */

`include "nebula_pkg.sv"

module nebula_axi_noc_bridge_simple
  import nebula_pkg::*;
#(
  parameter int NODE_X = 0,
  parameter int NODE_Y = 0,
  parameter int MESH_SIZE_X = 4,
  parameter int MESH_SIZE_Y = 4
)(
  input  logic clk,
  input  logic rst_n,
  
  // Configuration
  input  logic [AXI_ADDR_WIDTH-1:0] base_addr,
  input  logic [AXI_ADDR_WIDTH-1:0] addr_mask,
  
  // NoC Interface - External (connects to router)
  output logic      noc_flit_out_valid,
  input  logic      noc_flit_out_ready,
  output noc_flit_t noc_flit_out,
  
  input  logic      noc_flit_in_valid,
  output logic      noc_flit_in_ready,
  input  noc_flit_t noc_flit_in,
  
  // Status and Debug
  output logic [31:0] status_reg,
  output logic [31:0] error_reg,
  output logic [31:0] packet_tx_count,
  output logic [31:0] packet_rx_count,
  output logic [15:0] avg_latency,
  output logic [7:0]  buffer_utilization
);

  // =============================================================================
  // INTERNAL REGISTERS AND COUNTERS
  // =============================================================================
  
  logic [31:0] tx_count, rx_count;
  logic [31:0] error_status;
  
  // =============================================================================
  // SIMPLE NOC INTERFACE HANDLING
  // =============================================================================
  
  // For this simplified implementation, we'll just acknowledge NoC packets
  assign noc_flit_out_valid = 1'b0; // No outgoing packets for now
  assign noc_flit_out = '0;
  assign noc_flit_in_ready = 1'b1;  // Always ready to receive
  
  // Count incoming packets
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_count <= 0;
      rx_count <= 0;
      error_status <= 0;
    end else begin
      if (noc_flit_in_valid && noc_flit_in_ready) begin
        rx_count <= rx_count + 1;
      end
      
      if (noc_flit_out_valid && noc_flit_out_ready) begin
        tx_count <= tx_count + 1;
      end
    end
  end
  
  // =============================================================================
  // STATUS OUTPUTS
  // =============================================================================
  
  assign status_reg = {24'b0, 8'b0}; // Simple status
  assign error_reg = error_status;
  assign packet_tx_count = tx_count;
  assign packet_rx_count = rx_count;
  assign avg_latency = 16'h0; // Not implemented yet
  assign buffer_utilization = 8'h0; // Not implemented yet

endmodule
