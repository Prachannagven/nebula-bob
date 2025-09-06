/**
 * Nebula AXI4 System Integration Module
 * 
 * This module integrates the AXI4 interface with the NoC bridge and provides
 * a complete AXI4-to-NoC translation system. It instantiates both the AXI4
 * interface module and the translation bridge, connecting them with proper
 * flow control and error handling.
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: August 2025
 */

`include "nebula_pkg.sv"

module nebula_axi_system
  import nebula_pkg::*;
#(
  parameter int NODE_X = 0,
  parameter int NODE_Y = 0,
  parameter int MESH_SIZE_X = 4,
  parameter int MESH_SIZE_Y = 4
)(
  input  logic clk,
  input  logic rst_n,
  
  // AXI4 Interface
  input  logic                      axi_awvalid,
  output logic                      axi_awready,
  input  logic [AXI_ID_WIDTH-1:0]   axi_awid,
  input  logic [AXI_ADDR_WIDTH-1:0] axi_awaddr,
  input  logic [7:0]                axi_awlen,
  input  logic [2:0]                axi_awsize,
  input  logic [1:0]                axi_awburst,
  input  logic                      axi_awlock,
  input  logic [3:0]                axi_awcache,
  input  logic [2:0]                axi_awprot,
  input  logic [QOS_WIDTH-1:0]      axi_awqos,
  input  logic [3:0]                axi_awregion,
  input  logic [AXI_AWUSER_WIDTH-1:0] axi_awuser,
  
  input  logic                      axi_wvalid,
  output logic                      axi_wready,
  input  logic [AXI_DATA_WIDTH-1:0] axi_wdata,
  input  logic [AXI_STRB_WIDTH-1:0] axi_wstrb,
  input  logic                      axi_wlast,
  input  logic [AXI_WUSER_WIDTH-1:0] axi_wuser,
  
  output logic                      axi_bvalid,
  input  logic                      axi_bready,
  output logic [AXI_ID_WIDTH-1:0]   axi_bid,
  output logic [1:0]                axi_bresp,
  output logic [AXI_BUSER_WIDTH-1:0] axi_buser,
  
  input  logic                      axi_arvalid,
  output logic                      axi_arready,
  input  logic [AXI_ID_WIDTH-1:0]   axi_arid,
  input  logic [AXI_ADDR_WIDTH-1:0] axi_araddr,
  input  logic [7:0]                axi_arlen,
  input  logic [2:0]                axi_arsize,
  input  logic [1:0]                axi_arburst,
  input  logic                      axi_arlock,
  input  logic [3:0]                axi_arcache,
  input  logic [2:0]                axi_arprot,
  input  logic [QOS_WIDTH-1:0]      axi_arqos,
  input  logic [3:0]                axi_arregion,
  input  logic [AXI_ARUSER_WIDTH-1:0] axi_aruser,
  
  output logic                      axi_rvalid,
  input  logic                      axi_rready,
  output logic [AXI_ID_WIDTH-1:0]   axi_rid,
  output logic [AXI_DATA_WIDTH-1:0] axi_rdata,
  output logic [1:0]                axi_rresp,
  output logic                      axi_rlast,
  output logic [AXI_RUSER_WIDTH-1:0] axi_ruser,
  
  // NoC Interface
  output logic      noc_flit_out_valid,
  input  logic      noc_flit_out_ready,
  output noc_flit_t noc_flit_out,
  
  input  logic      noc_flit_in_valid,
  output logic      noc_flit_in_ready,
  input  noc_flit_t noc_flit_in,
  
  // Configuration
  input  logic [AXI_ADDR_WIDTH-1:0] base_addr,
  input  logic [AXI_ADDR_WIDTH-1:0] addr_mask,
  
  // Status and Debug
  output logic [31:0] status_reg,
  output logic [31:0] error_reg,
  output logic [31:0] perf_counters [3:0]
);

  // Internal connections between AXI interface and bridge
  logic                      int_noc_req_valid;
  logic                      int_noc_req_ready;
  noc_flit_t                 int_noc_req_flit;
  logic                      int_noc_resp_valid;
  logic                      int_noc_resp_ready;
  noc_flit_t                 int_noc_resp_flit;
  
  // Status and performance monitoring
  logic [31:0] axi_outstanding_count;
  logic [31:0] axi_error_status;
  logic [31:0] axi_perf_read_count;
  logic [31:0] axi_perf_write_count;
  
  logic [31:0] bridge_status_reg;
  logic [31:0] bridge_error_reg;
  logic [31:0] bridge_packet_tx_count;
  logic [31:0] bridge_packet_rx_count;
  logic [15:0] bridge_avg_latency;
  logic [7:0]  bridge_buffer_utilization;

  // =============================================================================
  // AXI4 INTERFACE INSTANTIATION
  // =============================================================================
  
  nebula_axi_if #(
    .OUTSTANDING_DEPTH(64),
    .NODE_X(NODE_X),
    .NODE_Y(NODE_Y)
  ) u_axi_if (
    .clk(clk),
    .rst_n(rst_n),
    
    // AXI4 Interface
    .axi_awvalid(axi_awvalid),
    .axi_awready(axi_awready),
    .axi_awid(axi_awid),
    .axi_awaddr(axi_awaddr),
    .axi_awlen(axi_awlen),
    .axi_awsize(axi_awsize),
    .axi_awburst(axi_awburst),
    .axi_awlock(axi_awlock),
    .axi_awcache(axi_awcache),
    .axi_awprot(axi_awprot),
    .axi_awqos(axi_awqos),
    .axi_awregion(axi_awregion),
    .axi_awuser(axi_awuser),
    
    .axi_wvalid(axi_wvalid),
    .axi_wready(axi_wready),
    .axi_wdata(axi_wdata),
    .axi_wstrb(axi_wstrb),
    .axi_wlast(axi_wlast),
    .axi_wuser(axi_wuser),
    
    .axi_bvalid(axi_bvalid),
    .axi_bready(axi_bready),
    .axi_bid(axi_bid),
    .axi_bresp(axi_bresp),
    .axi_buser(axi_buser),
    
    .axi_arvalid(axi_arvalid),
    .axi_arready(axi_arready),
    .axi_arid(axi_arid),
    .axi_araddr(axi_araddr),
    .axi_arlen(axi_arlen),
    .axi_arsize(axi_arsize),
    .axi_arburst(axi_arburst),
    .axi_arlock(axi_arlock),
    .axi_arcache(axi_arcache),
    .axi_arprot(axi_arprot),
    .axi_arqos(axi_arqos),
    .axi_arregion(axi_arregion),
    .axi_aruser(axi_aruser),
    
    .axi_rvalid(axi_rvalid),
    .axi_rready(axi_rready),
    .axi_rid(axi_rid),
    .axi_rdata(axi_rdata),
    .axi_rresp(axi_rresp),
    .axi_rlast(axi_rlast),
    .axi_ruser(axi_ruser),
    
    // NoC Interface
    .noc_req_valid(int_noc_req_valid),
    .noc_req_ready(int_noc_req_ready),
    .noc_req_flit(int_noc_req_flit),
    
    .noc_resp_valid(int_noc_resp_valid),
    .noc_resp_ready(int_noc_resp_ready),
    .noc_resp_flit(int_noc_resp_flit),
    
    // Status and Debug
    .outstanding_count(axi_outstanding_count),
    .error_status(axi_error_status),
    .perf_read_count(axi_perf_read_count),
    .perf_write_count(axi_perf_write_count)
  );

  // =============================================================================
  // AXI-NOC BRIDGE INSTANTIATION (Simple Version)
  // =============================================================================
  
  nebula_axi_noc_bridge_simple #(
    .NODE_X(NODE_X),
    .NODE_Y(NODE_Y),
    .MESH_SIZE_X(MESH_SIZE_X),
    .MESH_SIZE_Y(MESH_SIZE_Y)
  ) u_bridge (
    .clk(clk),
    .rst_n(rst_n),
    
    // Configuration
    .base_addr(base_addr),
    .addr_mask(addr_mask),
    
    // NoC Interface
    .noc_flit_out_valid(noc_flit_out_valid),
    .noc_flit_out_ready(noc_flit_out_ready),
    .noc_flit_out(noc_flit_out),
    
    .noc_flit_in_valid(noc_flit_in_valid),
    .noc_flit_in_ready(noc_flit_in_ready),
    .noc_flit_in(noc_flit_in),
    
    // Status and Debug
    .status_reg(bridge_status_reg),
    .error_reg(bridge_error_reg),
    .packet_tx_count(bridge_packet_tx_count),
    .packet_rx_count(bridge_packet_rx_count),
    .avg_latency(bridge_avg_latency),
    .buffer_utilization(bridge_buffer_utilization)
  );

  // =============================================================================
  // STATUS AND PERFORMANCE MONITORING AGGREGATION
  // =============================================================================
  
  // Combine status and error information
  assign status_reg = {
    bridge_buffer_utilization,          // [31:24]
    bridge_avg_latency,                 // [23:8]
    bridge_status_reg[7:0]              // [7:0]
  };
  
  assign error_reg = axi_error_status | bridge_error_reg;
  
  // Performance counter outputs
  assign perf_counters[0] = axi_perf_read_count;
  assign perf_counters[1] = axi_perf_write_count;
  assign perf_counters[2] = bridge_packet_tx_count;
  assign perf_counters[3] = bridge_packet_rx_count;

endmodule
