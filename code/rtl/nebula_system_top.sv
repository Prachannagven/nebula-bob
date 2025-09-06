/**
 * Nebula Complete System Integration
 * 
 * This module integrates the complete Nebula system including:
 * - Mesh topology with parameterizable size
 * - Network Interface Units (NIUs) for each node
 * - Global address mapping and routing
 * - Performance monitoring and debug interfaces
 * 
 * Features:
 * - Scalable mesh topology (2x2 to 8x8)
 * - AXI4 interfaces for each node
 * - Global address space management
 * - Hierarchical clustering support
 * - System-wide performance monitoring
 * - Debug and status reporting
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: September 2025
 */

import nebula_pkg::*;

module nebula_system_top #(
  parameter int MESH_SIZE_X = 4,
  parameter int MESH_SIZE_Y = 4,
  parameter logic [AXI_ADDR_WIDTH-1:0] GLOBAL_BASE_ADDR = 64'h0000_0000_1000_0000,
  parameter logic [AXI_ADDR_WIDTH-1:0] NODE_ADDR_SIZE = 64'h0000_0000_0010_0000  // 1MB per node
)(
  input  logic clk,
  input  logic rst_n,
  
  // ============================================================================
  // AXI4 INTERFACES (One per node)
  // ============================================================================
  
  // AXI Write Address Channels
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_awvalid,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_awready,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ID_WIDTH-1:0]       axi_awid,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ADDR_WIDTH-1:0]     axi_awaddr,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][7:0]                    axi_awlen,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][2:0]                    axi_awsize,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][1:0]                    axi_awburst,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_awlock,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][3:0]                    axi_awcache,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][2:0]                    axi_awprot,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][QOS_WIDTH-1:0]          axi_awqos,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][3:0]                    axi_awregion,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_AWUSER_WIDTH-1:0]   axi_awuser,
  
  // AXI Write Data Channels
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_wvalid,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_wready,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_DATA_WIDTH-1:0]     axi_wdata,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_STRB_WIDTH-1:0]     axi_wstrb,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_wlast,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_WUSER_WIDTH-1:0]    axi_wuser,
  
  // AXI Write Response Channels
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_bvalid,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_bready,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ID_WIDTH-1:0]       axi_bid,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][1:0]                    axi_bresp,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_BUSER_WIDTH-1:0]    axi_buser,
  
  // AXI Read Address Channels
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_arvalid,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_arready,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ID_WIDTH-1:0]       axi_arid,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ADDR_WIDTH-1:0]     axi_araddr,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][7:0]                    axi_arlen,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][2:0]                    axi_arsize,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][1:0]                    axi_arburst,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_arlock,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][3:0]                    axi_arcache,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][2:0]                    axi_arprot,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][QOS_WIDTH-1:0]          axi_arqos,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][3:0]                    axi_arregion,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ARUSER_WIDTH-1:0]   axi_aruser,
  
  // AXI Read Data Channels
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_rvalid,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_rready,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ID_WIDTH-1:0]       axi_rid,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_DATA_WIDTH-1:0]     axi_rdata,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][1:0]                    axi_rresp,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_rlast,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_RUSER_WIDTH-1:0]    axi_ruser,
  
  // ============================================================================
  // SYSTEM CONFIGURATION
  // ============================================================================
  
  // Global configuration
  input  logic [AXI_ADDR_WIDTH-1:0] global_base_addr,
  input  logic [AXI_ADDR_WIDTH-1:0] global_addr_mask,
  
  // ============================================================================
  // SYSTEM STATUS AND DEBUG
  // ============================================================================
  
  // System-wide status
  output logic [31:0] system_status,
  output logic [31:0] system_errors,
  output logic [31:0] system_perf_counters [15:0],
  
  // Per-node status
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][31:0] node_status,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][31:0] node_errors,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][31:0] node_info,
  
  // Mesh debug
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0][NUM_VCS-1:0] mesh_vc_status,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][PERF_COUNTER_WIDTH-1:0] mesh_packets_routed,
  output error_code_e [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] mesh_error_status
);

  // ============================================================================
  // PARAMETER VALIDATION
  // ============================================================================
  
  initial begin
    if (MESH_SIZE_X < 2 || MESH_SIZE_X > MAX_MESH_SIZE) begin
      $fatal(1, "MESH_SIZE_X must be between 2 and %0d, got %0d", MAX_MESH_SIZE, MESH_SIZE_X);
    end
    if (MESH_SIZE_Y < 2 || MESH_SIZE_Y > MAX_MESH_SIZE) begin
      $fatal(1, "MESH_SIZE_Y must be between 2 and %0d, got %0d", MAX_MESH_SIZE, MESH_SIZE_Y);
    end
    if (MESH_SIZE_X * MESH_SIZE_Y > 64) begin
      $fatal(1, "Total nodes %0d exceeds maximum of 64", MESH_SIZE_X * MESH_SIZE_Y);
    end
  end

  // ============================================================================
  // INTERNAL MESH CONNECTIVITY
  // ============================================================================
  
  // Mesh-NIU interface signals
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         mesh_local_flit_in_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]    mesh_local_flit_in;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         mesh_local_flit_in_ready;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         mesh_local_flit_out_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]    mesh_local_flit_out;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         mesh_local_flit_out_ready;

  // ============================================================================
  // MESH TOPOLOGY INSTANTIATION
  // ============================================================================
  
  nebula_mesh_top #(
    .MESH_SIZE_X(MESH_SIZE_X),
    .MESH_SIZE_Y(MESH_SIZE_Y)
  ) mesh_inst (
    .clk(clk),
    .rst_n(rst_n),
    
    // Local port interfaces
    .local_flit_in_valid(mesh_local_flit_in_valid),
    .local_flit_in(mesh_local_flit_in),
    .local_flit_in_ready(mesh_local_flit_in_ready),
    .local_flit_out_valid(mesh_local_flit_out_valid),
    .local_flit_out(mesh_local_flit_out),
    .local_flit_out_ready(mesh_local_flit_out_ready),
    
    // Debug and performance monitoring
    .vc_status(mesh_vc_status),
    .packets_routed(mesh_packets_routed),
    .error_status(mesh_error_status)
  );

  // ============================================================================
  // NETWORK INTERFACE UNIT INSTANTIATION
  // ============================================================================
  
  genvar x, y;
  generate
    for (x = 0; x < MESH_SIZE_X; x++) begin : gen_niu_x
      for (y = 0; y < MESH_SIZE_Y; y++) begin : gen_niu_y
        
        // Calculate node-specific addresses
        localparam logic [AXI_ADDR_WIDTH-1:0] NODE_BASE = 
          GLOBAL_BASE_ADDR + ((y * MESH_SIZE_X + x) * NODE_ADDR_SIZE);
        localparam logic [AXI_ADDR_WIDTH-1:0] NODE_MASK = 
          ~(NODE_ADDR_SIZE - 1);
        
        nebula_niu_axi #(
          .NODE_X(x),
          .NODE_Y(y),
          .MESH_SIZE_X(MESH_SIZE_X),
          .MESH_SIZE_Y(MESH_SIZE_Y),
          .NODE_BASE_ADDR(NODE_BASE),
          .NODE_ADDR_MASK(NODE_MASK)
        ) niu_inst (
          .clk(clk),
          .rst_n(rst_n),
          
          // AXI interface
          .axi_awvalid(axi_awvalid[x][y]),
          .axi_awready(axi_awready[x][y]),
          .axi_awid(axi_awid[x][y]),
          .axi_awaddr(axi_awaddr[x][y]),
          .axi_awlen(axi_awlen[x][y]),
          .axi_awsize(axi_awsize[x][y]),
          .axi_awburst(axi_awburst[x][y]),
          .axi_awlock(axi_awlock[x][y]),
          .axi_awcache(axi_awcache[x][y]),
          .axi_awprot(axi_awprot[x][y]),
          .axi_awqos(axi_awqos[x][y]),
          .axi_awregion(axi_awregion[x][y]),
          .axi_awuser(axi_awuser[x][y]),
          
          .axi_wvalid(axi_wvalid[x][y]),
          .axi_wready(axi_wready[x][y]),
          .axi_wdata(axi_wdata[x][y]),
          .axi_wstrb(axi_wstrb[x][y]),
          .axi_wlast(axi_wlast[x][y]),
          .axi_wuser(axi_wuser[x][y]),
          
          .axi_bvalid(axi_bvalid[x][y]),
          .axi_bready(axi_bready[x][y]),
          .axi_bid(axi_bid[x][y]),
          .axi_bresp(axi_bresp[x][y]),
          .axi_buser(axi_buser[x][y]),
          
          .axi_arvalid(axi_arvalid[x][y]),
          .axi_arready(axi_arready[x][y]),
          .axi_arid(axi_arid[x][y]),
          .axi_araddr(axi_araddr[x][y]),
          .axi_arlen(axi_arlen[x][y]),
          .axi_arsize(axi_arsize[x][y]),
          .axi_arburst(axi_arburst[x][y]),
          .axi_arlock(axi_arlock[x][y]),
          .axi_arcache(axi_arcache[x][y]),
          .axi_arprot(axi_arprot[x][y]),
          .axi_arqos(axi_arqos[x][y]),
          .axi_arregion(axi_arregion[x][y]),
          .axi_aruser(axi_aruser[x][y]),
          
          .axi_rvalid(axi_rvalid[x][y]),
          .axi_rready(axi_rready[x][y]),
          .axi_rid(axi_rid[x][y]),
          .axi_rdata(axi_rdata[x][y]),
          .axi_rresp(axi_rresp[x][y]),
          .axi_rlast(axi_rlast[x][y]),
          .axi_ruser(axi_ruser[x][y]),
          
          // Mesh interface
          .noc_flit_out_valid(mesh_local_flit_in_valid[x][y]),
          .noc_flit_out_ready(mesh_local_flit_in_ready[x][y]),
          .noc_flit_out(mesh_local_flit_in[x][y]),
          .noc_flit_in_valid(mesh_local_flit_out_valid[x][y]),
          .noc_flit_in_ready(mesh_local_flit_out_ready[x][y]),
          .noc_flit_in(mesh_local_flit_out[x][y]),
          
          // Configuration
          .global_base_addr(global_base_addr),
          .global_addr_mask(global_addr_mask),
          
          // Status and debug
          .status_reg(node_status[x][y]),
          .error_reg(node_errors[x][y]),
          .perf_counters(),
          .node_info_reg(node_info[x][y])
        );
        
      end
    end
  endgenerate

  // ============================================================================
  // SYSTEM-WIDE PERFORMANCE MONITORING
  // ============================================================================
  
  logic [31:0] total_packets_routed;
  logic [31:0] total_local_accesses;
  logic [31:0] total_remote_accesses;
  logic [31:0] total_address_errors;
  logic [31:0] max_hop_count;
  logic [31:0] avg_latency;
  logic [31:0] peak_throughput;
  logic [31:0] mesh_utilization;
  
  // Aggregate performance counters
  always_comb begin
    total_packets_routed = '0;
    total_local_accesses = '0;
    total_remote_accesses = '0;
    total_address_errors = '0;
    
    for (int i = 0; i < MESH_SIZE_X; i++) begin
      for (int j = 0; j < MESH_SIZE_Y; j++) begin
        total_packets_routed += mesh_packets_routed[i][j];
        // Additional NIU performance counters would be aggregated here
      end
    end
  end
  
  // Calculate mesh statistics
  assign max_hop_count = (MESH_SIZE_X - 1) + (MESH_SIZE_Y - 1); // Maximum Manhattan distance
  
  // System performance counter outputs
  assign system_perf_counters[0] = total_packets_routed;
  assign system_perf_counters[1] = total_local_accesses;
  assign system_perf_counters[2] = total_remote_accesses;
  assign system_perf_counters[3] = total_address_errors;
  assign system_perf_counters[4] = max_hop_count;
  assign system_perf_counters[5] = avg_latency;
  assign system_perf_counters[6] = peak_throughput;
  assign system_perf_counters[7] = mesh_utilization;
  assign system_perf_counters[8] = MESH_SIZE_X * MESH_SIZE_Y; // Total nodes
  assign system_perf_counters[9] = MESH_SIZE_X;
  assign system_perf_counters[10] = MESH_SIZE_Y;
  assign system_perf_counters[11] = '0; // Reserved
  assign system_perf_counters[12] = '0; // Reserved
  assign system_perf_counters[13] = '0; // Reserved
  assign system_perf_counters[14] = '0; // Reserved
  assign system_perf_counters[15] = '0; // Reserved

  // ============================================================================
  // SYSTEM STATUS AND ERROR AGGREGATION
  // ============================================================================
  
  logic system_error_flag;
  logic [7:0] error_node_count;
  
  always_comb begin
    system_error_flag = 1'b0;
    error_node_count = '0;
    
    for (int i = 0; i < MESH_SIZE_X; i++) begin
      for (int j = 0; j < MESH_SIZE_Y; j++) begin
        if (mesh_error_status[i][j] != ERR_NONE) begin
          system_error_flag = 1'b1;
          error_node_count += 1'b1;
        end
      end
    end
  end
  
  // System status register
  assign system_status = {
    16'h0000,                    // Reserved
    error_node_count,            // Number of nodes with errors
    4'($clog2(MESH_SIZE_X)),     // Mesh size X (log2)
    4'($clog2(MESH_SIZE_Y)),     // Mesh size Y (log2)
    2'b00,                       // Reserved
    1'b0,                        // System congestion flag
    system_error_flag            // System error flag
  };
  
  // System error register
  assign system_errors = {
    16'h0000,                    // Reserved
    total_address_errors[15:0]   // Total address errors
  };

  // ============================================================================
  // SYSTEM INITIALIZATION AND DEBUG
  // ============================================================================
  
  initial begin
    $display("Nebula System Configuration:");
    $display("  Mesh Size: %0dx%0d", MESH_SIZE_X, MESH_SIZE_Y);
    $display("  Total Nodes: %0d", MESH_SIZE_X * MESH_SIZE_Y);
    $display("  Global Base Address: 0x%016h", GLOBAL_BASE_ADDR);
    $display("  Node Address Size: 0x%016h", NODE_ADDR_SIZE);
    $display("  Max Hop Count: %0d", max_hop_count);
    
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        logic [AXI_ADDR_WIDTH-1:0] node_base = GLOBAL_BASE_ADDR + ((y * MESH_SIZE_X + x) * NODE_ADDR_SIZE);
        $display("  Node (%0d,%0d): Base Address 0x%016h", x, y, node_base);
      end
    end
  end

endmodule
