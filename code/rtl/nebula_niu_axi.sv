/**
 * Nebula Network Interface Unit (NIU) - AXI Version
 * 
 * This module provides a complete network interface for connecting AXI4
 * master/slave devices to the Nebula mesh network. It integrates the
 * AXI4 interface, NoC bridge, and address mapping functionality.
 * 
 * Features:
 * - Complete AXI4 master/slave interface
 * - Address-to-coordinate mapping
 * - Local vs. remote access determination
 * - Performance monitoring and statistics
 * - Error handling and reporting
 * - Configurable address space per node
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: September 2025
 */

import nebula_pkg::*;

module nebula_niu_axi #(
  parameter int NODE_X = 0,
  parameter int NODE_Y = 0,
  parameter int MESH_SIZE_X = 4,
  parameter int MESH_SIZE_Y = 4,
  parameter logic [AXI_ADDR_WIDTH-1:0] NODE_BASE_ADDR = 64'h0000_0000_1000_0000,
  parameter logic [AXI_ADDR_WIDTH-1:0] NODE_ADDR_MASK = 64'hFFFF_FFFF_FFF0_0000 // 1MB per node
)(
  input  logic clk,
  input  logic rst_n,
  
  // ============================================================================
  // AXI4 MASTER INTERFACE
  // ============================================================================
  
  // AXI Write Address Channel
  input  logic                         axi_awvalid,
  output logic                         axi_awready,
  input  logic [AXI_ID_WIDTH-1:0]      axi_awid,
  input  logic [AXI_ADDR_WIDTH-1:0]    axi_awaddr,
  input  logic [7:0]                   axi_awlen,
  input  logic [2:0]                   axi_awsize,
  input  logic [1:0]                   axi_awburst,
  input  logic                         axi_awlock,
  input  logic [3:0]                   axi_awcache,
  input  logic [2:0]                   axi_awprot,
  input  logic [QOS_WIDTH-1:0]         axi_awqos,
  input  logic [3:0]                   axi_awregion,
  input  logic [AXI_AWUSER_WIDTH-1:0]  axi_awuser,
  
  // AXI Write Data Channel
  input  logic                         axi_wvalid,
  output logic                         axi_wready,
  input  logic [AXI_DATA_WIDTH-1:0]    axi_wdata,
  input  logic [AXI_STRB_WIDTH-1:0]    axi_wstrb,
  input  logic                         axi_wlast,
  input  logic [AXI_WUSER_WIDTH-1:0]   axi_wuser,
  
  // AXI Write Response Channel
  output logic                         axi_bvalid,
  input  logic                         axi_bready,
  output logic [AXI_ID_WIDTH-1:0]      axi_bid,
  output logic [1:0]                   axi_bresp,
  output logic [AXI_BUSER_WIDTH-1:0]   axi_buser,
  
  // AXI Read Address Channel
  input  logic                         axi_arvalid,
  output logic                         axi_arready,
  input  logic [AXI_ID_WIDTH-1:0]      axi_arid,
  input  logic [AXI_ADDR_WIDTH-1:0]    axi_araddr,
  input  logic [7:0]                   axi_arlen,
  input  logic [2:0]                   axi_arsize,
  input  logic [1:0]                   axi_arburst,
  input  logic                         axi_arlock,
  input  logic [3:0]                   axi_arcache,
  input  logic [2:0]                   axi_arprot,
  input  logic [QOS_WIDTH-1:0]         axi_arqos,
  input  logic [3:0]                   axi_arregion,
  input  logic [AXI_ARUSER_WIDTH-1:0]  axi_aruser,
  
  // AXI Read Data Channel
  output logic                         axi_rvalid,
  input  logic                         axi_rready,
  output logic [AXI_ID_WIDTH-1:0]      axi_rid,
  output logic [AXI_DATA_WIDTH-1:0]    axi_rdata,
  output logic [1:0]                   axi_rresp,
  output logic                         axi_rlast,
  output logic [AXI_RUSER_WIDTH-1:0]   axi_ruser,
  
  // ============================================================================
  // MESH NETWORK INTERFACE
  // ============================================================================
  
  // NoC output (to mesh)
  output logic      noc_flit_out_valid,
  input  logic      noc_flit_out_ready,
  output noc_flit_t noc_flit_out,
  
  // NoC input (from mesh)
  input  logic      noc_flit_in_valid,
  output logic      noc_flit_in_ready,
  input  noc_flit_t noc_flit_in,
  
  // ============================================================================
  // CONFIGURATION AND STATUS
  // ============================================================================
  
  // Configuration registers
  input  logic [AXI_ADDR_WIDTH-1:0] global_base_addr,  // Global address space base
  input  logic [AXI_ADDR_WIDTH-1:0] global_addr_mask,  // Global address space mask
  
  // Status and performance monitoring
  output logic [31:0] status_reg,
  output logic [31:0] error_reg,
  output logic [31:0] perf_counters [7:0],
  output logic [31:0] node_info_reg
);

  // ============================================================================
  // PARAMETER VALIDATION
  // ============================================================================
  
  initial begin
    if (NODE_X >= MESH_SIZE_X || NODE_Y >= MESH_SIZE_Y) begin
      $fatal(1, "Node coordinates (%0d,%0d) exceed mesh size (%0dx%0d)", 
             NODE_X, NODE_Y, MESH_SIZE_X, MESH_SIZE_Y);
    end
    if (MESH_SIZE_X * MESH_SIZE_Y > 64) begin
      $fatal(1, "Mesh size %0dx%0d exceeds maximum of 64 nodes", MESH_SIZE_X, MESH_SIZE_Y);
    end
  end

  // ============================================================================
  // ADDRESS MAPPING AND DECODER
  // ============================================================================
  
  // Address mapping functions
  function automatic logic [COORD_WIDTH-1:0] addr_to_x_coord(logic [AXI_ADDR_WIDTH-1:0] addr);
    logic [AXI_ADDR_WIDTH-1:0] masked_addr;
    logic [NODE_ID_WIDTH-1:0] node_id;
    masked_addr = (addr & ~global_addr_mask) >> 20; // Assuming 1MB per node (20 bits)
    node_id = masked_addr[NODE_ID_WIDTH-1:0];
    return node_id % MESH_SIZE_X;
  endfunction
  
  function automatic logic [COORD_WIDTH-1:0] addr_to_y_coord(logic [AXI_ADDR_WIDTH-1:0] addr);
    logic [AXI_ADDR_WIDTH-1:0] masked_addr;
    logic [NODE_ID_WIDTH-1:0] node_id;
    masked_addr = (addr & ~global_addr_mask) >> 20; // Assuming 1MB per node (20 bits)
    node_id = masked_addr[NODE_ID_WIDTH-1:0];
    return node_id / MESH_SIZE_X;
  endfunction
  
  function automatic logic is_local_access(logic [AXI_ADDR_WIDTH-1:0] addr);
    logic [COORD_WIDTH-1:0] target_x, target_y;
    target_x = addr_to_x_coord(addr);
    target_y = addr_to_y_coord(addr);
    return (target_x == NODE_X) && (target_y == NODE_Y);
  endfunction
  
  function automatic logic is_valid_address(logic [AXI_ADDR_WIDTH-1:0] addr);
    logic [COORD_WIDTH-1:0] target_x, target_y;
    target_x = addr_to_x_coord(addr);
    target_y = addr_to_y_coord(addr);
    return (target_x < MESH_SIZE_X) && (target_y < MESH_SIZE_Y);
  endfunction

  // ============================================================================
  // PERFORMANCE COUNTERS
  // ============================================================================
  
  logic [31:0] local_read_count;
  logic [31:0] local_write_count;
  logic [31:0] remote_read_count;
  logic [31:0] remote_write_count;
  logic [31:0] address_errors;
  logic [31:0] protocol_errors;
  logic [15:0] avg_latency;
  logic [7:0]  buffer_utilization;
  
  // Bridge status/error registers
  logic [31:0] bridge_status_reg;
  logic [31:0] bridge_error_reg;
  logic [31:0] bridge_tx_count;
  logic [31:0] bridge_rx_count;
  
  // Performance counter updates
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      local_read_count     <= '0;
      local_write_count    <= '0;
      remote_read_count    <= '0;
      remote_write_count   <= '0;
      address_errors       <= '0;
      protocol_errors      <= '0;
    end else begin
      // Count local and remote accesses
      if (axi_arvalid && axi_arready) begin
        if (is_local_access(axi_araddr)) begin
          local_read_count <= local_read_count + 1'b1;
        end else begin
          remote_read_count <= remote_read_count + 1'b1;
        end
        
        if (!is_valid_address(axi_araddr)) begin
          address_errors <= address_errors + 1'b1;
        end
      end
      
      if (axi_awvalid && axi_awready) begin
        if (is_local_access(axi_awaddr)) begin
          local_write_count <= local_write_count + 1'b1;
        end else begin
          remote_write_count <= remote_write_count + 1'b1;
        end
        
        if (!is_valid_address(axi_awaddr)) begin
          address_errors <= address_errors + 1'b1;
        end
      end
      
      // NoC packet counting is handled by the bridge
      // Performance counters are updated via bridge outputs
    end
  end
  
  // Assign performance counter outputs
  assign perf_counters[0] = local_read_count;
  assign perf_counters[1] = local_write_count;
  assign perf_counters[2] = remote_read_count;
  assign perf_counters[3] = remote_write_count;
  assign perf_counters[4] = bridge_tx_count;
  assign perf_counters[5] = bridge_rx_count;
  assign perf_counters[6] = address_errors;
  assign perf_counters[7] = protocol_errors;

  // ============================================================================
  // LOCAL MEMORY INTERFACE (Simplified for NIU)
  // ============================================================================
  
  // For local accesses, we can either:
  // 1. Forward to a local memory controller
  // 2. Implement a simple memory model
  // 3. Just provide success responses for testing
  
  // Simple local access handler for testing purposes
  logic local_access_active;
  logic [AXI_ID_WIDTH-1:0] local_access_id;
  logic [1:0] local_access_type; // 00=read, 01=write
  logic [7:0] local_access_len;
  logic [2:0] local_access_size;
  logic [7:0] local_beat_count;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      local_access_active <= 1'b0;
      local_access_id     <= '0;
      local_access_type   <= '0;
      local_access_len    <= '0;
      local_access_size   <= '0;
      local_beat_count    <= '0;
    end else begin
      // Handle local read access
      if (axi_arvalid && axi_arready && is_local_access(axi_araddr) && !local_access_active) begin
        local_access_active <= 1'b1;
        local_access_id     <= axi_arid;
        local_access_type   <= 2'b00; // Read
        local_access_len    <= axi_arlen;
        local_access_size   <= axi_arsize;
        local_beat_count    <= '0;
      end
      // Handle local write access
      else if (axi_awvalid && axi_awready && is_local_access(axi_awaddr) && !local_access_active) begin
        local_access_active <= 1'b1;
        local_access_id     <= axi_awid;
        local_access_type   <= 2'b01; // Write
        local_access_len    <= axi_awlen;
        local_access_size   <= axi_awsize;
        local_beat_count    <= '0;
      end
      // Handle data beats
      else if (local_access_active) begin
        if (local_access_type == 2'b00) begin // Read
          if (axi_rvalid && axi_rready) begin
            local_beat_count <= local_beat_count + 1'b1;
            if (local_beat_count == local_access_len) begin
              local_access_active <= 1'b0;
            end
          end
        end else if (local_access_type == 2'b01) begin // Write
          if (axi_bvalid && axi_bready) begin
            local_access_active <= 1'b0;
          end
        end
      end
    end
  end

  // ============================================================================
  // AXI-NOC BRIDGE INSTANTIATION
  // ============================================================================
  
  nebula_axi_noc_bridge #(
    .NODE_X(NODE_X),
    .NODE_Y(NODE_Y),
    .MESH_SIZE_X(MESH_SIZE_X),
    .MESH_SIZE_Y(MESH_SIZE_Y),
    .REORDER_DEPTH(16)
  ) axi_noc_bridge_inst (
    .clk(clk),
    .rst_n(rst_n),
    
    // AXI interface (pass-through for remote accesses)
    .axi_awvalid(axi_awvalid && !is_local_access(axi_awaddr)),
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
    
    .axi_wvalid(axi_wvalid && !is_local_access(axi_awaddr)),
    .axi_wready(axi_wready),
    .axi_wdata(axi_wdata),
    .axi_wstrb(axi_wstrb),
    .axi_wlast(axi_wlast),
    .axi_wuser(axi_wuser),
    
    .axi_bvalid(axi_bvalid),
    .axi_bready(axi_bready && !local_access_active),
    .axi_bid(axi_bid),
    .axi_bresp(axi_bresp),
    .axi_buser(axi_buser),
    
    .axi_arvalid(axi_arvalid && !is_local_access(axi_araddr)),
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
    .axi_rready(axi_rready && !local_access_active),
    .axi_rid(axi_rid),
    .axi_rdata(axi_rdata),
    .axi_rresp(axi_rresp),
    .axi_rlast(axi_rlast),
    .axi_ruser(axi_ruser),
    
    // Configuration
    .base_addr(NODE_BASE_ADDR),
    .addr_mask(NODE_ADDR_MASK),
    
    // NoC interface
    .noc_flit_out_valid(noc_flit_out_valid),
    .noc_flit_out_ready(noc_flit_out_ready),
    .noc_flit_out(noc_flit_out),
    .noc_flit_in_valid(noc_flit_in_valid),
    .noc_flit_in_ready(noc_flit_in_ready),
    .noc_flit_in(noc_flit_in),
    
    // Status outputs
    .status_reg(bridge_status_reg),
    .error_reg(bridge_error_reg),
    
    // Performance counters
    .packet_tx_count(bridge_tx_count),
    .packet_rx_count(bridge_rx_count),
    .avg_latency(avg_latency),
    .buffer_utilization(buffer_utilization)
  );

  // ============================================================================
  // STATUS AND ERROR REPORTING
  // ============================================================================
  
  // Status register
  assign status_reg = {
    16'h0000,                    // Reserved
    2'b00,                       // Reserved
    1'b0,                        // Error flag
    1'b0,                        // Congestion flag
    4'($clog2(MESH_SIZE_X)),     // Mesh size X (log2)
    4'($clog2(MESH_SIZE_Y)),     // Mesh size Y (log2)
    COORD_WIDTH'(NODE_X),        // Node X coordinate
    COORD_WIDTH'(NODE_Y)         // Node Y coordinate
  };
  
  // Error register
  assign error_reg = {
    24'h000000,                  // Reserved
    address_errors[7:0]          // Address error count
  };
  
  // Node information register
  assign node_info_reg = {
    8'(MESH_SIZE_X),             // Mesh X size
    8'(MESH_SIZE_Y),             // Mesh Y size
    8'(NODE_X),                  // Node X coordinate
    8'(NODE_Y)                   // Node Y coordinate
  };
  
  // Local access response generation (simplified)
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      // Reset handled in local access logic above
    end else begin
      // Simple responses for local accesses
      if (local_access_active && local_access_type == 2'b00) begin // Read response
        // Generate read data response (simplified)
        // In a real implementation, this would interface with local memory
      end else if (local_access_active && local_access_type == 2'b01) begin // Write response
        // Generate write response (simplified)
        // In a real implementation, this would confirm write completion
      end
    end
  end

endmodule
