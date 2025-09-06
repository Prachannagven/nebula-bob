`timescale 1ns / 1ps
//==============================================================================
// Nebula Top-Level System Integration
//
// This module integrates the complete Nebula GPU interconnect system including:
// - Mesh network topology with configurable grid size
// - AXI4 and CHI protocol interfaces at each node
// - Configuration register interface for system control
// - Performance monitoring and error reporting
// - Clock and reset distribution
//
// Features:
// - Parameterizable mesh size (2x2 to 8x8)
// - Unified configuration interface
// - System-wide performance monitoring
// - Error aggregation and reporting
// - Debug and trace interfaces
//==============================================================================

import nebula_pkg::*;

module nebula_top #(
  parameter int MESH_WIDTH = 4,                 // Mesh width (number of columns)
  parameter int MESH_HEIGHT = 4,               // Mesh height (number of rows)
  parameter int NUM_NODES = MESH_WIDTH * MESH_HEIGHT,
  parameter int NODE_ID_WIDTH = $clog2(NUM_NODES),
  parameter int CONFIG_ADDR_WIDTH = 16,        // Configuration register address width
  parameter int CONFIG_DATA_WIDTH = 32,        // Configuration register data width
  parameter bit ENABLE_AXI = 1'b1,            // Enable AXI interfaces
  parameter bit ENABLE_CHI = 1'b1,            // Enable CHI interfaces
  parameter bit ENABLE_PERFORMANCE_MONITORING = 1'b1
)(
  // Clock and Reset
  input  logic clk,
  input  logic rst_n,
  
  // System Configuration Interface
  input  logic                           config_req_valid,
  output logic                           config_req_ready,
  input  logic [CONFIG_ADDR_WIDTH-1:0]  config_req_addr,
  input  logic [CONFIG_DATA_WIDTH-1:0]  config_req_data,
  input  logic                           config_req_write,
  
  output logic                           config_resp_valid,
  input  logic                           config_resp_ready,
  output logic [CONFIG_DATA_WIDTH-1:0]  config_resp_data,
  output logic                           config_resp_error,
  
  // External Memory Interfaces (one per node)
  output logic [NUM_NODES-1:0]                     mem_req_valid,
  input  logic [NUM_NODES-1:0]                     mem_req_ready,
  output logic [NUM_NODES-1:0][CHI_REQ_ADDR_WIDTH-1:0] mem_req_addr,
  output logic [NUM_NODES-1:0]                     mem_req_write,
  output logic [NUM_NODES-1:0][CHI_DATA_WIDTH-1:0] mem_req_data,
  output logic [NUM_NODES-1:0][CHI_BE_WIDTH-1:0]   mem_req_be,
  
  input  logic [NUM_NODES-1:0]                     mem_resp_valid,
  output logic [NUM_NODES-1:0]                     mem_resp_ready,
  input  logic [NUM_NODES-1:0][CHI_DATA_WIDTH-1:0] mem_resp_data,
  input  logic [NUM_NODES-1:0]                     mem_resp_error,
  
  // External AXI Interfaces (one per node, if enabled)
  input  logic [NUM_NODES-1:0]                     axi_aw_valid,
  output logic [NUM_NODES-1:0]                     axi_aw_ready,
  input  axi_aw_t [NUM_NODES-1:0]                  axi_aw,
  
  input  logic [NUM_NODES-1:0]                     axi_w_valid,
  output logic [NUM_NODES-1:0]                     axi_w_ready,
  input  axi_w_t [NUM_NODES-1:0]                   axi_w,
  
  output logic [NUM_NODES-1:0]                     axi_b_valid,
  input  logic [NUM_NODES-1:0]                     axi_b_ready,
  output axi_b_t [NUM_NODES-1:0]                   axi_b,
  
  input  logic [NUM_NODES-1:0]                     axi_ar_valid,
  output logic [NUM_NODES-1:0]                     axi_ar_ready,
  input  axi_ar_t [NUM_NODES-1:0]                  axi_ar,
  
  output logic [NUM_NODES-1:0]                     axi_r_valid,
  input  logic [NUM_NODES-1:0]                     axi_r_ready,
  output axi_r_t [NUM_NODES-1:0]                   axi_r,
  
  // External CHI Interfaces (one per node, if enabled)
  input  logic [NUM_NODES-1:0]                     chi_req_valid,
  output logic [NUM_NODES-1:0]                     chi_req_ready,
  input  chi_req_t [NUM_NODES-1:0]                 chi_req,
  
  output logic [NUM_NODES-1:0]                     chi_resp_valid,
  input  logic [NUM_NODES-1:0]                     chi_resp_ready,
  output chi_resp_t [NUM_NODES-1:0]                chi_resp,
  
  input  logic [NUM_NODES-1:0]                     chi_dat_req_valid,
  output logic [NUM_NODES-1:0]                     chi_dat_req_ready,
  input  chi_data_t [NUM_NODES-1:0]                chi_dat_req,
  
  output logic [NUM_NODES-1:0]                     chi_dat_resp_valid,
  input  logic [NUM_NODES-1:0]                     chi_dat_resp_ready,
  output chi_data_t [NUM_NODES-1:0]                chi_dat_resp,
  
  // System Status and Debug
  output logic [31:0]                              system_status,
  output logic [31:0]                              error_status,
  output logic [31:0]                              performance_counters [15:0],
  
  // Debug and Trace Interface
  output logic                                     debug_trace_valid,
  output logic [63:0]                             debug_trace_data,
  output logic [7:0]                              debug_trace_node_id
);

  // ============================================================================
  // INTERNAL SIGNALS AND PARAMETERS
  // ============================================================================
  
  localparam int COORD_WIDTH = $clog2(MESH_WIDTH > MESH_HEIGHT ? MESH_WIDTH : MESH_HEIGHT);
  
  // Node coordinate calculation
  function automatic logic [COORD_WIDTH-1:0] get_x_coord(input int node_id);
    return node_id % MESH_WIDTH;
  endfunction
  
  function automatic logic [COORD_WIDTH-1:0] get_y_coord(input int node_id);
    return node_id / MESH_WIDTH;
  endfunction
  
  // Mesh network interconnect signals
  noc_flit_t mesh_flit_out [NUM_NODES-1:0][NOC_NUM_PORTS-1:0];
  logic      mesh_valid_out [NUM_NODES-1:0][NOC_NUM_PORTS-1:0];
  logic      mesh_ready_out [NUM_NODES-1:0][NOC_NUM_PORTS-1:0];
  
  noc_flit_t mesh_flit_in [NUM_NODES-1:0][NOC_NUM_PORTS-1:0];
  logic      mesh_valid_in [NUM_NODES-1:0][NOC_NUM_PORTS-1:0];
  logic      mesh_ready_in [NUM_NODES-1:0][NOC_NUM_PORTS-1:0];
  
  // Configuration registers
  logic [CONFIG_DATA_WIDTH-1:0] config_regs [256]; // 256 configuration registers
  logic config_write_enable;
  logic [7:0] config_reg_addr;
  
  // Performance monitoring
  logic [31:0] node_performance_counters [NUM_NODES-1:0][4:0];
  logic [31:0] total_packets_sent;
  logic [31:0] total_packets_received;
  logic [31:0] total_axi_transactions;
  logic [31:0] total_chi_transactions;
  
  // Error status aggregation
  logic [NUM_NODES-1:0] node_errors;
  logic [NUM_NODES-1:0] router_errors;
  logic [NUM_NODES-1:0] protocol_errors;
  
  // ============================================================================
  // MESH NETWORK INSTANTIATION
  // ============================================================================
  
  generate
    for (genvar i = 0; i < NUM_NODES; i++) begin : gen_nodes
      
      // Calculate node coordinates
      localparam logic [COORD_WIDTH-1:0] NODE_X = get_x_coord(i);
      localparam logic [COORD_WIDTH-1:0] NODE_Y = get_y_coord(i);
      
      // Router instance
      nebula_router #(
        .ROUTER_ID(i),
        .X_COORD(NODE_X),
        .Y_COORD(NODE_Y),
        .MESH_WIDTH(MESH_WIDTH),
        .MESH_HEIGHT(MESH_HEIGHT)
      ) router_inst (
        .clk(clk),
        .rst_n(rst_n),
        
        // Input ports [N, S, E, W, Local]
        .flit_in(mesh_flit_in[i]),
        .valid_in(mesh_valid_in[i]),
        .ready_in(mesh_ready_in[i]),
        
        // Output ports [N, S, E, W, Local]
        .flit_out(mesh_flit_out[i]),
        .valid_out(mesh_valid_out[i]),
        .ready_out(mesh_ready_out[i]),
        
        // Performance monitoring
        .performance_counters(node_performance_counters[i]),
        .error_status(router_errors[i])
      );
      
      // Network Interface Unit (NIU) - connects protocols to local router port
      if (ENABLE_AXI || ENABLE_CHI) begin : gen_niu
        nebula_niu_axi #(
          .NODE_ID(i),
          .X_COORD(NODE_X),
          .Y_COORD(NODE_Y),
          .ENABLE_AXI(ENABLE_AXI),
          .ENABLE_CHI(ENABLE_CHI)
        ) niu_inst (
          .clk(clk),
          .rst_n(rst_n),
          
          // Local router interface (Local port of router)
          .noc_flit_out(mesh_flit_in[i][NOC_PORT_LOCAL]),
          .noc_valid_out(mesh_valid_in[i][NOC_PORT_LOCAL]),
          .noc_ready_out(mesh_ready_in[i][NOC_PORT_LOCAL]),
          
          .noc_flit_in(mesh_flit_out[i][NOC_PORT_LOCAL]),
          .noc_valid_in(mesh_valid_out[i][NOC_PORT_LOCAL]),
          .noc_ready_in(mesh_ready_out[i][NOC_PORT_LOCAL]),
          
          // External AXI interface
          .axi_aw_valid(axi_aw_valid[i]),
          .axi_aw_ready(axi_aw_ready[i]),
          .axi_aw(axi_aw[i]),
          
          .axi_w_valid(axi_w_valid[i]),
          .axi_w_ready(axi_w_ready[i]),
          .axi_w(axi_w[i]),
          
          .axi_b_valid(axi_b_valid[i]),
          .axi_b_ready(axi_b_ready[i]),
          .axi_b(axi_b[i]),
          
          .axi_ar_valid(axi_ar_valid[i]),
          .axi_ar_ready(axi_ar_ready[i]),
          .axi_ar(axi_ar[i]),
          
          .axi_r_valid(axi_r_valid[i]),
          .axi_r_ready(axi_r_ready[i]),
          .axi_r(axi_r[i]),
          
          // External CHI interface
          .chi_req_valid(chi_req_valid[i]),
          .chi_req_ready(chi_req_ready[i]),
          .chi_req(chi_req[i]),
          
          .chi_resp_valid(chi_resp_valid[i]),
          .chi_resp_ready(chi_resp_ready[i]),
          .chi_resp(chi_resp[i]),
          
          .chi_dat_req_valid(chi_dat_req_valid[i]),
          .chi_dat_req_ready(chi_dat_req_ready[i]),
          .chi_dat_req(chi_dat_req[i]),
          
          .chi_dat_resp_valid(chi_dat_resp_valid[i]),
          .chi_dat_resp_ready(chi_dat_resp_ready[i]),
          .chi_dat_resp(chi_dat_resp[i]),
          
          // Memory interface
          .mem_req_valid(mem_req_valid[i]),
          .mem_req_ready(mem_req_ready[i]),
          .mem_req_addr(mem_req_addr[i]),
          .mem_req_write(mem_req_write[i]),
          .mem_req_data(mem_req_data[i]),
          .mem_req_be(mem_req_be[i]),
          
          .mem_resp_valid(mem_resp_valid[i]),
          .mem_resp_ready(mem_resp_ready[i]),
          .mem_resp_data(mem_resp_data[i]),
          .mem_resp_error(mem_resp_error[i]),
          
          // Status and errors
          .protocol_error(protocol_errors[i])
        );
      end else begin : gen_no_niu
        // Tie off unused signals when NIU is disabled
        assign mesh_flit_in[i][NOC_PORT_LOCAL] = '0;
        assign mesh_valid_in[i][NOC_PORT_LOCAL] = 1'b0;
        assign mesh_ready_out[i][NOC_PORT_LOCAL] = 1'b1;
        assign protocol_errors[i] = 1'b0;
      end
    end
  endgenerate
  
  // ============================================================================
  // MESH INTERCONNECTION
  // ============================================================================
  
  generate
    for (genvar i = 0; i < NUM_NODES; i++) begin : gen_mesh_connections
      
      localparam int NODE_X = get_x_coord(i);
      localparam int NODE_Y = get_y_coord(i);
      
      // North connection
      if (NODE_Y > 0) begin : gen_north_connection
        localparam int NORTH_NODE = (NODE_Y - 1) * MESH_WIDTH + NODE_X;
        assign mesh_flit_in[i][NOC_PORT_NORTH] = mesh_flit_out[NORTH_NODE][NOC_PORT_SOUTH];
        assign mesh_valid_in[i][NOC_PORT_NORTH] = mesh_valid_out[NORTH_NODE][NOC_PORT_SOUTH];
        assign mesh_ready_out[NORTH_NODE][NOC_PORT_SOUTH] = mesh_ready_in[i][NOC_PORT_NORTH];
      end else begin : gen_north_tie_off
        assign mesh_flit_in[i][NOC_PORT_NORTH] = '0;
        assign mesh_valid_in[i][NOC_PORT_NORTH] = 1'b0;
      end
      
      // South connection
      if (NODE_Y < MESH_HEIGHT - 1) begin : gen_south_connection
        localparam int SOUTH_NODE = (NODE_Y + 1) * MESH_WIDTH + NODE_X;
        assign mesh_flit_in[i][NOC_PORT_SOUTH] = mesh_flit_out[SOUTH_NODE][NOC_PORT_NORTH];
        assign mesh_valid_in[i][NOC_PORT_SOUTH] = mesh_valid_out[SOUTH_NODE][NOC_PORT_NORTH];
        assign mesh_ready_out[SOUTH_NODE][NOC_PORT_NORTH] = mesh_ready_in[i][NOC_PORT_SOUTH];
      end else begin : gen_south_tie_off
        assign mesh_flit_in[i][NOC_PORT_SOUTH] = '0;
        assign mesh_valid_in[i][NOC_PORT_SOUTH] = 1'b0;
      end
      
      // East connection
      if (NODE_X < MESH_WIDTH - 1) begin : gen_east_connection
        localparam int EAST_NODE = NODE_Y * MESH_WIDTH + NODE_X + 1;
        assign mesh_flit_in[i][NOC_PORT_EAST] = mesh_flit_out[EAST_NODE][NOC_PORT_WEST];
        assign mesh_valid_in[i][NOC_PORT_EAST] = mesh_valid_out[EAST_NODE][NOC_PORT_WEST];
        assign mesh_ready_out[EAST_NODE][NOC_PORT_WEST] = mesh_ready_in[i][NOC_PORT_EAST];
      end else begin : gen_east_tie_off
        assign mesh_flit_in[i][NOC_PORT_EAST] = '0;
        assign mesh_valid_in[i][NOC_PORT_EAST] = 1'b0;
      end
      
      // West connection
      if (NODE_X > 0) begin : gen_west_connection
        localparam int WEST_NODE = NODE_Y * MESH_WIDTH + NODE_X - 1;
        assign mesh_flit_in[i][NOC_PORT_WEST] = mesh_flit_out[WEST_NODE][NOC_PORT_EAST];
        assign mesh_valid_in[i][NOC_PORT_WEST] = mesh_valid_out[WEST_NODE][NOC_PORT_EAST];
        assign mesh_ready_out[WEST_NODE][NOC_PORT_EAST] = mesh_ready_in[i][NOC_PORT_WEST];
      end else begin : gen_west_tie_off
        assign mesh_flit_in[i][NOC_PORT_WEST] = '0;
        assign mesh_valid_in[i][NOC_PORT_WEST] = 1'b0;
      end
      
      // Handle unused ready signals (edge nodes)
      if (NODE_Y == 0) assign mesh_ready_out[i][NOC_PORT_NORTH] = 1'b1;
      if (NODE_Y == MESH_HEIGHT - 1) assign mesh_ready_out[i][NOC_PORT_SOUTH] = 1'b1;
      if (NODE_X == 0) assign mesh_ready_out[i][NOC_PORT_WEST] = 1'b1;
      if (NODE_X == MESH_WIDTH - 1) assign mesh_ready_out[i][NOC_PORT_EAST] = 1'b1;
    end
  endgenerate
  
  // ============================================================================
  // CONFIGURATION REGISTER INTERFACE
  // ============================================================================
  
  assign config_write_enable = config_req_valid && config_req_ready && config_req_write;
  assign config_reg_addr = config_req_addr[7:0]; // Use lower 8 bits for register address
  
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      config_resp_valid <= 1'b0;
      config_resp_data <= '0;
      config_resp_error <= 1'b0;
      
      // Initialize configuration registers
      for (int i = 0; i < 256; i++) begin
        config_regs[i] <= '0;
      end
      
      // Set default configuration values
      config_regs[0] <= {16'h0000, 8'(MESH_HEIGHT), 8'(MESH_WIDTH)}; // System topology
      config_regs[1] <= {31'h0, ENABLE_CHI}; // CHI enable
      config_regs[2] <= {31'h0, ENABLE_AXI}; // AXI enable
      config_regs[3] <= NUM_NODES; // Total nodes
      
    end else begin
      
      // Handle configuration requests
      if (config_req_valid && config_req_ready) begin
        if (config_req_write) begin
          // Write operation
          if (config_reg_addr >= 16) begin // Registers 0-15 are read-only
            config_regs[config_reg_addr] <= config_req_data;
            config_resp_error <= 1'b0;
          end else begin
            config_resp_error <= 1'b1; // Attempt to write read-only register
          end
          config_resp_data <= '0;
        end else begin
          // Read operation
          config_resp_data <= config_regs[config_reg_addr];
          config_resp_error <= 1'b0;
        end
        config_resp_valid <= 1'b1;
      end else if (config_resp_valid && config_resp_ready) begin
        config_resp_valid <= 1'b0;
      end
    end
  end
  
  assign config_req_ready = !config_resp_valid || config_resp_ready;
  
  // ============================================================================
  // PERFORMANCE MONITORING
  // ============================================================================
  
  generate
    if (ENABLE_PERFORMANCE_MONITORING) begin : gen_performance_monitoring
      
      // Aggregate performance counters from all nodes
      always_ff @(posedge clk) begin
        if (!rst_n) begin
          total_packets_sent <= '0;
          total_packets_received <= '0;
          total_axi_transactions <= '0;
          total_chi_transactions <= '0;
        end else begin
          // Update every 1000 cycles to avoid overflow
          if ($time % 1000 == 0) begin
            total_packets_sent <= '0;
            total_packets_received <= '0;
            total_axi_transactions <= '0;
            total_chi_transactions <= '0;
            
            for (int i = 0; i < NUM_NODES; i++) begin
              total_packets_sent <= total_packets_sent + node_performance_counters[i][0];
              total_packets_received <= total_packets_received + node_performance_counters[i][1];
              total_axi_transactions <= total_axi_transactions + node_performance_counters[i][2];
              total_chi_transactions <= total_chi_transactions + node_performance_counters[i][3];
            end
          end
        end
      end
      
      // Export performance counters
      assign performance_counters[0] = total_packets_sent;
      assign performance_counters[1] = total_packets_received;
      assign performance_counters[2] = total_axi_transactions;
      assign performance_counters[3] = total_chi_transactions;
      assign performance_counters[4] = NUM_NODES;
      assign performance_counters[5] = MESH_WIDTH;
      assign performance_counters[6] = MESH_HEIGHT;
      assign performance_counters[7] = {31'h0, ENABLE_AXI};
      assign performance_counters[8] = {31'h0, ENABLE_CHI};
      
      // Remaining counters reserved for future use
      for (genvar i = 9; i < 16; i++) begin
        assign performance_counters[i] = '0;
      end
      
    end else begin : gen_no_performance_monitoring
      for (genvar i = 0; i < 16; i++) begin
        assign performance_counters[i] = '0;
      end
    end
  endgenerate
  
  // ============================================================================
  // ERROR AGGREGATION AND STATUS
  // ============================================================================
  
  // Aggregate errors from all nodes
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      node_errors <= '0;
    end else begin
      node_errors <= router_errors | protocol_errors;
    end
  end
  
  // System status register
  assign system_status = {
    16'h5A5A,                    // Magic number for system identification
    4'h0,                        // Reserved
    4'(MESH_HEIGHT),             // Mesh height
    4'(MESH_WIDTH),              // Mesh width  
    1'b0,                        // Reserved
    ENABLE_CHI,                  // CHI enabled
    ENABLE_AXI,                  // AXI enabled
    1'b1                         // System ready
  };
  
  // Error status register
  assign error_status = {
    16'h0,                       // Reserved
    |protocol_errors,            // Any protocol errors
    |router_errors,              // Any router errors
    |node_errors,                // Any node errors
    13'h0                        // Reserved
  };
  
  // ============================================================================
  // DEBUG AND TRACE INTERFACE
  // ============================================================================
  
  // Simple debug trace: capture first valid transaction per cycle
  logic [NODE_ID_WIDTH-1:0] trace_node_id;
  logic [63:0] trace_data;
  logic trace_valid;
  
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      trace_valid <= 1'b0;
      trace_node_id <= '0;
      trace_data <= '0;
    end else begin
      trace_valid <= 1'b0;
      
      // Find first node with valid outgoing traffic
      for (int i = 0; i < NUM_NODES; i++) begin
        if (mesh_valid_out[i][NOC_PORT_LOCAL] && mesh_ready_out[i][NOC_PORT_LOCAL] && !trace_valid) begin
          trace_valid <= 1'b1;
          trace_node_id <= i[NODE_ID_WIDTH-1:0];
          trace_data <= {mesh_flit_out[i][NOC_PORT_LOCAL].header, mesh_flit_out[i][NOC_PORT_LOCAL].payload[31:0]};
        end
      end
    end
  end
  
  assign debug_trace_valid = trace_valid;
  assign debug_trace_data = trace_data;
  assign debug_trace_node_id = {{8-NODE_ID_WIDTH{1'b0}}, trace_node_id};
  
  // ============================================================================
  // ASSERTIONS AND VERIFICATION
  // ============================================================================
  
  // Ensure mesh parameters are valid
  initial begin
    assert (MESH_WIDTH >= 2 && MESH_WIDTH <= 8) 
      else $fatal("MESH_WIDTH must be between 2 and 8");
    assert (MESH_HEIGHT >= 2 && MESH_HEIGHT <= 8) 
      else $fatal("MESH_HEIGHT must be between 2 and 8");
    assert (NUM_NODES == MESH_WIDTH * MESH_HEIGHT) 
      else $fatal("NUM_NODES must equal MESH_WIDTH * MESH_HEIGHT");
  end
  
  // Runtime assertions
  generate
    for (genvar i = 0; i < NUM_NODES; i++) begin : gen_assertions
      // Ensure no node has conflicting ready/valid signals
      always @(posedge clk) begin
        if (rst_n) begin
          for (int p = 0; p < NOC_NUM_PORTS; p++) begin
            assert (!(mesh_valid_out[i][p] && !mesh_ready_in[i][p] && mesh_ready_out[i][p]))
              else $error("Node %0d port %0d: invalid ready/valid combination", i, p);
          end
        end
      end
    end
  endgenerate

endmodule
