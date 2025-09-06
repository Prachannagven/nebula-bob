// =============================================================================
// NEBULA TOP-LEVEL SYSTEM INTEGRATION MODULE (SIMPLIFIED VERSION)
// =============================================================================

`timescale 1ns / 1ps

import nebula_pkg::*;

module nebula_top #(
  parameter int MESH_WIDTH = 4,
  parameter int MESH_HEIGHT = 4,
  parameter int NUM_NODES = MESH_WIDTH * MESH_HEIGHT
)(
  input  logic        clk,
  input  logic        rst_n,
  
  // Simple external interfaces for testing
  output logic [31:0] status_reg,
  output logic [31:0] perf_counter,
  output logic        system_ready
);

  // Internal mesh signals
  logic [NUM_NODES-1:0][NUM_PORTS-1:0]      mesh_flit_in_valid;
  noc_flit_t [NUM_NODES-1:0][NUM_PORTS-1:0] mesh_flit_in;
  logic [NUM_NODES-1:0][NUM_PORTS-1:0]      mesh_flit_in_ready;
  
  logic [NUM_NODES-1:0][NUM_PORTS-1:0]      mesh_flit_out_valid;
  noc_flit_t [NUM_NODES-1:0][NUM_PORTS-1:0] mesh_flit_out;
  logic [NUM_NODES-1:0][NUM_PORTS-1:0]      mesh_flit_out_ready;

  // Performance monitoring
  logic [NUM_NODES-1:0][31:0] node_packets_routed;
  error_code_e [NUM_NODES-1:0] node_error_status;

  // Generate mesh nodes
  genvar g_node;
  generate
    for (g_node = 0; g_node < NUM_NODES; g_node++) begin : gen_mesh_nodes
      
      localparam int NODE_X = g_node % MESH_WIDTH;
      localparam int NODE_Y = g_node / MESH_WIDTH;
      
      // Router instance
      nebula_router #(
        .ROUTER_X(NODE_X),
        .ROUTER_Y(NODE_Y),
        .MESH_SIZE_X(MESH_WIDTH),
        .MESH_SIZE_Y(MESH_HEIGHT)
      ) router_inst (
        .clk(clk),
        .rst_n(rst_n),
        .flit_in_valid(mesh_flit_in_valid[g_node]),
        .flit_in(mesh_flit_in[g_node]),
        .flit_in_ready(mesh_flit_in_ready[g_node]),
        .flit_out_valid(mesh_flit_out_valid[g_node]),
        .flit_out(mesh_flit_out[g_node]),
        .flit_out_ready(mesh_flit_out_ready[g_node]),
        .vc_status(),
        .packets_routed(node_packets_routed[g_node]),
        .error_status(node_error_status[g_node])
      );
      
    end
  endgenerate
  
  // Simple mesh interconnection
  genvar g_x, g_y;
  generate
    for (g_y = 0; g_y < MESH_HEIGHT; g_y++) begin : gen_mesh_y
      for (g_x = 0; g_x < MESH_WIDTH; g_x++) begin : gen_mesh_x
        
        localparam int CURRENT_NODE = g_y * MESH_WIDTH + g_x;
        
        // Connect neighbors with boundary handling
        if (g_y > 0) begin : gen_north
          localparam int NORTH_NODE = (g_y - 1) * MESH_WIDTH + g_x;
          assign mesh_flit_in_valid[CURRENT_NODE][PORT_NORTH] = mesh_flit_out_valid[NORTH_NODE][PORT_SOUTH];
          assign mesh_flit_in[CURRENT_NODE][PORT_NORTH] = mesh_flit_out[NORTH_NODE][PORT_SOUTH];
          assign mesh_flit_out_ready[NORTH_NODE][PORT_SOUTH] = mesh_flit_in_ready[CURRENT_NODE][PORT_NORTH];
        end else begin
          assign mesh_flit_in_valid[CURRENT_NODE][PORT_NORTH] = 1'b0;
          assign mesh_flit_in[CURRENT_NODE][PORT_NORTH] = '0;
        end
        
        if (g_y < MESH_HEIGHT - 1) begin : gen_south
          localparam int SOUTH_NODE = (g_y + 1) * MESH_WIDTH + g_x;
          assign mesh_flit_in_valid[CURRENT_NODE][PORT_SOUTH] = mesh_flit_out_valid[SOUTH_NODE][PORT_NORTH];
          assign mesh_flit_in[CURRENT_NODE][PORT_SOUTH] = mesh_flit_out[SOUTH_NODE][PORT_NORTH];
          assign mesh_flit_out_ready[SOUTH_NODE][PORT_NORTH] = mesh_flit_in_ready[CURRENT_NODE][PORT_SOUTH];
        end else begin
          assign mesh_flit_in_valid[CURRENT_NODE][PORT_SOUTH] = 1'b0;
          assign mesh_flit_in[CURRENT_NODE][PORT_SOUTH] = '0;
        end
        
        if (g_x > 0) begin : gen_west
          localparam int WEST_NODE = g_y * MESH_WIDTH + (g_x - 1);
          assign mesh_flit_in_valid[CURRENT_NODE][PORT_WEST] = mesh_flit_out_valid[WEST_NODE][PORT_EAST];
          assign mesh_flit_in[CURRENT_NODE][PORT_WEST] = mesh_flit_out[WEST_NODE][PORT_EAST];
          assign mesh_flit_out_ready[WEST_NODE][PORT_EAST] = mesh_flit_in_ready[CURRENT_NODE][PORT_WEST];
        end else begin
          assign mesh_flit_in_valid[CURRENT_NODE][PORT_WEST] = 1'b0;
          assign mesh_flit_in[CURRENT_NODE][PORT_WEST] = '0;
        end
        
        if (g_x < MESH_WIDTH - 1) begin : gen_east
          localparam int EAST_NODE = g_y * MESH_WIDTH + (g_x + 1);
          assign mesh_flit_in_valid[CURRENT_NODE][PORT_EAST] = mesh_flit_out_valid[EAST_NODE][PORT_WEST];
          assign mesh_flit_in[CURRENT_NODE][PORT_EAST] = mesh_flit_out[EAST_NODE][PORT_WEST];
          assign mesh_flit_out_ready[EAST_NODE][PORT_WEST] = mesh_flit_in_ready[CURRENT_NODE][PORT_EAST];
        end else begin
          assign mesh_flit_in_valid[CURRENT_NODE][PORT_EAST] = 1'b0;
          assign mesh_flit_in[CURRENT_NODE][PORT_EAST] = '0;
        end
        
        // Local port handling (simplified - no NIU connection for now)
        assign mesh_flit_in_valid[CURRENT_NODE][PORT_LOCAL] = 1'b0;
        assign mesh_flit_in[CURRENT_NODE][PORT_LOCAL] = '0;
        assign mesh_flit_out_ready[CURRENT_NODE][PORT_LOCAL] = 1'b1;
        
        // Boundary ready signals
        if (g_y == 0) assign mesh_flit_out_ready[CURRENT_NODE][PORT_NORTH] = 1'b1;
        if (g_y == MESH_HEIGHT - 1) assign mesh_flit_out_ready[CURRENT_NODE][PORT_SOUTH] = 1'b1;
        if (g_x == 0) assign mesh_flit_out_ready[CURRENT_NODE][PORT_WEST] = 1'b1;
        if (g_x == MESH_WIDTH - 1) assign mesh_flit_out_ready[CURRENT_NODE][PORT_EAST] = 1'b1;
        
      end
    end
  endgenerate
  
  // System monitoring
  always_comb begin
    perf_counter = '0;
    for (int i = 0; i < NUM_NODES; i++) begin
      perf_counter += node_packets_routed[i];
    end
  end
  
  always_comb begin
    status_reg = '0;
    status_reg[0] = rst_n;
    status_reg[1] = 1'b1;  // System operational
    status_reg[15:8] = NUM_NODES[7:0];
  end
  
  assign system_ready = rst_n;
  
  // Basic assertions
  initial begin
    assert (MESH_WIDTH >= 2 && MESH_WIDTH <= 8) 
      else $fatal(1, "MESH_WIDTH must be between 2 and 8");
    assert (MESH_HEIGHT >= 2 && MESH_HEIGHT <= 8) 
      else $fatal(1, "MESH_HEIGHT must be between 2 and 8");
  end

endmodule
