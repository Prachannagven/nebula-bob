/**
 * Nebula Mesh Topology Generator
 * 
 * This module instantiates a parameterizable mesh network of NoC routers
 * with proper interconnections between neighboring routers. It supports
 * edge/corner router handling and provides a scalable mesh infrastructure.
 * 
 * Features:
 * - Parameterizable grid size (2x2 to 8x8)
 * - Automatic router interconnection
 * - Edge/corner router handling (fewer connections)
 * - Local port access for each node
 * - Hierarchical clustering support for large systems
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: September 2025
 */

import nebula_pkg::*;

module nebula_mesh_top #(
  parameter int MESH_SIZE_X = 8,
  parameter int MESH_SIZE_Y = 8
)(
  input  logic clk,
  input  logic rst_n,
  
  // Local port interfaces (one per node)
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         local_flit_in_valid,
  input  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]    local_flit_in,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         local_flit_in_ready,
  
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         local_flit_out_valid,
  output noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]    local_flit_out,
  input  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         local_flit_out_ready,
  
  // Debug and performance monitoring
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0][NUM_VCS-1:0] vc_status,
  output logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][PERF_COUNTER_WIDTH-1:0] packets_routed,
  output error_code_e [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] error_status
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
  end

  // ============================================================================
  // INTERNAL MESH INTERCONNECTION SIGNALS
  // ============================================================================
  
  // Router port connections [x][y][port_id]
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0]         router_flit_in_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0]    router_flit_in;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0]         router_flit_in_ready;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0]         router_flit_out_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0]    router_flit_out;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0]         router_flit_out_ready;

  // ============================================================================
  // ROUTER MESH INSTANTIATION
  // ============================================================================
  
  genvar x, y;
  generate
    for (x = 0; x < MESH_SIZE_X; x++) begin : gen_router_x
      for (y = 0; y < MESH_SIZE_Y; y++) begin : gen_router_y
        
        nebula_router #(
          .ROUTER_X(x),
          .ROUTER_Y(y),
          .MESH_SIZE_X(MESH_SIZE_X),
          .MESH_SIZE_Y(MESH_SIZE_Y)
        ) router_inst (
          .clk(clk),
          .rst_n(rst_n),
          
          // Router port connections
          .flit_in_valid(router_flit_in_valid[x][y]),
          .flit_in(router_flit_in[x][y]),
          .flit_in_ready(router_flit_in_ready[x][y]),
          .flit_out_valid(router_flit_out_valid[x][y]),
          .flit_out(router_flit_out[x][y]),
          .flit_out_ready(router_flit_out_ready[x][y]),
          
          // Debug and status
          .vc_status(vc_status[x][y]),
          .packets_routed(packets_routed[x][y]),
          .error_status(error_status[x][y])
        );
        
      end
    end
  endgenerate

  // ============================================================================
  // MESH INTERCONNECTION LOGIC
  // ============================================================================
  
  generate
    for (x = 0; x < MESH_SIZE_X; x++) begin : interconnect_x
      for (y = 0; y < MESH_SIZE_Y; y++) begin : interconnect_y
        
        // ========================================================================
        // NORTH CONNECTIONS (Y+1 direction)
        // ========================================================================
        if (y < MESH_SIZE_Y - 1) begin : north_connection
          // Connect this router's north port to the router above's south port
          assign router_flit_in_valid[x][y+1][PORT_SOUTH] = router_flit_out_valid[x][y][PORT_NORTH];
          assign router_flit_in[x][y+1][PORT_SOUTH] = router_flit_out[x][y][PORT_NORTH];
          assign router_flit_out_ready[x][y][PORT_NORTH] = router_flit_in_ready[x][y+1][PORT_SOUTH];
        end else begin : north_edge
          // Edge router - no north connection
          assign router_flit_in_valid[x][y][PORT_NORTH] = 1'b0;
          assign router_flit_in[x][y][PORT_NORTH] = '0;
          // Edge ports act as sinks - always ready to accept flits
          assign router_flit_out_ready[x][y][PORT_NORTH] = 1'b1;
        end
        
        // ========================================================================
        // SOUTH CONNECTIONS (Y-1 direction)
        // ========================================================================
        if (y > 0) begin : south_connection
          // Connect this router's south port to the router below's north port
          assign router_flit_in_valid[x][y-1][PORT_NORTH] = router_flit_out_valid[x][y][PORT_SOUTH];
          assign router_flit_in[x][y-1][PORT_NORTH] = router_flit_out[x][y][PORT_SOUTH];
          assign router_flit_out_ready[x][y][PORT_SOUTH] = router_flit_in_ready[x][y-1][PORT_NORTH];
        end else begin : south_edge
          // Edge router - no south connection
          assign router_flit_in_valid[x][y][PORT_SOUTH] = 1'b0;
          assign router_flit_in[x][y][PORT_SOUTH] = '0;
          // Edge ports act as sinks - always ready to accept flits
          assign router_flit_out_ready[x][y][PORT_SOUTH] = 1'b1;
        end
        
        // ========================================================================
        // EAST CONNECTIONS (X+1 direction)
        // ========================================================================
        if (x < MESH_SIZE_X - 1) begin : east_connection
          // Connect this router's east port to the router to the right's west port
          assign router_flit_in_valid[x+1][y][PORT_WEST] = router_flit_out_valid[x][y][PORT_EAST];
          assign router_flit_in[x+1][y][PORT_WEST] = router_flit_out[x][y][PORT_EAST];
          assign router_flit_out_ready[x][y][PORT_EAST] = router_flit_in_ready[x+1][y][PORT_WEST];
        end else begin : east_edge
          // Edge router - no east connection
          assign router_flit_in_valid[x][y][PORT_EAST] = 1'b0;
          assign router_flit_in[x][y][PORT_EAST] = '0;
          // Edge ports act as sinks - always ready to accept flits
          assign router_flit_out_ready[x][y][PORT_EAST] = 1'b1;
        end
        
        // ========================================================================
        // WEST CONNECTIONS (X-1 direction)
        // ========================================================================
        if (x > 0) begin : west_connection
          // Connect this router's west port to the router to the left's east port
          assign router_flit_in_valid[x-1][y][PORT_EAST] = router_flit_out_valid[x][y][PORT_WEST];
          assign router_flit_in[x-1][y][PORT_EAST] = router_flit_out[x][y][PORT_WEST];
          assign router_flit_out_ready[x][y][PORT_WEST] = router_flit_in_ready[x-1][y][PORT_EAST];
        end else begin : west_edge
          // Edge router - no west connection
          assign router_flit_in_valid[x][y][PORT_WEST] = 1'b0;
          assign router_flit_in[x][y][PORT_WEST] = '0;
          // Edge ports act as sinks - always ready to accept flits
          assign router_flit_out_ready[x][y][PORT_WEST] = 1'b1;
        end
        
        // ========================================================================
        // LOCAL PORT CONNECTIONS
        // ========================================================================
        // Connect local interface to router's local port
        assign router_flit_in_valid[x][y][PORT_LOCAL] = local_flit_in_valid[x][y];
        assign router_flit_in[x][y][PORT_LOCAL] = local_flit_in[x][y];
        assign local_flit_in_ready[x][y] = router_flit_in_ready[x][y][PORT_LOCAL];
        
        assign local_flit_out_valid[x][y] = router_flit_out_valid[x][y][PORT_LOCAL];
        assign local_flit_out[x][y] = router_flit_out[x][y][PORT_LOCAL];
        assign router_flit_out_ready[x][y][PORT_LOCAL] = local_flit_out_ready[x][y];
        
      end
    end
  endgenerate

  // ============================================================================
  // HIERARCHICAL CLUSTERING SUPPORT (Future Extension)
  // ============================================================================
  
  // For systems larger than 8x8, hierarchical clustering can be implemented here
  // This would involve additional routing logic for inter-cluster communication
  
  // TODO: Implement cluster-level routing for scalability beyond 64 nodes
  // - Cluster address allocation
  // - Inter-cluster gateway routers
  // - Hierarchical address mapping
  // - Adaptive routing for load balancing

  // ============================================================================
  // PERFORMANCE MONITORING AND DEBUG
  // ============================================================================
  
  // Performance counters for the entire mesh
  logic [PERF_COUNTER_WIDTH-1:0] total_packets_routed;
  logic [PERF_COUNTER_WIDTH-1:0] total_packets_dropped;
  logic [PERF_COUNTER_WIDTH-1:0] peak_latency;
  logic [PERF_COUNTER_WIDTH-1:0] avg_utilization;
  
  // Calculate total packets routed across all routers
  always_comb begin
    total_packets_routed = '0;
    for (int i = 0; i < MESH_SIZE_X; i++) begin
      for (int j = 0; j < MESH_SIZE_Y; j++) begin
        total_packets_routed += packets_routed[i][j];
      end
    end
  end
  
  // Debug: Display mesh configuration at startup
  initial begin
    $display("Nebula Mesh Topology Configuration:");
    $display("  Mesh Size: %0dx%0d", MESH_SIZE_X, MESH_SIZE_Y);
    $display("  Total Nodes: %0d", MESH_SIZE_X * MESH_SIZE_Y);
    $display("  Max Hops: %0d", (MESH_SIZE_X - 1) + (MESH_SIZE_Y - 1));
    $display("  Edge Routers: %0d", 2 * (MESH_SIZE_X + MESH_SIZE_Y - 2));
    $display("  Corner Routers: 4");
    $display("  Internal Routers: %0d", (MESH_SIZE_X - 2) * (MESH_SIZE_Y - 2));
  end

endmodule
