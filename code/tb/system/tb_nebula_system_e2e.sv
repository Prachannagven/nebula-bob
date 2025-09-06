`timescale 1ns/1ps

module tb_nebula_system_e2e;

  import nebula_pkg::*;

  // =============================================================================
  // Constants
  // =============================================================================
  
  localparam int MESH_SIZE_X = 4;
  localparam int MESH_SIZE_Y = 4;
  localparam int NUM_NODES = MESH_SIZE_X * MESH_SIZE_Y;
  localparam int PACKETS_PER_NODE = 20;
  
  localparam int CLOCK_PERIOD = 10;
  localparam int SIM_TIMEOUT = 50000;
  
  // Traffic patterns
  typedef enum {
    UNIFORM_RANDOM,
    NEAREST_NEIGHBOR,
    HOTSPOT,
    TRANSPOSE
  } traffic_pattern_t;

  // Node state tracking
  typedef struct {
    logic active;
    int dest_x;
    int dest_y;
    int packets_sent;
    int packets_received;
    logic [31:0] send_timestamp;
  } node_state_t;

  // =============================================================================
  // DUT Signals
  // =============================================================================
  
  logic clk;
  logic rst_n;
  
  // Router mesh signals
  flit_t [NUM_NODES-1:0] node_req_data;
  logic [NUM_NODES-1:0] node_req_valid;
  logic [NUM_NODES-1:0] node_req_ready;
  
  flit_t [NUM_NODES-1:0] node_resp_data;
  logic [NUM_NODES-1:0] node_resp_valid;
  logic [NUM_NODES-1:0] node_resp_ready;
  
  // Internal router connections
  flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][4:0] router_req_data;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][4:0] router_req_valid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][4:0] router_req_ready;
  
  flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][4:0] router_resp_data;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][4:0] router_resp_valid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][4:0] router_resp_ready;

  // =============================================================================
  // State Variables
  // =============================================================================
  
  node_state_t node_state [NUM_NODES];
  traffic_pattern_t current_pattern;
  
  int total_packets_sent;
  int total_packets_received;
  logic [31:0] total_cycles;
  logic [15:0] max_latency;
  real packet_delivery_ratio;
  real avg_throughput;
  
  int test_count;
  int pass_count;
  int fail_count;

  // =============================================================================
  // Clock Generation
  // =============================================================================
  
  initial begin
    clk = 0;
    forever #(CLOCK_PERIOD/2) clk = ~clk;
  end

  // =============================================================================
  // DUT Instantiation (4x4 Mesh)
  // =============================================================================
  
  genvar gx, gy;
  generate
    for (gx = 0; gx < MESH_SIZE_X; gx++) begin : gen_x
      for (gy = 0; gy < MESH_SIZE_Y; gy++) begin : gen_y
        
        localparam int NODE_ID = gx * MESH_SIZE_X + gy;
        localparam int MY_X = gx;
        localparam int MY_Y = gy;
        
        nebula_router #(
          .MY_X_COORD(MY_X),
          .MY_Y_COORD(MY_Y),
          .MESH_SIZE_X(MESH_SIZE_X),
          .MESH_SIZE_Y(MESH_SIZE_Y)
        ) router_inst (
          .clk(clk),
          .rst_n(rst_n),
          
          // Local node interface
          .local_req_data(node_req_data[NODE_ID]),
          .local_req_valid(node_req_valid[NODE_ID]),
          .local_req_ready(node_req_ready[NODE_ID]),
          
          .local_resp_data(node_resp_data[NODE_ID]),
          .local_resp_valid(node_resp_valid[NODE_ID]),
          .local_resp_ready(node_resp_ready[NODE_ID]),
          
          // North
          .north_req_data(router_req_data[gx][gy][NORTH]),
          .north_req_valid(router_req_valid[gx][gy][NORTH]),
          .north_req_ready(router_req_ready[gx][gy][NORTH]),
          .north_resp_data(router_resp_data[gx][gy][NORTH]),
          .north_resp_valid(router_resp_valid[gx][gy][NORTH]),
          .north_resp_ready(router_resp_ready[gx][gy][NORTH]),
          
          // South
          .south_req_data(router_req_data[gx][gy][SOUTH]),
          .south_req_valid(router_req_valid[gx][gy][SOUTH]),
          .south_req_ready(router_req_ready[gx][gy][SOUTH]),
          .south_resp_data(router_resp_data[gx][gy][SOUTH]),
          .south_resp_valid(router_resp_valid[gx][gy][SOUTH]),
          .south_resp_ready(router_resp_ready[gx][gy][SOUTH]),
          
          // East
          .east_req_data(router_req_data[gx][gy][EAST]),
          .east_req_valid(router_req_valid[gx][gy][EAST]),
          .east_req_ready(router_req_ready[gx][gy][EAST]),
          .east_resp_data(router_resp_data[gx][gy][EAST]),
          .east_resp_valid(router_resp_valid[gx][gy][EAST]),
          .east_resp_ready(router_resp_ready[gx][gy][EAST]),
          
          // West
          .west_req_data(router_req_data[gx][gy][WEST]),
          .west_req_valid(router_req_valid[gx][gy][WEST]),
          .west_req_ready(router_req_ready[gx][gy][WEST]),
          .west_resp_data(router_resp_data[gx][gy][WEST]),
          .west_resp_valid(router_resp_valid[gx][gy][WEST]),
          .west_resp_ready(router_resp_ready[gx][gy][WEST])
        );
        
      end
    end
  endgenerate

  // =============================================================================
  // Mesh Interconnections
  // =============================================================================
  
  generate
    for (gx = 0; gx < MESH_SIZE_X; gx++) begin
      for (gy = 0; gy < MESH_SIZE_Y; gy++) begin
        
        // North connections
        if (gy < MESH_SIZE_Y - 1) begin
          assign router_req_data[gx][gy+1][SOUTH] = router_req_data[gx][gy][NORTH];
          assign router_req_valid[gx][gy+1][SOUTH] = router_req_valid[gx][gy][NORTH];
          assign router_req_ready[gx][gy][NORTH] = router_req_ready[gx][gy+1][SOUTH];
          
          assign router_resp_data[gx][gy][NORTH] = router_resp_data[gx][gy+1][SOUTH];
          assign router_resp_valid[gx][gy][NORTH] = router_resp_valid[gx][gy+1][SOUTH];
          assign router_resp_ready[gx][gy+1][SOUTH] = router_resp_ready[gx][gy][NORTH];
        end else begin
          assign router_req_ready[gx][gy][NORTH] = 1'b0;
          assign router_resp_data[gx][gy][NORTH] = '0;
          assign router_resp_valid[gx][gy][NORTH] = 1'b0;
        end
        
        // East connections
        if (gx < MESH_SIZE_X - 1) begin
          assign router_req_data[gx+1][gy][WEST] = router_req_data[gx][gy][EAST];
          assign router_req_valid[gx+1][gy][WEST] = router_req_valid[gx][gy][EAST];
          assign router_req_ready[gx][gy][EAST] = router_req_ready[gx+1][gy][WEST];
          
          assign router_resp_data[gx][gy][EAST] = router_resp_data[gx+1][gy][WEST];
          assign router_resp_valid[gx][gy][EAST] = router_resp_valid[gx+1][gy][WEST];
          assign router_resp_ready[gx+1][gy][WEST] = router_resp_ready[gx][gy][EAST];
        end else begin
          assign router_req_ready[gx][gy][EAST] = 1'b0;
          assign router_resp_data[gx][gy][EAST] = '0;
          assign router_resp_valid[gx][gy][EAST] = 1'b0;
        end
        
      end
    end
  endgenerate

  // =============================================================================
  // Test Tasks
  // =============================================================================
  
  task reset_dut();
    rst_n = 1'b0;
    
    // Initialize node interfaces
    for (int i = 0; i < NUM_NODES; i++) begin
      node_req_data[i] = '0;
      node_req_valid[i] = 1'b0;
      node_resp_ready[i] = 1'b1;
      
      node_state[i].active = 1'b0;
      node_state[i].dest_x = 0;
      node_state[i].dest_y = 0;
      node_state[i].packets_sent = 0;
      node_state[i].packets_received = 0;
      node_state[i].send_timestamp = 0;
    end
    
    // Reset statistics
    total_packets_sent = 0;
    total_packets_received = 0;
    total_cycles = 0;
    max_latency = 0;
    packet_delivery_ratio = 0.0;
    avg_throughput = 0.0;
    
    repeat(10) @(posedge clk);
    rst_n = 1'b1;
    repeat(10) @(posedge clk);
  endtask
  
  task generate_uniform_random_traffic();
    $display("Starting Uniform Random Traffic Pattern");
    
    for (int src = 0; src < NUM_NODES; src++) begin
      int dest = $random() % NUM_NODES;
      node_state[src].dest_x = dest % MESH_SIZE_X;
      node_state[src].dest_y = dest / MESH_SIZE_X;
      node_state[src].active = 1'b1;
    end
    
    current_pattern = UNIFORM_RANDOM;
  endtask
  
  task inject_packet(input int node_id, input int dest_x, input int dest_y, input int seq_num);
    flit_t packet;
    
    packet.packet_type = PACKET_DATA;
    packet.src_x = node_id % MESH_SIZE_X;
    packet.src_y = node_id / MESH_SIZE_X;
    packet.dest_x = dest_x;
    packet.dest_y = dest_y;
    packet.sequence_num = seq_num;
    packet.data = $random();
    packet.valid = 1'b1;
    
    if (node_req_ready[node_id]) begin
      node_req_data[node_id] <= packet;
      node_req_valid[node_id] <= 1'b1;
      node_state[node_id].send_timestamp <= total_cycles;
      total_packets_sent++;
      
      @(posedge clk);
      node_req_valid[node_id] <= 1'b0;
    end
  endtask
  
  // Simplified packet reception check
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      total_cycles <= 0;
    end else begin
      total_cycles <= total_cycles + 1;
      
      // Count packets received
      for (int i = 0; i < NUM_NODES; i++) begin
        if (node_resp_valid[i] && node_resp_ready[i]) begin
          total_packets_received <= total_packets_received + 1;
          node_state[i].packets_received <= node_state[i].packets_received + 1;
        end
      end
    end
  end

  // =============================================================================
  // Test Scenarios
  // =============================================================================
  
  task run_basic_test();
    int max_cycles = 2000;
    int packets_injected = 0;
    
    $display("--- Starting Basic Mesh Test ---");
    
    reset_dut();
    generate_uniform_random_traffic();
    
    // Inject packets
    for (int cycle = 0; cycle < max_cycles && packets_injected < PACKETS_PER_NODE * NUM_NODES; cycle++) begin
      for (int node = 0; node < NUM_NODES; node++) begin
        if (node_state[node].active && 
            node_state[node].packets_sent < PACKETS_PER_NODE) begin
          
          if ($random() % 10 < 3) begin  // 30% injection rate
            inject_packet(node, 
                         node_state[node].dest_x, 
                         node_state[node].dest_y,
                         node_state[node].packets_sent);
            node_state[node].packets_sent++;
            packets_injected++;
          end
        end
      end
      
      @(posedge clk);
    end
    
    // Wait for packets to drain
    repeat(500) @(posedge clk);
    
    // Collect statistics
    if (total_packets_sent > 0) begin
      packet_delivery_ratio = real'(total_packets_received) / real'(total_packets_sent);
    end else begin
      packet_delivery_ratio = 0.0;
    end
    
    avg_throughput = real'(total_packets_received) / real'(total_cycles) * 1000.0;
    
    // Check test results
    test_count++;
    if (packet_delivery_ratio >= 0.90) begin
      $display("      PASSED");
      $display("      Delivery ratio: %0.3f, Throughput: %0.3f packets/cycle", 
               packet_delivery_ratio, avg_throughput/1000.0);
      pass_count++;
    end else begin
      $display("      FAILED (Delivery ratio: %0.3f)", packet_delivery_ratio);
      fail_count++;
    end
    
    $display("--- Completed Basic Test ---");
  endtask

  // =============================================================================
  // Main Test Sequence
  // =============================================================================
  
  initial begin
    $display("===============================================");
    $display("    Nebula System End-to-End Test Suite");
    $display("===============================================");
    
    test_count = 0;
    pass_count = 0;
    fail_count = 0;
    
    // Run basic test only for now
    run_basic_test();
    
    // Summary
    $display("===============================================");
    $display("           Test Results Summary");
    $display("===============================================");
    if (fail_count == 0) begin
      $display("     ALL SYSTEM TESTS PASSED!");
    end else begin
      $display("    %0d test(s) failed", fail_count);
    end
    $display("    Total: %0d, Passed: %0d, Failed: %0d", test_count, pass_count, fail_count);
    $display("===============================================");
    
    $finish;
  end
  
  // Timeout
  initial begin
    #SIM_TIMEOUT;
    $display("ERROR: Simulation timeout");
    $finish;
  end

endmodule
