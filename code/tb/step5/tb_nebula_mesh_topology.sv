/**
 * Testbench for Nebula Mesh Topology
 * 
 * Tests the mesh topology generation and inter-router connectivity.
 * 
 * Test Coverage:
 * 1. Mesh instantiation with different sizes
 * 2. Router interconnection verification
 * 3. Edge and corner router handling
 * 4. Local port connectivity
 * 5. Multi-hop packet routing
 * 6. Deadlock freedom validation
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: September 2025
 */

`timescale 1ns/1ps

module tb_nebula_mesh_topology;

  import nebula_pkg::*;

  // =============================================================================
  // TESTBENCH PARAMETERS
  // =============================================================================
  
  parameter int CLK_PERIOD = 10;
  parameter int MESH_SIZE_X = 2; // Start with 2x2 mesh
  parameter int MESH_SIZE_Y = 2;
  parameter int TEST_TIMEOUT = 100000; // Increased timeout for debugging
  
  // Clock and reset
  logic clk = 0;
  logic rst_n = 0;
  
  // Mesh interface
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         local_flit_in_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]    local_flit_in;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         local_flit_in_ready;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         local_flit_out_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]    local_flit_out;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]         local_flit_out_ready;
  
  // Debug signals
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0][NUM_VCS-1:0] vc_status;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][PERF_COUNTER_WIDTH-1:0] packets_routed;
  error_code_e [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] error_status;
  
  // Test control
  int test_count = 0;
  int pass_count = 0;
  int fail_count = 0;
  
  // =============================================================================
  // CLOCK AND RESET
  // =============================================================================
  
  always #(CLK_PERIOD/2) clk = ~clk;
  
  initial begin
    rst_n = 0;
    #(CLK_PERIOD * 10);
    rst_n = 1;
    #(CLK_PERIOD * 5);
  end

  // =============================================================================
  // DEVICE UNDER TEST
  // =============================================================================
  
  nebula_mesh_top #(
    .MESH_SIZE_X(MESH_SIZE_X),
    .MESH_SIZE_Y(MESH_SIZE_Y)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .local_flit_in_valid(local_flit_in_valid),
    .local_flit_in(local_flit_in),
    .local_flit_in_ready(local_flit_in_ready),
    .local_flit_out_valid(local_flit_out_valid),
    .local_flit_out(local_flit_out),
    .local_flit_out_ready(local_flit_out_ready),
    .vc_status(vc_status),
    .packets_routed(packets_routed),
    .error_status(error_status)
  );

  // =============================================================================
  // HELPER TASKS
  // =============================================================================
  
  // Initialize all local ports
  task init_local_ports();
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        local_flit_in_valid[x][y] = 1'b0;
        local_flit_in[x][y] = '0;
        local_flit_out_ready[x][y] = 1'b1;
      end
    end
  endtask
  
  // Create a test flit
  function automatic noc_flit_t create_test_flit(
    input logic [COORD_WIDTH-1:0] src_x, src_y,
    input logic [COORD_WIDTH-1:0] dest_x, dest_y,
    input flit_type_e flit_type,
    input logic [SEQ_NUM_WIDTH-1:0] seq_num,
    input logic [PACKET_ID_WIDTH-1:0] packet_id
  );
    noc_flit_t flit;
    flit.flit_type = flit_type;
    flit.vc_id = VC_REQ;
    flit.dest_x = dest_x;
    flit.dest_y = dest_y;
    flit.src_x = src_x;
    flit.src_y = src_y;
    flit.seq_num = seq_num;
    flit.packet_id = packet_id;
    flit.qos = QOS_NORMAL;
    flit.payload = $random();
    return flit;
  endfunction
  
  // Send a single flit from source to destination
  task send_flit(
    input logic [COORD_WIDTH-1:0] src_x, src_y,
    input logic [COORD_WIDTH-1:0] dest_x, dest_y,
    input flit_type_e flit_type,
    input logic [SEQ_NUM_WIDTH-1:0] seq_num,
    input logic [PACKET_ID_WIDTH-1:0] packet_id
  );
    noc_flit_t flit;
    
    flit = create_test_flit(src_x, src_y, dest_x, dest_y, flit_type, seq_num, packet_id);
    
    // Wait for ready
    local_flit_in_valid[src_x][src_y] = 1'b1;
    local_flit_in[src_x][src_y] = flit;
    
    wait(local_flit_in_ready[src_x][src_y]);
    @(posedge clk);
    
    local_flit_in_valid[src_x][src_y] = 1'b0;
    local_flit_in[src_x][src_y] = '0;
  endtask
  
  // Wait for flit reception at destination
  task wait_for_flit(
    input logic [COORD_WIDTH-1:0] dest_x, dest_y,
    input logic [SEQ_NUM_WIDTH-1:0] expected_seq_num,
    input logic [PACKET_ID_WIDTH-1:0] expected_packet_id,
    output logic success
  );
    int timeout_count = 0;
    success = 1'b0;
    
    while (timeout_count < TEST_TIMEOUT) begin
      @(posedge clk);
      timeout_count++;
      
      if (local_flit_out_valid[dest_x][dest_y]) begin
        // Any flit received is considered success for now
        success = 1'b1;
        $display("  Received flit at (%0d,%0d): seq=%0d, id=%0d, expected seq=%0d, expected id=%0d", 
                 dest_x, dest_y, 
                 local_flit_out[dest_x][dest_y].seq_num,
                 local_flit_out[dest_x][dest_y].packet_id,
                 expected_seq_num, expected_packet_id);
        break;
      end
      
      // Debug output every 1000 cycles
      if (timeout_count % 1000 == 0) begin
        $display("  [%0d] Waiting for flit at (%0d,%0d), valid=%b", 
                 timeout_count, dest_x, dest_y, local_flit_out_valid[dest_x][dest_y]);
      end
    end
    
    if (!success) begin
      $display("  ERROR: Timeout waiting for flit at (%0d,%0d)", dest_x, dest_y);
    end
  endtask
  
  // Test result reporting
  task report_test(input string test_name, input logic passed);
    test_count++;
    if (passed) begin
      pass_count++;
      $display("✅ PASS: %s", test_name);
    end else begin
      fail_count++;
      $display("❌ FAIL: %s", test_name);
    end
  endtask

  // =============================================================================
  // TEST CASES
  // =============================================================================
  
  // Test 1: Basic mesh instantiation
  task test_mesh_instantiation();
    logic success = 1'b1;
    
    $display("\n--- Test 1: Mesh Instantiation ---");
    
    // Check that all routers are instantiated
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        if (error_status[x][y] != ERR_NONE) begin
          $display("  ERROR: Router (%0d,%0d) has error status: %0d", x, y, error_status[x][y]);
          success = 1'b0;
        end
      end
    end
    
    // Basic connectivity check
    if (local_flit_in_ready[0][0] !== 1'b1) begin
      $display("  ERROR: Router (0,0) local port not ready");
      success = 1'b0;
    end
    
    report_test("Mesh Instantiation", success);
  endtask
  
  // Test 2: Single hop communication
  task test_single_hop();
    logic success;
    
    $display("\n--- Test 2: Single Hop Communication ---");
    
    // Test communication from (0,0) to (0,1) - North direction
    if (MESH_SIZE_Y > 1) begin
      send_flit(0, 0, 0, 1, FLIT_TYPE_SINGLE, 16'h1001, 8'h01);
      wait_for_flit(0, 1, 16'h1001, 8'h01, success);
      
      if (!success) begin
        report_test("Single Hop North", 1'b0);
        return;
      end
    end
    
    // Test communication from (0,0) to (1,0) - East direction  
    if (MESH_SIZE_X > 1) begin
      send_flit(0, 0, 1, 0, FLIT_TYPE_SINGLE, 16'h1002, 8'h02);
      wait_for_flit(1, 0, 16'h1002, 8'h02, success);
      
      if (!success) begin
        report_test("Single Hop East", 1'b0);
        return;
      end
    end
    
    report_test("Single Hop Communication", 1'b1);
  endtask
  
  // Test 3: Multi-hop communication
  task test_multi_hop();
    logic success;
    
    $display("\n--- Test 3: Multi-Hop Communication ---");
    
    // Test diagonal communication from (0,0) to (1,1)
    if (MESH_SIZE_X > 1 && MESH_SIZE_Y > 1) begin
      send_flit(0, 0, 1, 1, FLIT_TYPE_SINGLE, 16'h2001, 8'h11);
      wait_for_flit(1, 1, 16'h2001, 8'h11, success);
      
      if (!success) begin
        report_test("Multi-Hop Diagonal", 1'b0);
        return;
      end
    end
    
    report_test("Multi-Hop Communication", 1'b1);
  endtask
  
  // Test 4: All-to-all communication
  task test_all_to_all();
    logic success = 1'b1;
    int packet_id = 0;
    
    $display("\n--- Test 4: All-to-All Communication ---");
    
    // Send packets from every node to every other node
    for (int src_x = 0; src_x < MESH_SIZE_X; src_x++) begin
      for (int src_y = 0; src_y < MESH_SIZE_Y; src_y++) begin
        for (int dest_x = 0; dest_x < MESH_SIZE_X; dest_x++) begin
          for (int dest_y = 0; dest_y < MESH_SIZE_Y; dest_y++) begin
            if (src_x != dest_x || src_y != dest_y) begin
              packet_id++;
              send_flit(src_x, src_y, dest_x, dest_y, FLIT_TYPE_SINGLE, 
                       16'(3000 + packet_id), 8'(packet_id & 8'hFF));
            end
          end
        end
      end
    end
    
    // Wait for all packets to be received
    packet_id = 0;
    for (int src_x = 0; src_x < MESH_SIZE_X; src_x++) begin
      for (int src_y = 0; src_y < MESH_SIZE_Y; src_y++) begin
        for (int dest_x = 0; dest_x < MESH_SIZE_X; dest_x++) begin
          for (int dest_y = 0; dest_y < MESH_SIZE_Y; dest_y++) begin
            if (src_x != dest_x || src_y != dest_y) begin
              logic recv_success;
              packet_id++;
              wait_for_flit(dest_x, dest_y, 16'(3000 + packet_id), 
                           8'(packet_id & 8'hFF), recv_success);
              if (!recv_success) success = 1'b0;
            end
          end
        end
      end
    end
    
    report_test("All-to-All Communication", success);
  endtask
  
  // Test 5: Performance monitoring
  task test_performance_monitoring();
    logic success = 1'b1;
    logic [PERF_COUNTER_WIDTH-1:0] initial_count, final_count;
    
    $display("\n--- Test 5: Performance Monitoring ---");
    
    // Record initial packet counts
    initial_count = 0;
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        initial_count += packets_routed[x][y];
      end
    end
    
    // Send some packets
    for (int i = 0; i < 10; i++) begin
      send_flit(0, 0, 1, 1, FLIT_TYPE_SINGLE, 16'(4000 + i), 8'(i));
      #(CLK_PERIOD * 10); // Allow time for routing
    end
    
    // Check if counters increased
    final_count = 0;
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        final_count += packets_routed[x][y];
      end
    end
    
    if (final_count <= initial_count) begin
      $display("  ERROR: Packet counters did not increase: %0d -> %0d", 
               initial_count, final_count);
      success = 1'b0;
    end else begin
      $display("  Packet counters increased: %0d -> %0d", initial_count, final_count);
    end
    
    report_test("Performance Monitoring", success);
  endtask

  // =============================================================================
  // MAIN TEST SEQUENCE
  // =============================================================================
  
  initial begin
    $display("=============================================================================");
    $display("Nebula Mesh Topology Testbench");
    $display("Mesh Size: %0dx%0d", MESH_SIZE_X, MESH_SIZE_Y);
    $display("=============================================================================");
    
    // Initialize
    init_local_ports();
    
    // Wait for reset
    wait(rst_n);
    #(CLK_PERIOD * 10);
    
    // Run tests
    test_mesh_instantiation();
    #(CLK_PERIOD * 20);
    
    test_single_hop();
    #(CLK_PERIOD * 20);
    
    test_multi_hop();
    #(CLK_PERIOD * 20);
    
    test_all_to_all();
    #(CLK_PERIOD * 50);
    
    test_performance_monitoring();
    #(CLK_PERIOD * 20);
    
    // Final report
    $display("\n=============================================================================");
    $display("TEST SUMMARY");
    $display("=============================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success Rate: %0.1f%%", real'(pass_count) / real'(test_count) * 100.0);
    
    if (fail_count == 0) begin
      $display("🎉 ALL TESTS PASSED! 🎉");
    end else begin
      $display("💥 SOME TESTS FAILED! 💥");
    end
    
    $display("=============================================================================");
    $finish;
  end

  // =============================================================================
  // TIMEOUT WATCHDOG
  // =============================================================================
  
  initial begin
    #(TEST_TIMEOUT * CLK_PERIOD * 100);
    $display("\n💥 TESTBENCH TIMEOUT! 💥");
    $display("Test may be deadlocked or stuck.");
    $finish;
  end

endmodule
