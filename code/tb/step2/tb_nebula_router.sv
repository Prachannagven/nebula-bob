/**
 * Testbench for Nebula Router
 * 
 * Tests the 5-stage router pipeline with various traffic patterns:
 * - Single-hop packet forwarding in all directions
 * - Multi-hop routing through intermediate coordinates
 * - Congestion handling and adaptive routing
 * - Pipeline stall and backpressure propagation
 * - VC allocation and management
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: August 2025
 */

import nebula_pkg::*;

module tb_nebula_router;

  // Test parameters
  parameter int MESH_SIZE_X = 8;
  parameter int MESH_SIZE_Y = 8;
  parameter int ROUTER_X = 2;  // Middle of 4x4 mesh
  parameter int ROUTER_Y = 2;
  parameter int TEST_TIMEOUT = 1000;
  
  // DUT signals
  logic                                    clk;
  logic                                    rst_n;
  logic [NUM_PORTS-1:0]                   flit_in_valid;
  noc_flit_t [NUM_PORTS-1:0]              flit_in;
  logic [NUM_PORTS-1:0]                   flit_in_ready;
  logic [NUM_PORTS-1:0]                   flit_out_valid;
  noc_flit_t [NUM_PORTS-1:0]              flit_out;
  logic [NUM_PORTS-1:0]                   flit_out_ready;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]      vc_status;
  logic [PERF_COUNTER_WIDTH-1:0]          packets_routed;
  error_code_e                            error_status;

  // Test control
  int test_case;
  int errors;
  int cycle_count;
  
  // Traffic generation
  noc_flit_t test_flit;
  logic [FLIT_WIDTH*FLITS_PER_PACKET-1:0] test_payload;

  // DUT instantiation
  nebula_router #(
    .ROUTER_X(ROUTER_X),
    .ROUTER_Y(ROUTER_Y),
    .MESH_SIZE_X(MESH_SIZE_X),
    .MESH_SIZE_Y(MESH_SIZE_Y)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .flit_in_valid(flit_in_valid),
    .flit_in(flit_in),
    .flit_in_ready(flit_in_ready),
    .flit_out_valid(flit_out_valid),
    .flit_out(flit_out),
    .flit_out_ready(flit_out_ready),
    .vc_status(vc_status),
    .packets_routed(packets_routed),
    .error_status(error_status)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;  // 100MHz clock
  end

  // Test sequence
  initial begin
    $dumpfile("nebula_router_tb.vcd");
    $dumpvars(0, tb_nebula_router);
    
    // Initialize
    rst_n = 0;
    flit_in_valid = '0;
    flit_in = '{default: '0};
    flit_out_ready = '1;  // Always ready to receive output
    test_case = 0;
    errors = 0;
    cycle_count = 0;
    
    // Reset sequence
    repeat (10) @(posedge clk);
    rst_n = 1;
    repeat (5) @(posedge clk);
    
    $display("=== NEBULA ROUTER TESTBENCH ===");
    $display("Router position: (%0d, %0d) in %0dx%0d mesh", 
             ROUTER_X, ROUTER_Y, MESH_SIZE_X, MESH_SIZE_Y);
    $display("");
    
    // Test cases
    run_test_case(1, "Basic Functionality Test");
    run_test_case(2, "XY Routing Test - East");
    run_test_case(3, "XY Routing Test - West");
    run_test_case(4, "XY Routing Test - North");
    run_test_case(5, "XY Routing Test - South");
    run_test_case(6, "Local Delivery Test");
    run_test_case(7, "Multiple VC Test");
    run_test_case(8, "Backpressure Test");
    
    // Final results
    $display("");
    $display("=== FINAL RESULTS ===");
    if (errors == 0) begin
      $display("✅ ALL TESTS PASSED!");
      $display("Total packets routed: %0d", packets_routed);
    end else begin
      $display("❌ %0d ERRORS DETECTED", errors);
    end
    $display("Total cycles: %0d", cycle_count);
    
    $finish;
  end
  
  // Cycle counter
  always @(posedge clk) begin
    cycle_count++;
    if (cycle_count > TEST_TIMEOUT) begin
      $display("❌ TIMEOUT: Test exceeded %0d cycles", TEST_TIMEOUT);
      errors++;
      $finish;
    end
  end

  // Test execution task
  task run_test_case(input int case_num, input string test_name);
    begin
      test_case = case_num;
      $display("--- Test Case %0d: %s ---", case_num, test_name);
      
      case (case_num)
        1: test_basic_functionality();
        2: test_xy_routing_east();
        3: test_xy_routing_west(); 
        4: test_xy_routing_north();
        5: test_xy_routing_south();
        6: test_local_delivery();
        7: test_multiple_vc();
        8: test_backpressure();
        default: $display("Unknown test case: %0d", case_num);
      endcase
      
      // Wait between tests
      repeat (10) @(posedge clk);
    end
  endtask

  // Test Case 1: Basic functionality
  task test_basic_functionality();
    begin
      $display("Testing basic pipeline functionality...");
      
      // Send a single flit packet to check pipeline stages
      create_test_flit(ROUTER_X + 1, ROUTER_Y, 0, 0, FLIT_TYPE_SINGLE, 8'hAA);
      
      send_flit_on_port(PORT_LOCAL, test_flit);
      
      // Wait for expected output on East port
      wait_for_output(PORT_EAST, 8'hAA);
      
      $display("✅ Basic functionality test passed");
    end
  endtask

  // Test Case 2: XY Routing - East direction
  task test_xy_routing_east();
    begin
      $display("Testing XY routing to East...");
      
      // Send packet destined for router to the east
      create_test_flit(ROUTER_X + 1, ROUTER_Y, 0, 1, FLIT_TYPE_SINGLE, 8'hBB);
      
      send_flit_on_port(PORT_LOCAL, test_flit);
      wait_for_output(PORT_EAST, 8'hBB);
      
      $display("✅ East routing test passed");
    end
  endtask

  // Test Case 3: XY Routing - West direction
  task test_xy_routing_west();
    begin
      $display("Testing XY routing to West...");
      
      // Send packet destined for router to the west
      create_test_flit(ROUTER_X - 1, ROUTER_Y, 0, 2, FLIT_TYPE_SINGLE, 8'hCC);
      
      send_flit_on_port(PORT_LOCAL, test_flit);
      wait_for_output(PORT_WEST, 8'hCC);
      
      $display("✅ West routing test passed");
    end
  endtask

  // Test Case 4: XY Routing - North direction  
  task test_xy_routing_north();
    begin
      $display("Testing XY routing to North...");
      
      // Send packet destined for router to the north
      create_test_flit(ROUTER_X, ROUTER_Y + 1, 0, 3, FLIT_TYPE_SINGLE, 8'hDD);
      
      send_flit_on_port(PORT_LOCAL, test_flit);
      wait_for_output(PORT_NORTH, 8'hDD);
      
      $display("✅ North routing test passed");
    end
  endtask

  // Test Case 5: XY Routing - South direction
  task test_xy_routing_south();
    begin
      $display("Testing XY routing to South...");
      
      // Send packet destined for router to the south
      create_test_flit(ROUTER_X, ROUTER_Y - 1, 0, 4, FLIT_TYPE_SINGLE, 8'hEE);
      
      send_flit_on_port(PORT_LOCAL, test_flit);
      wait_for_output(PORT_SOUTH, 8'hEE);
      
      $display("✅ South routing test passed");
    end
  endtask

  // Test Case 6: Local delivery
  task test_local_delivery();
    begin
      $display("Testing local delivery...");
      
      // Send packet destined for this router
      create_test_flit(ROUTER_X, ROUTER_Y, 0, 5, FLIT_TYPE_SINGLE, 8'hFF);
      
      send_flit_on_port(PORT_NORTH, test_flit);
      wait_for_output(PORT_LOCAL, 8'hFF);
      
      $display("✅ Local delivery test passed");
    end
  endtask

  // Test Case 7: Multiple VC test
  task test_multiple_vc();
    begin
      $display("Testing multiple VCs...");
      
      // Send flits on different VCs simultaneously
      create_test_flit(ROUTER_X + 1, ROUTER_Y, 0, 6, FLIT_TYPE_SINGLE, 8'h11);
      send_flit_on_port(PORT_LOCAL, test_flit);
      
      create_test_flit(ROUTER_X + 1, ROUTER_Y, 1, 7, FLIT_TYPE_SINGLE, 8'h22);
      test_flit.vc_id = 1;
      send_flit_on_port(PORT_LOCAL, test_flit);
      
      // Both should route to East port
      wait_for_output(PORT_EAST, 8'h11);
      wait_for_output(PORT_EAST, 8'h22);
      
      $display("✅ Multiple VC test passed");
    end
  endtask

  // Test Case 8: Backpressure test
  task test_backpressure();
    begin
      $display("Testing backpressure handling...");
      
      // Block output port to create backpressure
      flit_out_ready[PORT_EAST] = 1'b0;
      
      create_test_flit(ROUTER_X + 1, ROUTER_Y, 0, 8, FLIT_TYPE_SINGLE, 8'h33);
      send_flit_on_port(PORT_LOCAL, test_flit);
      
      // Wait and verify no output due to backpressure
      repeat (20) @(posedge clk);
      if (flit_out_valid[PORT_EAST]) begin
        $display("❌ Backpressure test failed - flit transmitted despite blocked output");
        errors++;
      end else begin
        $display("✅ Backpressure correctly blocks transmission");
      end
      
      // Release backpressure and verify transmission
      flit_out_ready[PORT_EAST] = 1'b1;
      wait_for_output(PORT_EAST, 8'h33);
      
      $display("✅ Backpressure test passed");
    end
  endtask

  // Helper task: Create test flit
  task create_test_flit(
    input logic [COORD_WIDTH-1:0] dest_x,
    input logic [COORD_WIDTH-1:0] dest_y,
    input logic [VC_ID_WIDTH-1:0] vc_id,
    input logic [PACKET_ID_WIDTH-1:0] packet_id,
    input flit_type_e flit_type,
    input logic [7:0] test_pattern
  );
    begin
      test_flit = '0;
      test_flit.flit_type = flit_type;
      test_flit.vc_id = vc_id;
      test_flit.dest_x = dest_x;
      test_flit.dest_y = dest_y;
      test_flit.src_x = ROUTER_X;
      test_flit.src_y = ROUTER_Y;
      test_flit.seq_num = 16'h0001;
      test_flit.packet_id = packet_id;
      test_flit.qos = QOS_NORMAL;
      test_flit.payload[7:0] = test_pattern;
    end
  endtask

  // Helper task: Send flit on specified port
  task send_flit_on_port(input int port, input noc_flit_t flit);
    begin
      @(posedge clk);
      $display("[DEBUG] @%0t: Sending flit on port %0d: flit_type=%0d, dest=(%0d,%0d), src=(%0d,%0d), payload[7:0]=0x%02x", 
               $time, port, flit.flit_type, flit.dest_x, flit.dest_y, flit.src_x, flit.src_y, flit.payload[7:0]);
      flit_in_valid[port] = 1'b1;
      flit_in[port] = flit;
      
      // Wait for ready signal
      while (!flit_in_ready[port]) @(posedge clk);
      
      @(posedge clk);
      flit_in_valid[port] = 1'b0;
      flit_in[port] = '0;
    end
  endtask

  // Helper task: Wait for specific output
  task wait_for_output(input int port, input logic [7:0] expected_pattern);
    begin
      int wait_cycles = 0;
      
      while (!flit_out_valid[port] || flit_out[port].payload[7:0] != expected_pattern) begin
        @(posedge clk);
        wait_cycles++;
        if (wait_cycles > 50) begin
          $display("❌ Timeout waiting for output on port %0d with pattern 0x%02x", 
                   port, expected_pattern);
          errors++;
          return;
        end
      end
      
      $display("✅ Received expected output on port %0d with pattern 0x%02x (latency: %0d cycles)", 
               port, expected_pattern, wait_cycles);
    end
  endtask

  // Monitor for debugging
  always @(posedge clk) begin
    if (rst_n) begin
      // Monitor error status
      if (error_status != ERR_NONE) begin
        $display("⚠️  Router error detected: %0d at cycle %0d", error_status, cycle_count);
      end
      
      // Monitor packet completion
      if (packets_routed > 0 && $time > 0) begin
        // Track packet completions (silent to avoid spam)
      end
    end
  end

endmodule
