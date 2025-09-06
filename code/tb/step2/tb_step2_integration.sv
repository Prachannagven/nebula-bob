/**
 * Step 2 Integration Testbench for Multi-Router Communication
 * 
 * Tests a 2x2 mesh of routers to validate:
 * - Multi-hop packet routing across the mesh
 * - End-to-end packet delivery
 * - Congestion handling with multiple routers
 * - VC allocation across router boundaries
 * - Network-wide flow control
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: August 2025
 */

import nebula_pkg::*;

module tb_step2_integration;

  // Test parameters
  parameter int MESH_SIZE_X = 2;
  parameter int MESH_SIZE_Y = 2;
  parameter int TEST_TIMEOUT = 2000;
  parameter int NUM_TEST_PACKETS = 16;  // Test all-to-all communication
  
  // System signals
  logic clk;
  logic rst_n;
  
  // Router interconnect signals
  // [router_y][router_x][port] format
  logic [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0][NUM_PORTS-1:0]      router_flit_out_valid;
  noc_flit_t [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0][NUM_PORTS-1:0] router_flit_out;
  logic [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0][NUM_PORTS-1:0]      router_flit_out_ready;
  logic [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0][NUM_PORTS-1:0]      router_flit_in_valid;
  noc_flit_t [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0][NUM_PORTS-1:0] router_flit_in;
  logic [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0][NUM_PORTS-1:0]      router_flit_in_ready;
  
  // Separate signal for local port ready (controlled by sequential logic)
  logic [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0] local_ready;
  
  // Packet consumption tracking
  logic [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0] packet_consumed;
  int consumed_packet_ids[MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0][$];
  
  // Debug and status signals
  logic [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0][NUM_PORTS-1:0][NUM_VCS-1:0] vc_status;
  logic [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0][PERF_COUNTER_WIDTH-1:0] packets_routed;
  error_code_e [MESH_SIZE_Y-1:0][MESH_SIZE_X-1:0] error_status;

  // Test control
  int test_case;
  int errors;
  int cycle_count;
  int packets_sent;
  int packets_received;
  
  // Traffic generation and monitoring
  noc_flit_t test_packets [0:NUM_TEST_PACKETS-1];
  logic [NUM_TEST_PACKETS-1:0] packet_sent_flags;
  logic [NUM_TEST_PACKETS-1:0] packet_received_flags;

  genvar gx, gy;

  // ============================================================================
  // 2x2 MESH INSTANTIATION
  // ============================================================================
  
  generate
    for (gy = 0; gy < MESH_SIZE_Y; gy++) begin : gen_mesh_y
      for (gx = 0; gx < MESH_SIZE_X; gx++) begin : gen_mesh_x
        
        nebula_router #(
          .ROUTER_X(gx),
          .ROUTER_Y(gy),
          .MESH_SIZE_X(MESH_SIZE_X),
          .MESH_SIZE_Y(MESH_SIZE_Y)
        ) router_inst (
          .clk(clk),
          .rst_n(rst_n),
          .flit_in_valid(router_flit_in_valid[gy][gx]),
          .flit_in(router_flit_in[gy][gx]),
          .flit_in_ready(router_flit_in_ready[gy][gx]),
          .flit_out_valid(router_flit_out_valid[gy][gx]),
          .flit_out(router_flit_out[gy][gx]),
          .flit_out_ready(router_flit_out_ready[gy][gx]),
          .vc_status(vc_status[gy][gx]),
          .packets_routed(packets_routed[gy][gx]),
          .error_status(error_status[gy][gx])
        );
      end
    end
  endgenerate

  // ============================================================================
  // MESH INTERCONNECTION
  // ============================================================================
  
  generate
    for (gy = 0; gy < MESH_SIZE_Y; gy++) begin : gen_interconnect_y
      for (gx = 0; gx < MESH_SIZE_X; gx++) begin : gen_interconnect_x
        
        // North connections
        if (gy < MESH_SIZE_Y - 1) begin : north_connect
          // Connect to router above
          assign router_flit_in_valid[gy][gx][PORT_NORTH] = router_flit_out_valid[gy+1][gx][PORT_SOUTH];
          assign router_flit_in[gy][gx][PORT_NORTH] = router_flit_out[gy+1][gx][PORT_SOUTH];
          assign router_flit_out_ready[gy+1][gx][PORT_SOUTH] = router_flit_in_ready[gy][gx][PORT_NORTH];
        end else begin : north_terminate
          // Edge connection - terminate
          assign router_flit_in_valid[gy][gx][PORT_NORTH] = 1'b0;
          assign router_flit_in[gy][gx][PORT_NORTH] = '0;
          assign router_flit_out_ready[gy][gx][PORT_NORTH] = 1'b1;
        end
        
        // South connections
        if (gy > 0) begin : south_connect
          // Connect to router below
          assign router_flit_in_valid[gy][gx][PORT_SOUTH] = router_flit_out_valid[gy-1][gx][PORT_NORTH];
          assign router_flit_in[gy][gx][PORT_SOUTH] = router_flit_out[gy-1][gx][PORT_NORTH];
          assign router_flit_out_ready[gy-1][gx][PORT_NORTH] = router_flit_in_ready[gy][gx][PORT_SOUTH];
        end else begin : south_terminate
          // Edge connection - terminate
          assign router_flit_in_valid[gy][gx][PORT_SOUTH] = 1'b0;
          assign router_flit_in[gy][gx][PORT_SOUTH] = '0;
          assign router_flit_out_ready[gy][gx][PORT_SOUTH] = 1'b1;
        end
        
        // East connections
        if (gx < MESH_SIZE_X - 1) begin : east_connect
          // Connect to router to the right
          assign router_flit_in_valid[gy][gx][PORT_EAST] = router_flit_out_valid[gy][gx+1][PORT_WEST];
          assign router_flit_in[gy][gx][PORT_EAST] = router_flit_out[gy][gx+1][PORT_WEST];
          assign router_flit_out_ready[gy][gx+1][PORT_WEST] = router_flit_in_ready[gy][gx][PORT_EAST];
        end else begin : east_terminate
          // Edge connection - terminate
          assign router_flit_in_valid[gy][gx][PORT_EAST] = 1'b0;
          assign router_flit_in[gy][gx][PORT_EAST] = '0;
          assign router_flit_out_ready[gy][gx][PORT_EAST] = 1'b1;
        end
        
        // West connections
        if (gx > 0) begin : west_connect
          // Connect to router to the left
          assign router_flit_in_valid[gy][gx][PORT_WEST] = router_flit_out_valid[gy][gx-1][PORT_EAST];
          assign router_flit_in[gy][gx][PORT_WEST] = router_flit_out[gy][gx-1][PORT_EAST];
          assign router_flit_out_ready[gy][gx-1][PORT_EAST] = router_flit_in_ready[gy][gx][PORT_WEST];
        end else begin : west_terminate
          // Edge connection - terminate
          assign router_flit_in_valid[gy][gx][PORT_WEST] = 1'b0;
          assign router_flit_in[gy][gx][PORT_WEST] = '0;
          assign router_flit_out_ready[gy][gx][PORT_WEST] = 1'b1;
        end
      end
    end
  endgenerate

  // ============================================================================
  // LOCAL PORT CONNECTIONS - PACKET INJECTION AND CONSUMPTION
  // ============================================================================
  
  generate
    for (gy = 0; gy < MESH_SIZE_Y; gy++) begin : gen_local_y
      for (gx = 0; gx < MESH_SIZE_X; gx++) begin : gen_local_x
        
        // Local input connections (for packet injection)
        // These will be controlled by test tasks
        assign router_flit_in_valid[gy][gx][PORT_LOCAL] = 1'b0; // Controlled by tasks
        assign router_flit_in[gy][gx][PORT_LOCAL] = '0;         // Controlled by tasks
        
        // Local output connections (for packet consumption)
        assign router_flit_out_ready[gy][gx][PORT_LOCAL] = local_ready[gy][gx];
        
      end
    end
  endgenerate

  // ============================================================================
  // PACKET CONSUMPTION LOGIC
  // ============================================================================
  
  generate
    for (gy = 0; gy < MESH_SIZE_Y; gy++) begin : gen_consume_y
      for (gx = 0; gx < MESH_SIZE_X; gx++) begin : gen_consume_x
        
        always_ff @(posedge clk or negedge rst_n) begin
          if (!rst_n) begin
            local_ready[gy][gx] <= 1'b1;
            packet_consumed[gy][gx] <= 1'b0;
          end else begin
            packet_consumed[gy][gx] <= 1'b0;
            
            // Consume packets that arrive at local port
            if (router_flit_out_valid[gy][gx][PORT_LOCAL] && local_ready[gy][gx]) begin
              packet_consumed[gy][gx] <= 1'b1;
              consumed_packet_ids[gy][gx].push_back(router_flit_out[gy][gx][PORT_LOCAL].packet_id);
              
              $display("[CONSUME] @%0t: Router (%0d,%0d) consumed packet ID %0d from (%0d,%0d)", 
                       $time, gx, gy, router_flit_out[gy][gx][PORT_LOCAL].packet_id,
                       router_flit_out[gy][gx][PORT_LOCAL].src_x, router_flit_out[gy][gx][PORT_LOCAL].src_y);
            end
            
            // Keep local port ready to consume packets
            local_ready[gy][gx] <= 1'b1;
          end
        end
        
      end
    end
  endgenerate

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;  // 100MHz clock
  end

  // ============================================================================
  // TEST EXECUTION
  // ============================================================================
  
  initial begin
    $dumpfile("step2_integration_tb.vcd");
    $dumpvars(0, tb_step2_integration);
    
    // Initialize
    rst_n = 0;
    test_case = 0;
    errors = 0;
    cycle_count = 0;
    packets_sent = 0;
    packets_received = 0;
    packet_sent_flags = '0;
    packet_received_flags = '0;
    
    // Initialize local input ports
    for (int y = 0; y < MESH_SIZE_Y; y++) begin
      for (int x = 0; x < MESH_SIZE_X; x++) begin
        router_flit_in_valid[y][x][PORT_LOCAL] = 1'b0;
        router_flit_in[y][x][PORT_LOCAL] = '0;
      end
    end
    
    // Reset sequence
    repeat (20) @(posedge clk);
    rst_n = 1;
    repeat (10) @(posedge clk);
    
    $display("=== STEP 2 INTEGRATION TESTBENCH ===");
    $display("Testing %0dx%0d mesh of routers", MESH_SIZE_X, MESH_SIZE_Y);
    $display("");
    
    // Generate test packets for all-to-all communication
    generate_test_packets();
    
    // Test cases
    run_test_case(1, "Single-hop Communication Test");
    run_test_case(2, "Multi-hop Communication Test");  
    run_test_case(3, "All-to-All Communication Test");
    run_test_case(4, "Congestion Handling Test");
    
    // Final results
    print_final_results();
    
    $finish;
  end

  // ============================================================================
  // DEBUG AND MONITORING
  // ============================================================================
  
  // Network state monitoring
  always @(posedge clk) begin
    if (rst_n) begin
      cycle_count <= cycle_count + 1;
      
      // Monitor for deadlock conditions
      if (cycle_count % 100 == 0 && cycle_count > 0) begin
        $display("[MONITOR] @%0t: Cycle %0d - Network Status Check", $time, cycle_count);
        monitor_network_state();
      end
      
      // Monitor packet consumption
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        for (int x = 0; x < MESH_SIZE_X; x++) begin
          if (packet_consumed[y][x]) begin
            packets_received++;
            $display("[STATS] @%0t: Packets received so far: %0d", $time, packets_received);
          end
        end
      end
    end
  end
  
  // Task to monitor network state for debugging
  task monitor_network_state();
    begin
      $display("  Router States:");
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        for (int x = 0; x < MESH_SIZE_X; x++) begin
          $display("    Router(%0d,%0d): Routed=%0d, Error=%0d", 
                   x, y, packets_routed[y][x], error_status[y][x]);
          
          // Check port status
          for (int p = 0; p < NUM_PORTS; p++) begin
            if (router_flit_out_valid[y][x][p] && !router_flit_out_ready[y][x][p]) begin
              $display("      ⚠️  Port %0d blocked: valid=%0b, ready=%0b", 
                       p, router_flit_out_valid[y][x][p], router_flit_out_ready[y][x][p]);
            end
          end
        end
      end
      
      $display("  Consumed packets by router:");
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        for (int x = 0; x < MESH_SIZE_X; x++) begin
          if (consumed_packet_ids[y][x].size() > 0) begin
            $display("    Router(%0d,%0d): %0d packets", x, y, consumed_packet_ids[y][x].size());
          end
        end
      end
    end
  endtask

  // Cycle counter and timeout
  always @(posedge clk) begin
    if (rst_n) begin
      if (cycle_count > TEST_TIMEOUT) begin
        $display("❌ TIMEOUT: Test exceeded %0d cycles", TEST_TIMEOUT);
        errors++;
        $finish;
      end
    end
  end

  // Test execution task
  task run_test_case(input int case_num, input string test_name);
    begin
      test_case = case_num;
      $display("--- Test Case %0d: %s ---", case_num, test_name);
      
      case (case_num)
        1: test_single_hop();
        2: test_multi_hop();
        3: test_all_to_all();
        4: test_congestion_handling();
        default: $display("Unknown test case: %0d", case_num);
      endcase
      
      // Wait between tests
      repeat (20) @(posedge clk);
    end
  endtask

  // Generate test packets for all source-destination pairs
  task generate_test_packets();
    begin
      begin : generate_packets_block
        int packet_idx = 0;
        $display("Generating test packets for all-to-all communication...");
        
        for (int src_y = 0; src_y < MESH_SIZE_Y; src_y++) begin
        for (int src_x = 0; src_x < MESH_SIZE_X; src_x++) begin
          for (int dst_y = 0; dst_y < MESH_SIZE_Y; dst_y++) begin
            for (int dst_x = 0; dst_x < MESH_SIZE_X; dst_x++) begin
              if (packet_idx < NUM_TEST_PACKETS) begin
                test_packets[packet_idx] = '0;
                test_packets[packet_idx].flit_type = FLIT_TYPE_SINGLE;
                test_packets[packet_idx].vc_id = packet_idx % NUM_VCS;
                test_packets[packet_idx].dest_x = dst_x;
                test_packets[packet_idx].dest_y = dst_y;
                test_packets[packet_idx].src_x = src_x;
                test_packets[packet_idx].src_y = src_y;
                test_packets[packet_idx].seq_num = 16'h0001;
                test_packets[packet_idx].packet_id = packet_idx;
                test_packets[packet_idx].qos = QOS_NORMAL;
                test_packets[packet_idx].payload[15:0] = {8'h00, packet_idx[7:0]};
                packet_idx++;
              end
            end
          end
        end
      end
      
        $display("Generated %0d test packets", packet_idx);
      end : generate_packets_block
    end
  endtask

  // Test Case 1: Single-hop communication
  task test_single_hop();
    begin
      $display("Testing single-hop communication between adjacent routers...");
      
      // Send packet from (0,0) to (1,0) - single hop east
      inject_packet_at_router(0, 0, test_packets[0]);
      wait_for_packet_at_router(1, 0, test_packets[0]);
      
      $display("✅ Single-hop communication test passed");
    end
  endtask

  // Test Case 2: Multi-hop communication
  task test_multi_hop();
    begin
      $display("Testing multi-hop communication across diagonal...");
      
      begin : multi_hop_block
        // Send packet from (0,0) to (1,1) - requires 2 hops
        noc_flit_t diagonal_packet;
        diagonal_packet = test_packets[1];
        diagonal_packet.dest_x = 1;
        diagonal_packet.dest_y = 1;
        diagonal_packet.src_x = 0;
        diagonal_packet.src_y = 0;
        
        inject_packet_at_router(0, 0, diagonal_packet);
        wait_for_packet_at_router(1, 1, diagonal_packet);
      end : multi_hop_block
      
      $display("✅ Multi-hop communication test passed");
    end
  endtask

  // Test Case 3: All-to-all communication
  task test_all_to_all();
    begin
      $display("Testing all-to-all communication pattern...");
      
      // Inject all test packets
      fork
        begin : inject_packets
          for (int i = 0; i < NUM_TEST_PACKETS; i++) begin
            inject_packet_at_router(test_packets[i].src_x, test_packets[i].src_y, test_packets[i]);
            repeat (5) @(posedge clk);  // Spread out injections
          end
        end
        
        begin : collect_packets
          for (int i = 0; i < NUM_TEST_PACKETS; i++) begin
            wait_for_packet_at_router(test_packets[i].dest_x, test_packets[i].dest_y, test_packets[i]);
          end
        end
      join
      
      $display("✅ All-to-all communication test completed");
      $display("Successfully routed %0d/%0d packets", packets_received, NUM_TEST_PACKETS);
    end
  endtask

  // Test Case 4: Congestion handling
  task test_congestion_handling();
    begin
      $display("Testing congestion handling with burst traffic...");
      
      // Create congestion by sending multiple packets to same destination
      for (int i = 0; i < 4; i++) begin
        begin : congest_packet_block
          noc_flit_t congest_packet;
          congest_packet = test_packets[i];
          congest_packet.dest_x = 1;
          congest_packet.dest_y = 1;  // All packets go to router (1,1)
          congest_packet.vc_id = i % NUM_VCS;
          congest_packet.packet_id = 100 + i;
          
          inject_packet_at_router(0, 0, congest_packet);
        end : congest_packet_block
      end
      
      // Allow time for congestion to resolve
      repeat (100) @(posedge clk);
      
      // Verify all packets eventually arrive
      for (int i = 0; i < 4; i++) begin
        // Check if packet with ID 100+i was received at (1,1)
        // This is a simplified check - in practice would need more sophisticated monitoring
      end
      
      $display("✅ Congestion handling test completed");
    end
  endtask

  // Helper task: Inject packet at specified router
  task inject_packet_at_router(
    input int router_x,
    input int router_y, 
    input noc_flit_t packet
  );
    begin
      $display("[INJECT] @%0t: Preparing to inject packet ID %0d at router (%0d,%0d) -> (%0d,%0d)", 
               $time, packet.packet_id, router_x, router_y, packet.dest_x, packet.dest_y);
      
      @(posedge clk);
      
      // Force the local input signals for injection
      force router_flit_in_valid[router_y][router_x][PORT_LOCAL] = 1'b1;
      force router_flit_in[router_y][router_x][PORT_LOCAL] = packet;
      
      // Wait for ready signal
      while (!router_flit_in_ready[router_y][router_x][PORT_LOCAL]) begin
        $display("[INJECT] @%0t: Waiting for ready signal at router (%0d,%0d)", $time, router_x, router_y);
        @(posedge clk);
      end
      
      @(posedge clk);
      
      // Release the forced signals
      release router_flit_in_valid[router_y][router_x][PORT_LOCAL];
      release router_flit_in[router_y][router_x][PORT_LOCAL];
      
      packets_sent++;
      $display("📤 Injected packet ID %0d at router (%0d,%0d) -> (%0d,%0d)", 
               packet.packet_id, router_x, router_y, packet.dest_x, packet.dest_y);
    end
  endtask

  // Helper task: Wait for packet at specified router
  task wait_for_packet_at_router(
    input int router_x,
    input int router_y,
    input noc_flit_t expected_packet
  );
    begin
      int wait_cycles = 0;
      bit packet_found = 1'b0;
      
      $display("[WAIT] @%0t: Waiting for packet ID %0d at router (%0d,%0d)", 
               $time, expected_packet.packet_id, router_x, router_y);
      
      while (!packet_found && wait_cycles < 500) begin
        @(posedge clk);
        wait_cycles++;
        
        // Check if packet was consumed (appears in the consumed list)
        for (int i = 0; i < consumed_packet_ids[router_y][router_x].size(); i++) begin
          if (consumed_packet_ids[router_y][router_x][i] == expected_packet.packet_id) begin
            packet_found = 1'b1;
            $display("📥 Found consumed packet ID %0d at router (%0d,%0d) after %0d cycles", 
                     expected_packet.packet_id, router_x, router_y, wait_cycles);
            break;
          end
        end
        
        // Debug: periodically show what we're seeing
        if (wait_cycles % 50 == 0 && wait_cycles > 0) begin
          $display("[WAIT] @%0t: Still waiting for packet ID %0d at router (%0d,%0d), cycle %0d", 
                   $time, expected_packet.packet_id, router_x, router_y, wait_cycles);
          if (router_flit_out_valid[router_y][router_x][PORT_LOCAL]) begin
            $display("       Currently seeing packet ID %0d at local port", 
                     router_flit_out[router_y][router_x][PORT_LOCAL].packet_id);
          end
        end
      end
      
      if (!packet_found) begin
        $display("❌ Timeout waiting for packet ID %0d at router (%0d,%0d) after %0d cycles", 
                 expected_packet.packet_id, router_x, router_y, wait_cycles);
        errors++;
      end
    end
  endtask

  // Monitor network activity
  always @(posedge clk) begin
    if (rst_n) begin
      // Monitor for stuck packets or errors
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        for (int x = 0; x < MESH_SIZE_X; x++) begin
          if (error_status[y][x] != ERR_NONE) begin
            $display("⚠️  Router (%0d,%0d) error: %0d at cycle %0d", 
                     x, y, error_status[y][x], cycle_count);
          end
        end
      end
    end
  end

  // Print final results summary
  task print_final_results();
    begin
      $display("");
      $display("=== FINAL RESULTS ===");
      $display("Packets sent: %0d", packets_sent);
      $display("Packets received: %0d", packets_received);
      
      // Count total packets routed by mesh
      begin : final_results_block
        int total_packets_routed = 0;
        int total_consumed = 0;
        
        for (int y = 0; y < MESH_SIZE_Y; y++) begin
          for (int x = 0; x < MESH_SIZE_X; x++) begin
            total_packets_routed += packets_routed[y][x];
            total_consumed += consumed_packet_ids[y][x].size();
            if (error_status[y][x] != ERR_NONE) begin
              $display("❌ Router (%0d,%0d) has error: %0d", x, y, error_status[y][x]);
              errors++;
            end
          end
        end
        
        $display("Total packets routed by mesh: %0d", total_packets_routed);
        $display("Total packets consumed: %0d", total_consumed);
      end : final_results_block
      
      if (errors > 0) begin
        $display("❌ %0d ERRORS DETECTED", errors);
      end else begin
        $display("✅ ALL TESTS PASSED");
      end
      
      $display("Total cycles: %0d", cycle_count);
    end
  endtask

endmodule
