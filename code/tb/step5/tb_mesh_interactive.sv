/**
 * Interactive Progressive Testbench for Nebula Mesh Topology
 * 
 * This testbench allows step-by-step testing of mesh functionality
 * with user interaction and detailed debugging information.
 * 
 * Features:
 * - Progressive test stages
 * - Interactive user control
 * - Detailed state monitoring
 * - Congestion detection
 * - Manual packet injection
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: September 2025
 */

`timescale 1ns/1ps

module tb_mesh_interactive;

  import nebula_pkg::*;

  // =============================================================================
  // TESTBENCH PARAMETERS
  // =============================================================================
  
  parameter int CLK_PERIOD = 10;
  parameter int MESH_SIZE_X = 2; // Start with 2x2 mesh
  parameter int MESH_SIZE_Y = 2;
  parameter int MAX_CYCLES = 1000;
  
  // Test stages
  typedef enum {
    STAGE_INIT,
    STAGE_RESET_CHECK,
    STAGE_BASIC_CONNECTIVITY,
    STAGE_SINGLE_PACKET,
    STAGE_BIDIRECTIONAL,
    STAGE_MULTI_HOP,
    STAGE_CONGESTION_TEST,
    STAGE_COMPLETE
  } test_stage_e;
  
  test_stage_e current_stage = STAGE_INIT;
  
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
  logic user_continue = 0;
  logic test_active = 0;
  int cycle_count = 0;
  int packet_id_counter = 1;
  
  // Monitoring
  int total_packets_sent = 0;
  int total_packets_received = 0;
  logic [31:0] last_activity_cycle = 0;
  
  // =============================================================================
  // CLOCK AND RESET
  // =============================================================================
  
  always #(CLK_PERIOD/2) clk = ~clk;
  
  // Cycle counter
  always @(posedge clk) begin
    if (rst_n) cycle_count++;
  end
  
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
  // INITIALIZATION AND UTILITY TASKS
  // =============================================================================
  
  // Initialize all local ports
  task init_local_ports();
    $display("[INIT] Initializing local ports...");
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        local_flit_in_valid[x][y] = 1'b0;
        local_flit_in[x][y] = '0;
        local_flit_out_ready[x][y] = 1'b1;
      end
    end
    $display("[INIT] Local ports initialized");
  endtask
  
  // Display mesh status
  task display_mesh_status();
    $display("\n=== MESH STATUS (Cycle %0d) ===", cycle_count);
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        $display("Router[%0d][%0d]: ready=%b, packets_routed=%0d, error=%s", 
                 x, y, local_flit_in_ready[x][y], packets_routed[x][y],
                 error_status[x][y].name());
      end
    end
    $display("Total sent: %0d, Total received: %0d", total_packets_sent, total_packets_received);
    $display("================================\n");
  endtask
  
  // Wait for user input
  task wait_for_user();
    $display("\n>>> Press ENTER to continue or 'q' to quit...");
    user_continue = 0;
    // In a real simulation, this would wait for user input
    // For automated testing, we'll add a small delay
    #(CLK_PERIOD * 50);
    user_continue = 1;
  endtask
  
  // Create a test flit
  function automatic noc_flit_t create_test_flit(
    input logic [COORD_WIDTH-1:0] src_x, src_y,
    input logic [COORD_WIDTH-1:0] dest_x, dest_y,
    input flit_type_e flit_type,
    input logic [PACKET_ID_WIDTH-1:0] packet_id
  );
    noc_flit_t flit;
    flit.flit_type = flit_type;
    flit.vc_id = VC_REQ;
    flit.dest_x = dest_x;
    flit.dest_y = dest_y;
    flit.src_x = src_x;
    flit.src_y = src_y;
    flit.seq_num = 16'(packet_id);
    flit.packet_id = packet_id;
    flit.qos = QOS_NORMAL;
    flit.payload = {16'hCAFE, 16'(packet_id)}; // Identifiable payload
    return flit;
  endfunction
  
  // Send a packet with timeout and monitoring
  task automatic send_packet_monitored(
    input logic [COORD_WIDTH-1:0] src_x, src_y,
    input logic [COORD_WIDTH-1:0] dest_x, dest_y,
    output logic success
  );
    noc_flit_t flit;
    int wait_cycles = 0;
    
    flit = create_test_flit(src_x, src_y, dest_x, dest_y, FLIT_TYPE_SINGLE, packet_id_counter);
    
    $display("[SEND] Packet %0d: (%0d,%0d) -> (%0d,%0d)", 
             packet_id_counter, src_x, src_y, dest_x, dest_y);
    
    // Try to inject packet
    local_flit_in_valid[src_x][src_y] = 1'b1;
    local_flit_in[src_x][src_y] = flit;
    
    // Wait for acceptance with timeout
    while (!local_flit_in_ready[src_x][src_y] && wait_cycles < MAX_CYCLES) begin
      @(posedge clk);
      wait_cycles++;
      if (wait_cycles % 100 == 0) begin
        $display("[SEND] Waiting for router[%0d][%0d] ready... (cycle %0d)", src_x, src_y, wait_cycles);
      end
    end
    
    if (wait_cycles >= MAX_CYCLES) begin
      $display("[SEND] ❌ TIMEOUT: Router[%0d][%0d] never became ready!", src_x, src_y);
      success = 1'b0;
    end else begin
      @(posedge clk);
      $display("[SEND] ✅ Packet %0d injected after %0d cycles", packet_id_counter, wait_cycles);
      total_packets_sent++;
      success = 1'b1;
    end
    
    // Clear signals
    local_flit_in_valid[src_x][src_y] = 1'b0;
    local_flit_in[src_x][src_y] = '0;
    
    packet_id_counter++;
  endtask
  
  // Wait for packet reception with monitoring
  task automatic wait_for_packet_monitored(
    input logic [COORD_WIDTH-1:0] dest_x, dest_y,
    input logic [PACKET_ID_WIDTH-1:0] expected_packet_id,
    output logic success
  );
    int wait_cycles = 0;
    
    $display("[RECV] Waiting for packet %0d at (%0d,%0d)...", expected_packet_id, dest_x, dest_y);
    
    while (wait_cycles < MAX_CYCLES) begin
      @(posedge clk);
      wait_cycles++;
      
      if (local_flit_out_valid[dest_x][dest_y]) begin
        if (local_flit_out[dest_x][dest_y].packet_id == expected_packet_id) begin
          $display("[RECV] ✅ Packet %0d received at (%0d,%0d) after %0d cycles", 
                   expected_packet_id, dest_x, dest_y, wait_cycles);
          $display("[RECV]   Payload: 0x%08x", local_flit_out[dest_x][dest_y].payload);
          total_packets_received++;
          success = 1'b1;
          return;
        end else begin
          $display("[RECV] Unexpected packet %0d (expected %0d)", 
                   local_flit_out[dest_x][dest_y].packet_id, expected_packet_id);
        end
      end
      
      if (wait_cycles % 100 == 0) begin
        $display("[RECV] Still waiting... (cycle %0d)", wait_cycles);
      end
    end
    
    $display("[RECV] ❌ TIMEOUT: Packet %0d never received at (%0d,%0d)!", 
             expected_packet_id, dest_x, dest_y);
    success = 1'b0;
  endtask

  // =============================================================================
  // PROGRESSIVE TEST STAGES
  // =============================================================================
  
  // Stage 1: Reset and Initialization Check
  task automatic stage_reset_check();
    logic success = 1'b1;
    
    $display("\n" + "="*60);
    $display("STAGE 1: RESET AND INITIALIZATION CHECK");
    $display("="*60);
    
    display_mesh_status();
    
    // Check all routers are in good state
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        if (error_status[x][y] != ERR_NONE) begin
          $display("❌ Router[%0d][%0d] has error: %s", x, y, error_status[x][y].name());
          success = 1'b0;
        end
        if (!local_flit_in_ready[x][y]) begin
          $display("❌ Router[%0d][%0d] local port not ready", x, y);
          success = 1'b0;
        end
      end
    end
    
    if (success) begin
      $display("✅ All routers initialized correctly");
    end
    
    wait_for_user();
  endtask
  
  // Stage 2: Basic Connectivity Test
  task stage_basic_connectivity();
    $display("\n" + "="*60);
    $display("STAGE 2: BASIC CONNECTIVITY TEST");
    $display("="*60);
    
    $display("Testing if routers can accept and forward flits...");
    
    // Test each router can accept input
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        if (local_flit_in_ready[x][y]) begin
          $display("✅ Router[%0d][%0d] ready to accept flits", x, y);
        end else begin
          $display("❌ Router[%0d][%0d] NOT ready", x, y);
        end
      end
    end
    
    wait_for_user();
  endtask
  
  // Stage 3: Single Packet Test
  task stage_single_packet();
    logic send_success, recv_success;
    
    $display("\n" + "="*60);
    $display("STAGE 3: SINGLE PACKET TEST");
    $display("="*60);
    
    $display("Sending single packet from (0,0) to (0,0) (loopback)...");
    
    send_packet_monitored(0, 0, 0, 0, send_success);
    
    if (send_success) begin
      wait_for_packet_monitored(0, 0, packet_id_counter-1, recv_success);
      if (recv_success) begin
        $display("✅ Loopback test passed!");
      end
    end
    
    display_mesh_status();
    wait_for_user();
  endtask
  
  // Stage 4: Bidirectional Test
  task stage_bidirectional();
    logic send_success, recv_success;
    
    $display("\n" + "="*60);
    $display("STAGE 4: BIDIRECTIONAL TEST");
    $display("="*60);
    
    if (MESH_SIZE_X > 1) begin
      $display("Testing bidirectional communication between (0,0) and (1,0)...");
      
      // Send from (0,0) to (1,0)
      send_packet_monitored(0, 0, 1, 0, send_success);
      if (send_success) begin
        wait_for_packet_monitored(1, 0, packet_id_counter-1, recv_success);
      end
      
      #(CLK_PERIOD * 20); // Small gap
      
      // Send from (1,0) to (0,0)
      send_packet_monitored(1, 0, 0, 0, send_success);
      if (send_success) begin
        wait_for_packet_monitored(0, 0, packet_id_counter-1, recv_success);
      end
    end else begin
      $display("Skipping bidirectional test (mesh too small)");
    end
    
    display_mesh_status();
    wait_for_user();
  endtask
  
  // Stage 5: Multi-hop Test
  task stage_multi_hop();
    logic send_success, recv_success;
    
    $display("\n" + "="*60);
    $display("STAGE 5: MULTI-HOP TEST");
    $display("="*60);
    
    if (MESH_SIZE_X > 1 && MESH_SIZE_Y > 1) begin
      $display("Testing multi-hop communication from (0,0) to (1,1)...");
      
      send_packet_monitored(0, 0, 1, 1, send_success);
      if (send_success) begin
        wait_for_packet_monitored(1, 1, packet_id_counter-1, recv_success);
        if (recv_success) begin
          $display("✅ Multi-hop test passed!");
        end
      end
    end else begin
      $display("Skipping multi-hop test (mesh too small)");
    end
    
    display_mesh_status();
    wait_for_user();
  endtask
  
  // Stage 6: Controlled Congestion Test
  task automatic stage_congestion_test();
    logic send_success, recv_success;
    int packets_to_send = 3; // Small number to avoid deadlock
    
    $display("\n" + "="*60);
    $display("STAGE 6: CONTROLLED CONGESTION TEST");
    $display("="*60);
    
    $display("Sending %0d packets with small delays...", packets_to_send);
    
    for (int i = 0; i < packets_to_send; i++) begin
      $display("\n--- Packet %0d of %0d ---", i+1, packets_to_send);
      
      send_packet_monitored(0, 0, 1, 1, send_success);
      
      if (send_success) begin
        // Don't wait for reception immediately - let them accumulate
        $display("Packet %0d injected, continuing...", i+1);
      end else begin
        $display("Failed to inject packet %0d", i+1);
        break;
      end
      
      #(CLK_PERIOD * 10); // Small delay between injections
    end
    
    $display("\nNow waiting for all packets to be received...");
    
    // Wait for all packets - calculate expected IDs before the loop
    begin
      int start_id = packet_id_counter - packets_to_send;
      for (int i = 0; i < packets_to_send; i++) begin
        int expected_id = start_id + i;
        wait_for_packet_monitored(1, 1, expected_id, recv_success);
      end
    end
    
    display_mesh_status();
    wait_for_user();
  endtask

  // =============================================================================
  // MONITORING AND SAFETY
  // =============================================================================
  
  // Activity monitoring
  always @(posedge clk) begin
    if (rst_n && test_active) begin
      // Check for any activity
      for (int x = 0; x < MESH_SIZE_X; x++) begin
        for (int y = 0; y < MESH_SIZE_Y; y++) begin
          if (local_flit_in_valid[x][y] || local_flit_out_valid[x][y]) begin
            last_activity_cycle = cycle_count;
          end
        end
      end
      
      // Detect potential deadlock
      if (cycle_count > last_activity_cycle + 500) begin
        $display("\n⚠️  WARNING: No activity for 500 cycles - potential deadlock!");
        $display("Last activity at cycle %0d, current cycle %0d", last_activity_cycle, cycle_count);
        display_mesh_status();
      end
    end
  end

  // =============================================================================
  // MAIN TEST SEQUENCE
  // =============================================================================
  
  initial begin
    $display("=============================================================================");
    $display("NEBULA MESH INTERACTIVE TESTBENCH");
    $display("Mesh Size: %0dx%0d", MESH_SIZE_X, MESH_SIZE_Y);
    $display("=============================================================================");
    $display("This testbench will run progressive tests with user interaction.");
    $display("Each stage will wait for user confirmation before proceeding.");
    
    // Initialize
    init_local_ports();
    
    // Wait for reset
    wait(rst_n);
    #(CLK_PERIOD * 10);
    test_active = 1;
    last_activity_cycle = cycle_count;
    
    // Run progressive tests
    current_stage = STAGE_RESET_CHECK;
    stage_reset_check();
    
    current_stage = STAGE_BASIC_CONNECTIVITY;
    stage_basic_connectivity();
    
    current_stage = STAGE_SINGLE_PACKET;
    stage_single_packet();
    
    current_stage = STAGE_BIDIRECTIONAL;
    stage_bidirectional();
    
    current_stage = STAGE_MULTI_HOP;
    stage_multi_hop();
    
    current_stage = STAGE_CONGESTION_TEST;
    stage_congestion_test();
    
    current_stage = STAGE_COMPLETE;
    
    // Final report
    $display("\n=============================================================================");
    $display("INTERACTIVE TEST COMPLETE");
    $display("=============================================================================");
    $display("Total packets sent: %0d", total_packets_sent);
    $display("Total packets received: %0d", total_packets_received);
    
    if (total_packets_sent == total_packets_received) begin
      $display("🎉 ALL PACKETS SUCCESSFULLY TRANSMITTED! 🎉");
    end else begin
      $display("⚠️  Packet loss detected: %0d packets lost", 
               total_packets_sent - total_packets_received);
    end
    
    display_mesh_status();
    $display("=============================================================================");
    $finish;
  end

  // =============================================================================
  // SAFETY TIMEOUT
  // =============================================================================
  
  initial begin
    #(CLK_PERIOD * 50000); // Large timeout for interactive use
    $display("\n💥 TESTBENCH TIMEOUT! 💥");
    $display("Current stage: %s", current_stage.name());
    $display("Total runtime exceeded maximum allowed.");
    display_mesh_status();
    $finish;
  end

endmodule
