`timescale 1ns / 1ps

// =============================================================================
// Nebula Mesh Comprehensive Test (Non-Interactive)
// =============================================================================
// This testbench runs a comprehensive test of the mesh router without
// user interaction, designed for automated validation.

module tb_mesh_comprehensive;
  import nebula_pkg::*;

  // =============================================================================
  // PARAMETERS AND CONSTANTS
  // =============================================================================
  
  // Mesh configuration
  localparam int MESH_SIZE_X = 2;
  localparam int MESH_SIZE_Y = 2;
  localparam int COORD_WIDTH = 2;
  localparam int MAX_CYCLES = 2000;   // Timeout per operation
  localparam int TOTAL_TIMEOUT = 10000; // Total test timeout
  
  // Timing
  localparam time CLK_PERIOD = 10ns;
  localparam time RST_DURATION = 100ns;

  // =============================================================================
  // CLOCK AND RESET
  // =============================================================================
  
  logic clk = 0;
  logic rst_n = 0;
  
  always #(CLK_PERIOD/2) clk = ~clk;
  
  initial begin
    rst_n = 0;
    #RST_DURATION;
    rst_n = 1;
  end

  // =============================================================================
  // MESH INSTANTIATION
  // =============================================================================
  
  // Local port arrays for easy access
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_in_valid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_in_ready;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_in;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_out_valid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_out_ready;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_out;
  
  // Instantiate the mesh
  nebula_axi_system #(
    .MESH_SIZE_X(MESH_SIZE_X),
    .MESH_SIZE_Y(MESH_SIZE_Y)
  ) mesh_system (
    .clk(clk),
    .rst_n(rst_n),
    .local_flit_in_valid(local_flit_in_valid),
    .local_flit_in_ready(local_flit_in_ready),
    .local_flit_in(local_flit_in),
    .local_flit_out_valid(local_flit_out_valid),
    .local_flit_out_ready(local_flit_out_ready),
    .local_flit_out(local_flit_out)
  );

  // =============================================================================
  // TEST CONTROL AND TRACKING
  // =============================================================================
  
  int total_packets_sent = 0;
  int total_packets_received = 0;
  int packet_id_counter = 1;
  int cycle_count = 0;
  logic test_active = 0;
  
  // Cycle counter
  always @(posedge clk) begin
    if (rst_n) cycle_count++;
  end

  // =============================================================================
  // INITIALIZATION
  // =============================================================================
  
  initial begin
    // Initialize all local ports
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        local_flit_in_valid[x][y] = 1'b0;
        local_flit_in[x][y] = '0;
        local_flit_out_ready[x][y] = 1'b1; // Always ready to receive
      end
    end
  end

  // =============================================================================
  // UTILITY FUNCTIONS
  // =============================================================================
  
  // Create test flit
  function automatic noc_flit_t create_test_flit(
    input logic [COORD_WIDTH-1:0] src_x, src_y,
    input logic [COORD_WIDTH-1:0] dest_x, dest_y,
    input flit_type_t flit_type,
    input logic [PACKET_ID_WIDTH-1:0] packet_id
  );
    noc_flit_t flit;
    flit.src_x = src_x;
    flit.src_y = src_y;
    flit.dest_x = dest_x;
    flit.dest_y = dest_y;
    flit.flit_type = flit_type;
    flit.packet_id = packet_id;
    flit.payload = 32'hDEAD0000 + packet_id; // Unique payload per packet
    flit.vc_id = 0; // Use VC 0 for all tests
    return flit;
  endfunction

  // =============================================================================
  // TEST TASKS
  // =============================================================================
  
  // Send packet with monitoring
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
    end
    
    $display("[RECV] ❌ TIMEOUT: Packet %0d never received at (%0d,%0d)!", 
             expected_packet_id, dest_x, dest_y);
    success = 1'b0;
  endtask

  // =============================================================================
  // MAIN TEST SEQUENCE
  // =============================================================================
  
  initial begin
    $display("=============================================================================");
    $display("NEBULA MESH COMPREHENSIVE TESTBENCH");
    $display("Mesh Size: %0dx%0d", MESH_SIZE_X, MESH_SIZE_Y);
    $display("=============================================================================");
    
    logic send_success, recv_success;
    int test_num = 1;
    
    // Wait for reset
    wait(rst_n);
    #(CLK_PERIOD * 10);
    test_active = 1;
    
    // =============================================================================
    // TEST 1: Loopback Test
    // =============================================================================
    $display("\n--- TEST %0d: LOOPBACK ---", test_num++);
    send_packet_monitored(0, 0, 0, 0, send_success);
    if (send_success) begin
      wait_for_packet_monitored(0, 0, packet_id_counter-1, recv_success);
    end
    
    // Small delay between tests
    #(CLK_PERIOD * 20);
    
    // =============================================================================
    // TEST 2: Single Hop East
    // =============================================================================
    if (MESH_SIZE_X > 1) begin
      $display("\n--- TEST %0d: SINGLE HOP EAST ---", test_num++);
      send_packet_monitored(0, 0, 1, 0, send_success);
      if (send_success) begin
        wait_for_packet_monitored(1, 0, packet_id_counter-1, recv_success);
      end
      #(CLK_PERIOD * 20);
    end
    
    // =============================================================================
    // TEST 3: Single Hop North (if possible)
    // =============================================================================
    if (MESH_SIZE_Y > 1) begin
      $display("\n--- TEST %0d: SINGLE HOP NORTH ---", test_num++);
      send_packet_monitored(0, 0, 0, 1, send_success);
      if (send_success) begin
        wait_for_packet_monitored(0, 1, packet_id_counter-1, recv_success);
      end
      #(CLK_PERIOD * 20);
    end
    
    // =============================================================================
    // TEST 4: Multi-hop Diagonal
    // =============================================================================
    if (MESH_SIZE_X > 1 && MESH_SIZE_Y > 1) begin
      $display("\n--- TEST %0d: MULTI-HOP DIAGONAL ---", test_num++);
      send_packet_monitored(0, 0, 1, 1, send_success);
      if (send_success) begin
        wait_for_packet_monitored(1, 1, packet_id_counter-1, recv_success);
      end
      #(CLK_PERIOD * 20);
    end
    
    // =============================================================================
    // TEST 5: Reverse Path
    // =============================================================================
    if (MESH_SIZE_X > 1 && MESH_SIZE_Y > 1) begin
      $display("\n--- TEST %0d: REVERSE PATH ---", test_num++);
      send_packet_monitored(1, 1, 0, 0, send_success);
      if (send_success) begin
        wait_for_packet_monitored(0, 0, packet_id_counter-1, recv_success);
      end
      #(CLK_PERIOD * 20);
    end
    
    // =============================================================================
    // TEST 6: Bidirectional Communication
    // =============================================================================
    if (MESH_SIZE_X > 1) begin
      $display("\n--- TEST %0d: BIDIRECTIONAL ---", test_num++);
      
      // Send from (0,0) to (1,0)
      send_packet_monitored(0, 0, 1, 0, send_success);
      int packet_a_id = packet_id_counter - 1;
      
      // Small delay
      #(CLK_PERIOD * 5);
      
      // Send from (1,0) to (0,0)
      send_packet_monitored(1, 0, 0, 0, send_success);
      int packet_b_id = packet_id_counter - 1;
      
      // Wait for both
      if (send_success) begin
        wait_for_packet_monitored(1, 0, packet_a_id, recv_success);
        wait_for_packet_monitored(0, 0, packet_b_id, recv_success);
      end
      
      #(CLK_PERIOD * 20);
    end
    
    // =============================================================================
    // FINAL REPORT
    // =============================================================================
    $display("\n=============================================================================");
    $display("COMPREHENSIVE TEST COMPLETE");
    $display("=============================================================================");
    $display("Total packets sent: %0d", total_packets_sent);
    $display("Total packets received: %0d", total_packets_received);
    
    if (total_packets_sent == total_packets_received) begin
      $display("🎉 ALL PACKETS SUCCESSFULLY TRANSMITTED! 🎉");
      $display("✅ MESH ROUTER TEST PASSED!");
    end else begin
      $display("⚠️  Packet loss detected: %0d packets lost", 
               total_packets_sent - total_packets_received);
      $display("❌ MESH ROUTER TEST FAILED!");
    end
    
    // Router status
    $display("\nRouter Status:");
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        $display("  Router[%0d][%0d]: ready=%b", x, y, local_flit_in_ready[x][y]);
      end
    end
    
    $display("=============================================================================");
    $finish;
  end

  // =============================================================================
  // SAFETY TIMEOUT
  // =============================================================================
  
  initial begin
    #(CLK_PERIOD * TOTAL_TIMEOUT);
    $display("\n💥 TESTBENCH TIMEOUT! 💥");
    $display("Test exceeded maximum runtime.");
    $display("Total packets sent: %0d", total_packets_sent);
    $display("Total packets received: %0d", total_packets_received);
    $finish;
  end

endmodule
