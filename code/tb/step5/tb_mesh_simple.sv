`timescale 1ns / 1ps

//==============================================================================
// Simple Mesh Test - Minimal deadlock reproduction
//==============================================================================

module tb_mesh_simple;
  import nebula_pkg::*;

  // Clock and reset
  logic clk = 0;
  logic rst_n = 0;
  
  // Parameters
  localparam int MESH_SIZE_X = 2;
  localparam int MESH_SIZE_Y = 2;
  localparam time CLK_PERIOD = 10ns;
  
  // Local interfaces
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_in_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_in;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_in_ready;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_out_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_out;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_out_ready;
  
  // Status outputs (not used in this simple test)
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0][NUM_VCS-1:0] vc_status;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][PERF_COUNTER_WIDTH-1:0] packets_routed;
  error_code_e [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] error_status;
  
  // DUT
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
  
  // Clock generation
  always #(CLK_PERIOD/2) clk = ~clk;
  
  // Variables
  int cycle_count = 0;
  int packet_id = 1;
  
  // Track packets
  logic packet_sent = 0;
  logic packet_received = 0;
  
  // Always accept output flits
  always_comb begin
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        local_flit_out_ready[x][y] = 1'b1;
      end
    end
  end
  
  // Initialize all inputs
  initial begin
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        local_flit_in_valid[x][y] = 1'b0;
        local_flit_in[x][y] = '0;
      end
    end
  end
  
  // Create test flit
  function automatic noc_flit_t make_flit(
    logic [COORD_WIDTH-1:0] src_x, src_y,
    logic [COORD_WIDTH-1:0] dest_x, dest_y
  );
    noc_flit_t flit;
    flit.flit_type = FLIT_TYPE_SINGLE;
    flit.vc_id = VC_REQ;
    flit.dest_x = dest_x;
    flit.dest_y = dest_y;
    flit.src_x = src_x;
    flit.src_y = src_y;
    flit.seq_num = 16'(packet_id);
    flit.packet_id = packet_id;
    flit.qos = QOS_NORMAL;
    flit.payload = {16'hDEAD, 16'(packet_id)};
    return flit;
  endfunction
  
  // Monitor output
  always @(posedge clk) begin
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        if (local_flit_out_valid[x][y] && local_flit_out_ready[x][y]) begin
          $display("[RECV] @%0t: Packet %0d received at (%0d,%0d)", 
                   $time, local_flit_out[x][y].packet_id, x, y);
          packet_received = 1;
        end
      end
    end
  end
  
  // Cycle counter
  always @(posedge clk) begin
    if (rst_n) cycle_count <= cycle_count + 1;
    else cycle_count <= 0;
  end
  
  // Test sequence
  initial begin
    // Initialize
    packet_sent = 0;
    packet_received = 0;
    
    // Apply reset
    rst_n = 0;
    repeat(10) @(posedge clk);
    rst_n = 1;
    repeat(5) @(posedge clk);
    
    $display("=== SIMPLE MESH TEST STARTING ===");
    $display("Testing (0,0) -> (1,0) packet transmission");
    
    // Send single packet from (0,0) to (1,0)
    packet_id = 1;
    local_flit_in_valid[0][0] = 1'b1;
    local_flit_in[0][0] = make_flit(0, 0, 1, 0);
    packet_sent = 1;
    
    $display("[SEND] @%0t: Sending packet %0d from (0,0) to (1,0)", $time, packet_id);
    
    // Wait for acceptance
    wait(local_flit_in_ready[0][0]);
    @(posedge clk);
    local_flit_in_valid[0][0] = 1'b0;
    
    $display("[SEND] @%0t: Packet accepted by router", $time);
    
    // Wait for reception or timeout
    fork
      begin
        wait(packet_received);
        $display("✅ SUCCESS: Packet received!");
      end
      begin
        repeat(1000) @(posedge clk);
        if (!packet_received) begin
          $display("❌ TIMEOUT: Packet not received within 1000 cycles");
          
          // Debug router status
          $display("\n=== DEBUG INFO ===");
          $display("Router[0][0] debug:");
          $display("  packets_routed = %0d", packets_routed[0][0]);
          $display("Router[1][0] debug:");  
          $display("  packets_routed = %0d", packets_routed[1][0]);
        end
      end
    join_any
    
    #(CLK_PERIOD * 50);
    
    $display("=== SIMPLE MESH TEST COMPLETE ===");
    $finish;
  end
  
  // Monitor for deadlock
  always @(posedge clk) begin
    if (rst_n && packet_sent && !packet_received) begin
      if (cycle_count > 0 && cycle_count % 100 == 0) begin
        $display("[DEBUG] @%0t: Cycle %0d - still waiting for packet", $time, cycle_count);
      end
    end
  end
  
endmodule
