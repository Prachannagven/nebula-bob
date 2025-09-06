/**
 * Simple Router Testbench for Flow Control Debugging
 * 
 * This testbench tests a single router in isolation to debug
 * the flow control and deadlock issues identified in the mesh test.
 * 
 * Focus Areas:
 * - Virtual channel buffer management
 * - Switch allocation persistence
 * - Backpressure handling
 * - Multi-packet injection
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: September 2025
 */

`timescale 1ns/1ps

module tb_router_simple;

  import nebula_pkg::*;

  // =============================================================================
  // TESTBENCH PARAMETERS
  // =============================================================================
  
  parameter int CLK_PERIOD = 10;
  parameter int ROUTER_X = 1;
  parameter int ROUTER_Y = 1;
  parameter int TEST_TIMEOUT = 500; // Shorter timeout for quick tests
  
  // Clock and reset
  logic clk = 0;
  logic rst_n = 0;
  
  // Router interfaces
  logic [NUM_PORTS-1:0] flit_in_valid;
  noc_flit_t [NUM_PORTS-1:0] flit_in;
  logic [NUM_PORTS-1:0] flit_in_ready;
  
  logic [NUM_PORTS-1:0] flit_out_valid;
  noc_flit_t [NUM_PORTS-1:0] flit_out;
  logic [NUM_PORTS-1:0] flit_out_ready;
  
  // Debug and monitoring
  logic [NUM_PORTS-1:0][NUM_VCS-1:0] vc_status;
  logic [PERF_COUNTER_WIDTH-1:0] packets_routed;
  error_code_e error_status;
  
  // Test control
  int cycle_count = 0;
  int packets_sent = 0;
  int packets_received = 0;
  int packet_id_counter = 1;
  
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
  
  nebula_router #(
    .ROUTER_X(ROUTER_X),
    .ROUTER_Y(ROUTER_Y),
    .MESH_SIZE_X(3),
    .MESH_SIZE_Y(3)
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

  // =============================================================================
  // INITIALIZATION AND UTILITY TASKS
  // =============================================================================
  
  // Initialize all ports
  task automatic init_ports();
    for (int i = 0; i < NUM_PORTS; i++) begin
      flit_in_valid[i] = 1'b0;
      flit_in[i] = '0;
      flit_out_ready[i] = 1'b1; // All output ports ready to receive
    end
  endtask
  
  // Create a test flit
  function automatic noc_flit_t create_flit(
    input logic [COORD_WIDTH-1:0] dest_x, dest_y,
    input logic [2:0] input_port,
    input logic [PACKET_ID_WIDTH-1:0] packet_id
  );
    noc_flit_t flit;
    flit.flit_type = FLIT_TYPE_SINGLE;
    flit.vc_id = VC_REQ;
    flit.dest_x = dest_x;
    flit.dest_y = dest_y;
    flit.src_x = ROUTER_X;
    flit.src_y = ROUTER_Y;
    flit.seq_num = 16'(packet_id);
    flit.packet_id = packet_id;
    flit.qos = QOS_NORMAL;
    flit.payload = {16'hABCD, 16'(packet_id)};
    return flit;
  endfunction
  
  // Inject a single flit and monitor
  task automatic inject_flit(
    input logic [2:0] input_port,
    input logic [COORD_WIDTH-1:0] dest_x, dest_y,
    output logic success
  );
    noc_flit_t flit;
    int wait_cycles = 0;
    
    flit = create_flit(dest_x, dest_y, input_port, packet_id_counter);
    
    $display("[INJECT] Port %0d: Packet %0d to (%0d,%0d) at cycle %0d", 
             input_port, packet_id_counter, dest_x, dest_y, cycle_count);
    
    // Try to inject
    flit_in_valid[input_port] = 1'b1;
    flit_in[input_port] = flit;
    
    // Wait for ready
    while (!flit_in_ready[input_port] && wait_cycles < TEST_TIMEOUT) begin
      @(posedge clk);
      wait_cycles++;
    end
    
    @(posedge clk);
    flit_in_valid[input_port] = 1'b0;
    flit_in[input_port] = '0;
    
    if (wait_cycles >= TEST_TIMEOUT) begin
      $display("[INJECT] ❌ TIMEOUT: Port %0d not ready after %0d cycles", input_port, wait_cycles);
      success = 1'b0;
    end else begin
      $display("[INJECT] ✅ Injected after %0d cycles", wait_cycles);
      packets_sent++;
      success = 1'b1;
    end
    
    packet_id_counter++;
  endtask
  
  // Monitor output for packet reception
  task automatic monitor_output(
    input int expected_packets,
    input int timeout_cycles
  );
    int received = 0;
    int cycles = 0;
    
    $display("[MONITOR] Waiting for %0d packets...", expected_packets);
    
    while (received < expected_packets && cycles < timeout_cycles) begin
      @(posedge clk);
      cycles++;
      
      // Check all output ports
      for (int port = 0; port < NUM_PORTS; port++) begin
        if (flit_out_valid[port] && flit_out_ready[port]) begin
          received++;
          packets_received++;
          $display("[MONITOR] ✅ Packet %0d received on port %0d (total: %0d)", 
                   flit_out[port].packet_id, port, received);
        end
      end
    end
    
    if (received < expected_packets) begin
      $display("[MONITOR] ❌ Only received %0d/%0d packets in %0d cycles", 
               received, expected_packets, cycles);
    end else begin
      $display("[MONITOR] ✅ All %0d packets received in %0d cycles", 
               received, cycles);
    end
  endtask
  
  // Display router status
  task automatic display_status();
    $display("\n=== ROUTER STATUS (Cycle %0d) ===", cycle_count);
    $display("Packets routed: %0d", packets_routed);
    $display("Error status: %s", error_status.name());
    $display("Input ready states: %b", flit_in_ready);
    $display("Output valid states: %b", flit_out_valid);
    $display("Total sent: %0d, received: %0d", packets_sent, packets_received);
    
    // VC status for local port (port 4)
    $display("Local port VC status: %b", vc_status[PORT_LOCAL]);
    $display("==================================\n");
  endtask

  // =============================================================================
  // TEST CASES
  // =============================================================================
  
  // Test 1: Single packet loopback
  task automatic test_single_loopback();
    logic success;
    
    $display("\n" + "="*60);
    $display("TEST 1: SINGLE PACKET LOOPBACK");
    $display("="*60);
    
    // Inject packet destined for local router
    inject_flit(PORT_LOCAL, ROUTER_X, ROUTER_Y, success);
    
    if (success) begin
      monitor_output(1, TEST_TIMEOUT);
    end
    
    display_status();
  endtask
  
  // Test 2: Single packet forwarding
  task automatic test_single_forward();
    logic success;
    
    $display("\n" + "="*60);
    $display("TEST 2: SINGLE PACKET FORWARDING");
    $display("="*60);
    
    // Inject packet from local port, destined for different location
    inject_flit(PORT_LOCAL, ROUTER_X+1, ROUTER_Y, success);
    
    if (success) begin
      monitor_output(1, TEST_TIMEOUT);
    end
    
    display_status();
  endtask
  
  // Test 3: Back-to-back packets
  task automatic test_back_to_back();
    logic success1, success2;
    
    $display("\n" + "="*60);
    $display("TEST 3: BACK-TO-BACK PACKETS");
    $display("="*60);
    
    // Inject two packets quickly
    inject_flit(PORT_LOCAL, ROUTER_X, ROUTER_Y, success1);
    #(CLK_PERIOD * 2); // Small delay
    inject_flit(PORT_LOCAL, ROUTER_X, ROUTER_Y, success2);
    
    if (success1 && success2) begin
      monitor_output(2, TEST_TIMEOUT * 2);
    end
    
    display_status();
  endtask
  
  // Test 4: Multiple input ports
  task automatic test_multiple_inputs();
    logic success_local, success_north;
    
    $display("\n" + "="*60);
    $display("TEST 4: MULTIPLE INPUT PORTS");
    $display("="*60);
    
    // Inject from local port
    inject_flit(PORT_LOCAL, ROUTER_X, ROUTER_Y, success_local);
    
    #(CLK_PERIOD * 5);
    
    // Inject from north port (simulating incoming packet)
    inject_flit(PORT_NORTH, ROUTER_X, ROUTER_Y, success_north);
    
    if (success_local && success_north) begin
      monitor_output(2, TEST_TIMEOUT * 2);
    end
    
    display_status();
  endtask
  
  // Test 5: Stress test - rapid injection
  task automatic test_stress();
    logic success;
    int packets_to_send = 5;
    
    $display("\n" + "="*60);
    $display("TEST 5: STRESS TEST - RAPID INJECTION");
    $display("="*60);
    
    // Inject multiple packets rapidly
    for (int i = 0; i < packets_to_send; i++) begin
      inject_flit(PORT_LOCAL, ROUTER_X, ROUTER_Y, success);
      if (!success) begin
        $display("Failed to inject packet %0d", i+1);
        break;
      end
      #(CLK_PERIOD); // Minimal delay
    end
    
    monitor_output(packets_to_send, TEST_TIMEOUT * packets_to_send);
    display_status();
  endtask

  // =============================================================================
  // MAIN TEST SEQUENCE
  // =============================================================================
  
  initial begin
    $display("=============================================================================");
    $display("SIMPLE ROUTER FLOW CONTROL TESTBENCH");
    $display("Router Position: (%0d,%0d)", ROUTER_X, ROUTER_Y);
    $display("=============================================================================");
    
    // Initialize
    init_ports();
    
    // Wait for reset
    wait(rst_n);
    #(CLK_PERIOD * 10);
    
    // Run progressive tests
    test_single_loopback();
    #(CLK_PERIOD * 20);
    
    test_single_forward();
    #(CLK_PERIOD * 20);
    
    test_back_to_back();
    #(CLK_PERIOD * 20);
    
    test_multiple_inputs();
    #(CLK_PERIOD * 20);
    
    test_stress();
    #(CLK_PERIOD * 20);
    
    // Final report
    $display("\n=============================================================================");
    $display("ROUTER TEST SUMMARY");
    $display("=============================================================================");
    $display("Total packets sent: %0d", packets_sent);
    $display("Total packets received: %0d", packets_received);
    
    if (packets_sent == packets_received) begin
      $display("🎉 ALL PACKETS SUCCESSFULLY ROUTED! 🎉");
    end else begin
      $display("⚠️  Packet loss detected: %0d packets lost", 
               packets_sent - packets_received);
    end
    
    display_status();
    $display("=============================================================================");
    $finish;
  end

  // =============================================================================
  // SAFETY TIMEOUT
  // =============================================================================
  
  initial begin
    #(CLK_PERIOD * 10000);
    $display("\n💥 TESTBENCH TIMEOUT! 💥");
    $display("Router may be deadlocked.");
    display_status();
    $finish;
  end

endmodule
