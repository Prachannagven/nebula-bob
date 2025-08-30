/**
 * Testbench for nebula_packet_assembler module
 *
 * Tests:
 * - Single flit packet assembly
 * - Multi-flit packet assembly
 * - Header generation
 * - Payload data handling
 * - Sequence number management
 * - Flow control with ready signals
 */

`timescale 1ns/1ps

import nebula_pkg::*;

module tb_nebula_packet_assembler;

  // Parameters
  parameter int MAX_PAYLOAD_SIZE = 1024;
  parameter int FLITS_PER_PACKET = 4;

  // Clock and reset
  logic clk;
  logic rst_n;

  // Packet input interface
  logic                              pkt_valid;
  logic [COORD_WIDTH-1:0]            src_x, src_y;
  logic [COORD_WIDTH-1:0]            dest_x, dest_y;
  logic [VC_ID_WIDTH-1:0]            vc_id;
  logic [QOS_WIDTH-1:0]              qos;
  logic [MAX_PAYLOAD_SIZE*8-1:0]     payload_data;
  logic [$clog2(MAX_PAYLOAD_SIZE)-1:0] payload_size;
  logic                              pkt_ready;

  // Flit output interface
  logic                              flit_valid;
  noc_flit_t                         flit_out;
  logic                              flit_ready;

  // Status
  logic                              busy;

  // Test variables
  int error_count = 0;
  int test_count = 0;
  logic [63:0] test_payload;
  logic [SEQ_NUM_WIDTH-1:0] first_seq, second_seq;

  // DUT instantiation
  nebula_packet_assembler #(
    .MAX_PAYLOAD_SIZE(MAX_PAYLOAD_SIZE),
    .FLITS_PER_PACKET(FLITS_PER_PACKET)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .pkt_valid(pkt_valid),
    .src_x(src_x),
    .src_y(src_y),
    .dest_x(dest_x),
    .dest_y(dest_y),
    .vc_id(vc_id),
    .qos(qos),
    .payload_data(payload_data),
    .payload_size(payload_size),
    .pkt_ready(pkt_ready),
    .flit_valid(flit_valid),
    .flit_out(flit_out),
    .flit_ready(flit_ready),
    .busy(busy)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test stimulus
  initial begin
    $display("=== NEBULA PACKET ASSEMBLER TESTBENCH START ===");

    // Initialize
    rst_n = 0;
    pkt_valid = 0;
    flit_ready = 1;
    src_x = 0;
    src_y = 0;
    dest_x = 1;
    dest_y = 1;
    vc_id = 0;
    qos = 8;
    payload_data = 0;
    payload_size = 0;

    // Reset
    repeat(3) @(posedge clk);
    rst_n = 1;
    @(posedge clk);

    // Test 1: Initial state
    test_initial_state();

    // Test 2: Single flit packet
    test_single_flit_packet();

    // Test 3: Multi-flit packet
    test_multi_flit_packet();

    // Test 4: Header generation
    test_header_generation();

    // Test 5: Payload data integrity
    test_payload_integrity();

    // Test 6: Flow control
    test_flow_control();

    // Test 7: Sequence number management
    test_sequence_numbers();

    // Summary
    $display("\n=== TEST SUMMARY ===");
    $display("Total tests: %0d", test_count);
    $display("Errors: %0d", error_count);
    if (error_count == 0) begin
      $display("*** ALL TESTS PASSED ***");
    end else begin
      $display("*** %0d TESTS FAILED ***", error_count);
    end

    $finish;
  end

  // Test 1: Initial state
  task test_initial_state();
    $display("\n--- Test 1: Initial State ---");
    test_count++;

    if (pkt_ready !== 1'b1) begin
      $error("Expected pkt_ready=1, got %b", pkt_ready);
      error_count++;
    end

    if (flit_valid !== 1'b0) begin
      $error("Expected flit_valid=0, got %b", flit_valid);
      error_count++;
    end

    if (busy !== 1'b0) begin
      $error("Expected busy=0, got %b", busy);
      error_count++;
    end

    $display("Initial state test completed");
  endtask

  // Test 2: Single flit packet
  task test_single_flit_packet();
    $display("\n--- Test 2: Single Flit Packet ---");
    test_count++;

    // Send small packet that fits in one flit
    @(posedge clk);
    pkt_valid = 1;
    payload_data = 64'hDEADBEEFCAFEBABE;
    payload_size = 8;  // 8 bytes

    wait(pkt_ready);
    @(posedge clk);
    pkt_valid = 0;

    // Wait for flit to be generated
    wait(flit_valid);
    
    if (flit_out.flit_type !== FLIT_TYPE_SINGLE) begin
      $error("Expected SINGLE flit type, got %b", flit_out.flit_type);
      error_count++;
    end
    
    if (flit_out.src_x !== src_x || flit_out.src_y !== src_y) begin
      $error("Source coordinates mismatch: expected (%0d,%0d), got (%0d,%0d)", src_x, src_y, flit_out.src_x, flit_out.src_y);
      error_count++;
    end

    if (flit_out.dest_x !== dest_x || flit_out.dest_y !== dest_y) begin
      $error("Destination coordinates mismatch: expected (%0d,%0d), got (%0d,%0d)", dest_x, dest_y, flit_out.dest_x, flit_out.dest_y);
      error_count++;
    end

    $display("Single flit packet test completed");
  endtask

  // Test 3: Multi-flit packet
  task test_multi_flit_packet();
    $display("\n--- Test 3: Multi-Flit Packet ---");
    test_count++;

    // Send larger packet that requires multiple flits
    @(posedge clk);
    pkt_valid = 1;
    // Use a larger payload size that definitely needs multiple flits
    // With PAYLOAD_BITS_PER_FLIT = 208 bits, let's use 500 bits = ~63 bytes
    payload_size = 63;  // 63 bytes = 504 bits, should need 3 flits: (504+208-1)/208 = 3

    wait(pkt_ready);
    @(posedge clk);
    pkt_valid = 0;

    // Wait for first flit (HEAD)
    wait(flit_valid);
    
    if (flit_out.flit_type !== FLIT_TYPE_HEAD) begin
      $error("Expected HEAD flit type, got %b", flit_out.flit_type);
      error_count++;
    end

    @(posedge clk);

    // Wait for second flit (BODY)  
    wait(flit_valid);

    if (flit_out.flit_type !== FLIT_TYPE_BODY) begin
      $error("Expected BODY flit type, got %b", flit_out.flit_type);
      error_count++;
    end

    @(posedge clk);

    // Wait for third flit (TAIL)
    wait(flit_valid);

    if (flit_out.flit_type !== FLIT_TYPE_TAIL) begin
      $error("Expected TAIL flit type, got %b", flit_out.flit_type);
      error_count++;
    end

    $display("Multi-flit packet test completed");
  endtask

  // Test 4: Header generation
  task test_header_generation();
    $display("\n--- Test 4: Header Generation ---");
    test_count++;

    // Test with different parameters
    src_x = 2;
    src_y = 3;
    dest_x = 5;
    dest_y = 7;
    vc_id = 1;
    qos = 12;

    @(posedge clk);
    pkt_valid = 1;
    payload_data = 64'h123456789ABCDEF0;
    payload_size = 8;

    wait(pkt_ready);
    @(posedge clk);
    pkt_valid = 0;

    wait(flit_valid);

    if (flit_out.src_x !== 2 || flit_out.src_y !== 3) begin
      $error("Header source coordinates incorrect");
      error_count++;
    end

    if (flit_out.dest_x !== 5 || flit_out.dest_y !== 7) begin
      $error("Header destination coordinates incorrect");
      error_count++;
    end

    if (flit_out.vc_id !== 1) begin
      $error("Header VC ID incorrect");
      error_count++;
    end

    if (flit_out.qos !== 12) begin
      $error("Header QoS incorrect");
      error_count++;
    end

    $display("Header generation test completed");
  endtask

  // Test 5: Payload data integrity
  task test_payload_integrity();
    $display("\n--- Test 5: Payload Data Integrity ---");
    test_count++;

    // Test with known payload
    test_payload = 64'hFEDCBA9876543210;

    @(posedge clk);
    pkt_valid = 1;
    payload_data = test_payload;
    payload_size = 8;

    wait(pkt_ready);
    @(posedge clk);
    pkt_valid = 0;

    wait(flit_valid);

    // Check if payload is correctly embedded in flit
    if (flit_out.payload !== test_payload[FLIT_WIDTH-48-1:0]) begin
      $error("Payload data mismatch in flit");
      error_count++;
    end

    $display("Payload integrity test completed");
  endtask

  // Test 6: Flow control
  task test_flow_control();
    $display("\n--- Test 6: Flow Control ---");
    test_count++;

    // Test with flit_ready = 0
    flit_ready = 0;

    @(posedge clk);
    pkt_valid = 1;
    payload_data = 64'h1111111122222222;
    payload_size = 8;

    @(posedge clk);  // Wait for transfer to start
    pkt_valid = 0;

    // Flit should be generated but not consumed
    wait(flit_valid);
    @(posedge clk);

    // Should still be busy since flit wasn't accepted
    if (!busy) begin
      $error("Expected busy=1 when flit_ready=0");
      error_count++;
    end

    // Now accept the flit
    flit_ready = 1;
    @(posedge clk);

    if (busy) begin
      $error("Expected busy=0 after accepting flit");
      error_count++;
    end

    $display("Flow control test completed");
  endtask

  // Test 7: Sequence number management
  task test_sequence_numbers();
    $display("\n--- Test 7: Sequence Number Management ---");
    test_count++;

    // First packet
    @(posedge clk);
    pkt_valid = 1;
    payload_data = 64'hAAAAAAAA;
    payload_size = 8;

    @(posedge clk);  // Wait for transfer to start
    pkt_valid = 0;

    wait(flit_valid);
    first_seq = flit_out.seq_num;

    // Wait for packet to complete
    wait(!busy);
    @(posedge clk);

    // Second packet
    @(posedge clk);
    pkt_valid = 1;
    payload_data = 64'hBBBBBBBB;
    payload_size = 8;

    @(posedge clk);  // Wait for transfer to start
    pkt_valid = 0;

    wait(flit_valid);
    second_seq = flit_out.seq_num;

    if (second_seq !== first_seq + 1) begin
      $error("Sequence number not incremented correctly: %h -> %h", first_seq, second_seq);
      error_count++;
    end

    $display("Sequence number test completed");
  endtask

endmodule
