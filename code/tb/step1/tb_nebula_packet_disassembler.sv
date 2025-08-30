/**
 * Testbench for nebula_packet_disassembler module
 *
 * Tests:
 * - Single flit packet disassembly
 * - Multi-flit packet disassembly
 * - Header extraction
 * - Payload reconstruction
 * - Sequence number verification
 * - Error detection
 * - Flow control with ready signals
 */

`timescale 1ns/1ps

import nebula_pkg::*;

module tb_nebula_packet_disassembler;

  // Parameters
  parameter int MAX_PAYLOAD_SIZE = 1024;
  parameter int FLITS_PER_PACKET = 4;

  // Clock and reset
  logic clk;
  logic rst_n;

  // Flit input interface
  logic                              flit_valid;
  noc_flit_t                         flit_in;
  logic                              flit_ready;

  // Packet output interface
  logic                              pkt_valid;
  logic [COORD_WIDTH-1:0]            src_x, src_y;
  logic [COORD_WIDTH-1:0]            dest_x, dest_y;
  logic [VC_ID_WIDTH-1:0]            vc_id;
  logic [QOS_WIDTH-1:0]              qos;
  logic [MAX_PAYLOAD_SIZE*8-1:0]     payload_data;
  logic [$clog2(MAX_PAYLOAD_SIZE)-1:0] payload_size;
  logic                              pkt_ready;

  // Error reporting
  logic                              error_detected;
  error_code_e                       error_code;

  // Test variables
  int error_count = 0;
  int test_count = 0;
  logic [127:0] test_payload;

  // DUT instantiation
  nebula_packet_disassembler #(
    .MAX_PAYLOAD_SIZE(MAX_PAYLOAD_SIZE),
    .FLITS_PER_PACKET(FLITS_PER_PACKET)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .flit_valid(flit_valid),
    .flit_in(flit_in),
    .flit_ready(flit_ready),
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
    .error_detected(error_detected),
    .error_code(error_code)
  );

  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // Test stimulus
  initial begin
    $display("=== NEBULA PACKET DISASSEMBLER TESTBENCH START ===");

    // Initialize
    rst_n = 0;
    flit_valid = 0;
    pkt_ready = 1;
    flit_in = '0;

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

    // Test 4: Header extraction
    test_header_extraction();

    // Test 5: Payload reconstruction
    test_payload_reconstruction();

    // Test 6: Sequence number verification
    test_sequence_verification();

    // Test 7: Error detection
    test_error_detection();

    // Test 8: Flow control
    test_flow_control();

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

    if (flit_ready !== 1'b1) begin
      $error("Expected flit_ready=1, got %b", flit_ready);
      error_count++;
    end

    if (pkt_valid !== 1'b0) begin
      $error("Expected pkt_valid=0, got %b", pkt_valid);
      error_count++;
    end

    if (error_detected !== 1'b0) begin
      $error("Expected error_detected=0, got %b", error_detected);
      error_count++;
    end

    $display("Initial state test completed");
  endtask

  // Test 2: Single flit packet
  task test_single_flit_packet();
    $display("\n--- Test 2: Single Flit Packet ---");
    test_count++;

    // Send single flit packet
    @(posedge clk);
    flit_valid = 1;
    flit_in.flit_type = FLIT_TYPE_SINGLE;
    flit_in.src_x = 1;
    flit_in.src_y = 2;
    flit_in.dest_x = 3;
    flit_in.dest_y = 4;
    flit_in.vc_id = 0;
    flit_in.qos = 8;
    flit_in.seq_num = 1;
    flit_in.packet_id = 1;
    flit_in.payload = 64'hDEADBEEFCAFEBABE;

    wait(flit_ready);
    @(posedge clk);
    flit_valid = 0;

    // Wait for packet to be assembled
    wait(pkt_valid);
    @(posedge clk);

    if (src_x !== 1 || src_y !== 2) begin
      $error("Source coordinates mismatch");
      error_count++;
    end

    if (dest_x !== 3 || dest_y !== 4) begin
      $error("Destination coordinates mismatch");
      error_count++;
    end

    if (vc_id !== 0) begin
      $error("VC ID mismatch");
      error_count++;
    end

    if (qos !== 8) begin
      $error("QoS mismatch");
      error_count++;
    end

    $display("Single flit packet test completed");
  endtask

  // Test 3: Multi-flit packet
  task test_multi_flit_packet();
    logic [255:0] test_payload_256;
    
    $display("\n--- Test 3: Multi-Flit Packet ---");
    test_count++;

    test_payload_256 = 256'hDEADBEEFCAFEBABE0123456789ABCDEF0123456789ABCDEF0123456789ABCDEF;

    // Send HEAD flit (first 208 bits)
    @(posedge clk);
    flit_valid = 1;
    flit_in.flit_type = FLIT_TYPE_HEAD;
    flit_in.src_x = 0;
    flit_in.src_y = 0;
    flit_in.dest_x = 1;
    flit_in.dest_y = 1;
    flit_in.vc_id = 1;
    flit_in.qos = 12;
    flit_in.seq_num = 2;
    flit_in.packet_id = 2;
    flit_in.payload = test_payload_256[207:0];  // First 208 bits

    wait(flit_ready);
    @(posedge clk);

    // Send TAIL flit (remaining 48 bits)
    flit_in.flit_type = FLIT_TYPE_TAIL;
    flit_in.seq_num = 2;  // Same sequence number for same packet
    flit_in.packet_id = 2; // Same packet ID
    flit_in.payload = {160'h0, test_payload_256[255:208]}; // Remaining 48 bits, padded

    wait(flit_ready);
    @(posedge clk);
    flit_valid = 0;

    // Wait for packet to be assembled
    wait(pkt_valid);
    @(posedge clk);

    if (src_x !== 0 || src_y !== 0) begin
      $error("Multi-flit source coordinates mismatch");
      error_count++;
    end

    if (dest_x !== 1 || dest_y !== 1) begin
      $error("Multi-flit destination coordinates mismatch");
      error_count++;
    end

    if (payload_data[255:0] !== test_payload_256) begin
      $error("Multi-flit payload reconstruction failed: expected %h, got %h", 
             test_payload_256, payload_data[255:0]);
      error_count++;
    end

    $display("Multi-flit packet test completed");
  endtask

  // Test 4: Header extraction
  task test_header_extraction();
    $display("\n--- Test 4: Header Extraction ---");
    test_count++;

    // Send packet with specific header values
    @(posedge clk);
    flit_valid = 1;
    flit_in.flit_type = FLIT_TYPE_SINGLE;
    flit_in.src_x = 5;
    flit_in.src_y = 6;
    flit_in.dest_x = 7;
    flit_in.dest_y = 8;
    flit_in.vc_id = 2;
    flit_in.qos = 15;
    flit_in.seq_num = 3;
    flit_in.packet_id = 3;
    flit_in.payload = 64'h123456789ABCDEF0;

    wait(flit_ready);
    @(posedge clk);
    flit_valid = 0;

    wait(pkt_valid);
    @(posedge clk);

    if (src_x !== 5 || src_y !== 6) begin
      $error("Header extraction: source coordinates incorrect");
      error_count++;
    end

    if (dest_x !== 7 || dest_y !== 8) begin
      $error("Header extraction: destination coordinates incorrect");
      error_count++;
    end

    if (vc_id !== 2) begin
      $error("Header extraction: VC ID incorrect");
      error_count++;
    end

    if (qos !== 15) begin
      $error("Header extraction: QoS incorrect");
      error_count++;
    end

    $display("Header extraction test completed");
  endtask

  // Test 5: Payload reconstruction
  task test_payload_reconstruction();
    $display("\n--- Test 5: Payload Reconstruction ---");
    test_count++;

    test_payload = {64'hFEDCBA9876543210, 64'h0123456789ABCDEF};

    // Send SINGLE flit (128-bit payload fits in one flit)
    @(posedge clk);
    flit_valid = 1;
    flit_in.flit_type = FLIT_TYPE_SINGLE;
    flit_in.seq_num = 100;
    flit_in.packet_id = 50;
    // Real assembler puts payload in lower bits, zero-padded to 208 bits
    flit_in.payload = {80'h0, test_payload[127:0]};  // 208 bits total

    wait(flit_ready);
    @(posedge clk);
    flit_valid = 0;

    wait(pkt_valid);
    @(posedge clk);

    if (payload_data[127:0] !== test_payload) begin
      $error("Payload reconstruction failed: expected %h, got %h", test_payload, payload_data[127:0]);
      error_count++;
    end

    $display("Payload reconstruction test completed");
  endtask

  // Test 6: Sequence number verification
  task test_sequence_verification();
    $display("\n--- Test 6: Sequence Number Verification ---");
    test_count++;

    // Send packet with sequence number
    @(posedge clk);
    flit_valid = 1;
    flit_in.flit_type = FLIT_TYPE_SINGLE;
    flit_in.seq_num = 10;
    flit_in.packet_id = 5;
    flit_in.payload = 64'hAAAAAAAA;

    wait(flit_ready);
    @(posedge clk);
    flit_valid = 0;

    wait(pkt_valid);
    @(posedge clk);

    // Send another packet with same sequence number (should be OK for single flit)
    @(posedge clk);
    flit_valid = 1;
    flit_in.flit_type = FLIT_TYPE_SINGLE;
    flit_in.seq_num = 10;
    flit_in.packet_id = 6;  // Different packet ID
    flit_in.payload = 64'hBBBBBBBB;

    wait(flit_ready);
    @(posedge clk);
    flit_valid = 0;

    wait(pkt_valid);
    @(posedge clk);

    if (error_detected) begin
      $error("Unexpected error detected in sequence verification test");
      error_count++;
    end

    $display("Sequence number verification test completed");
  endtask

  // Test 7: Error detection
  task test_error_detection();
    $display("\n--- Test 7: Error Detection ---");
    test_count++;

    // Send HEAD flit
    @(posedge clk);
    flit_valid = 1;
    flit_in.flit_type = FLIT_TYPE_HEAD;
    flit_in.seq_num = 20;
    flit_in.packet_id = 10;
    flit_in.payload = 64'h11111111;

    wait(flit_ready);
    @(posedge clk);

    // Send BODY flit with wrong sequence number
    flit_in.flit_type = FLIT_TYPE_BODY;
    flit_in.seq_num = 22;  // Wrong sequence number (should be 21)
    flit_in.packet_id = 10;
    flit_in.payload = 64'h22222222;

    wait(flit_ready);
    @(posedge clk);
    flit_valid = 0;

    // Wait a few cycles for error detection
    repeat(5) @(posedge clk);

    if (!error_detected) begin
      $error("Expected error detection for sequence number mismatch");
      error_count++;
    end

    if (error_code !== ERR_PROTOCOL) begin
      $error("Expected ERR_PROTOCOL, got %h", error_code);
      error_count++;
    end

    $display("Error detection test completed");
  endtask

  // Test 8: Flow control
  task test_flow_control();
    $display("\n--- Test 8: Flow Control ---");
    test_count++;

    // Test with pkt_ready = 0
    pkt_ready = 0;

    @(posedge clk);
    flit_valid = 1;
    flit_in.flit_type = FLIT_TYPE_SINGLE;
    flit_in.payload = 64'h33333333;

    wait(flit_ready);
    @(posedge clk);
    flit_valid = 0;

    // Packet should be assembled but not consumed
    wait(pkt_valid);
    @(posedge clk);

    // Should still have pkt_valid high since not accepted
    if (!pkt_valid) begin
      $error("Expected pkt_valid=1 when pkt_ready=0");
      error_count++;
    end

    // Now accept the packet
    pkt_ready = 1;
    @(posedge clk);

    if (pkt_valid) begin
      $error("Expected pkt_valid=0 after accepting packet");
      error_count++;
    end

    $display("Flow control test completed");
  endtask

endmodule
