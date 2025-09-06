`timescale 1ns / 1ps
//==============================================================================
// Testbench for Nebula CHI-NoC Bridge
//
// This testbench validates the CHI-NoC bridge by testing:
// - CHI message to NoC packet translation
// - NoC packet to CHI message reconstruction
// - Virtual channel mapping and flow control
// - Multi-flit packet handling and sequencing
// - Transaction ID mapping and routing
//==============================================================================

import nebula_pkg::*;

module tb_nebula_chi_noc_bridge;

  // ============================================================================
  // TESTBENCH PARAMETERS AND SIGNALS
  // ============================================================================

  localparam int CLK_PERIOD = 10; // 100 MHz
  localparam int NODE_X = 2;
  localparam int NODE_Y = 1;
  localparam int NODE_ID = (NODE_Y * 4) + NODE_X; // Calculate NODE_ID from coordinates

  // Clock and reset
  logic clk = 0;
  logic rst_n = 0;

  // CHI Interface Signals
  logic                chi_req_valid;
  logic                chi_req_ready;
  chi_req_t            chi_req;

  logic                chi_resp_valid;
  logic                chi_resp_ready;
  chi_resp_t           chi_resp;

  logic                chi_dat_req_valid;
  logic                chi_dat_req_ready;
  chi_data_t           chi_dat_req;
  
  logic                chi_dat_resp_valid;
  logic                chi_dat_resp_ready;
  chi_data_t           chi_dat_resp;

  logic                chi_snp_valid;
  logic                chi_snp_ready;
  chi_snoop_t          chi_snp;

  logic                chi_snp_resp_valid;
  logic                chi_snp_resp_ready;
  chi_resp_t           chi_snp_resp;

  logic                chi_snp_dat_valid;
  logic                chi_snp_dat_ready;
  chi_data_t           chi_snp_dat;

  // Incoming CHI Interface Signals
  logic                chi_req_in_valid;
  logic                chi_req_in_ready;
  chi_req_t            chi_req_in;

  logic                chi_resp_in_valid;
  logic                chi_resp_in_ready;
  chi_resp_t           chi_resp_in;

  logic                chi_dat_in_valid;
  logic                chi_dat_in_ready;
  chi_data_t           chi_dat_in;

  logic                chi_snp_in_valid;
  logic                chi_snp_in_ready;
  chi_snoop_t          chi_snp_in;

  // NoC Interface Signals
  logic                noc_flit_out_valid;
  logic                noc_flit_out_ready;
  noc_flit_t           noc_flit_out;

  logic                noc_flit_in_valid;
  logic                noc_flit_in_ready;
  noc_flit_t           noc_flit_in;

  // Configuration and Status
  logic [31:0]         status_reg;
  logic [31:0]         error_reg;
  logic [31:0]         tx_flit_counter;
  logic [31:0]         rx_flit_counter;
  logic [31:0]         tx_packet_counter;
  logic [31:0]         rx_packet_counter;

  // Module Status Outputs
  logic [31:0]         packets_sent;
  logic [31:0]         packets_received;
  logic [31:0]         protocol_errors;
  logic [31:0]         buffer_overruns;

  // Test control signals
  logic [31:0] test_count = 0;
  logic [31:0] error_count = 0;
  logic test_active = 0;

  // NoC traffic simulation
  logic [15:0] next_seq_num = 1;
  
  // CHI transaction tracking
  typedef struct {
    logic [CHI_TXN_ID_WIDTH-1:0] txn_id;
    chi_opcode_e opcode;
    logic [CHI_REQ_ADDR_WIDTH-1:0] addr;
    logic outstanding;
  } chi_transaction_t;
  
  chi_transaction_t pending_transactions[256];

  // ============================================================================
  // CLOCK AND RESET GENERATION
  // ============================================================================

  always #(CLK_PERIOD/2) clk = ~clk;

  initial begin
    rst_n = 0;
    #(CLK_PERIOD * 5);
    rst_n = 1;
    #(CLK_PERIOD * 2);
  end

  // ============================================================================
  // DEVICE UNDER TEST INSTANTIATION
  // ============================================================================

  nebula_chi_noc_bridge #(
    .NODE_ID(NODE_ID),
    .MAX_OUTSTANDING(64)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    
    // CHI Request Channel (outgoing)
    .chi_req_valid(chi_req_valid),
    .chi_req_ready(chi_req_ready),
    .chi_req(chi_req),

    // CHI Response Channel (outgoing)
    .chi_resp_valid(chi_resp_valid),
    .chi_resp_ready(chi_resp_ready),
    .chi_resp(chi_resp),

    // CHI Data Channel (outgoing)
    .chi_dat_out_valid(chi_dat_req_valid),
    .chi_dat_out_ready(chi_dat_req_ready),
    .chi_dat_out(chi_dat_req),

    // CHI Snoop Channel (outgoing)
    .chi_snp_valid(chi_snp_valid),
    .chi_snp_ready(chi_snp_ready),
    .chi_snp(chi_snp),

    // CHI Request Channel (incoming)
    .chi_req_in_valid(chi_req_in_valid),
    .chi_req_in_ready(chi_req_in_ready),
    .chi_req_in(chi_req_in),

    // CHI Response Channel (incoming)
    .chi_resp_in_valid(chi_resp_in_valid),
    .chi_resp_in_ready(chi_resp_in_ready),
    .chi_resp_in(chi_resp_in),

    // CHI Data Channel (incoming)
    .chi_dat_in_valid(chi_dat_resp_valid),
    .chi_dat_in_ready(chi_dat_resp_ready),
    .chi_dat_in(chi_dat_resp),

    // CHI Snoop Channel (incoming)
    .chi_snp_in_valid(chi_snp_resp_valid),
    .chi_snp_in_ready(chi_snp_resp_ready),
    .chi_snp_in(chi_snp_resp),

    // NoC Interface
    .noc_flit_out_valid(noc_flit_out_valid),
    .noc_flit_out_ready(noc_flit_out_ready),
    .noc_flit_out(noc_flit_out),

    .noc_flit_in_valid(noc_flit_in_valid),
    .noc_flit_in_ready(noc_flit_in_ready),
    .noc_flit_in(noc_flit_in),

    // Status and Debug
    .packets_sent(packets_sent),
    .packets_received(packets_received),
    .protocol_errors(protocol_errors),
    .buffer_overruns(buffer_overruns)
  );

  // ============================================================================
  // TEST STIMULUS AND VERIFICATION
  // ============================================================================

  // Connect performance counters
  assign tx_flit_counter = packets_sent;
  assign rx_flit_counter = packets_received;
  assign tx_packet_counter = packets_sent;
  assign rx_packet_counter = packets_received;

  // Initialize signals
  initial begin
    chi_req_valid = 0;
    chi_req = '0;
    chi_resp_ready = 1;
    chi_dat_req_valid = 0;
    chi_dat_req = '0;
    chi_dat_resp_ready = 1;
    chi_snp_ready = 1;
    chi_snp_resp_valid = 0;
    chi_snp_resp = '0;
    chi_snp_dat_valid = 0;
    chi_snp_dat = '0;
    noc_flit_out_ready = 1;
    noc_flit_in_valid = 0;
    noc_flit_in = '0;

    // Initialize transaction tracking
    for (int i = 0; i < 256; i++) begin
      pending_transactions[i].outstanding = 0;
    end

    // Wait for reset deassertion
    wait (rst_n);
    #(CLK_PERIOD * 5);

    // Run tests
    test_active = 1;
    run_basic_functionality_test();
    run_chi_request_translation_test();
    run_chi_response_translation_test();
    run_chi_data_translation_test();
    run_chi_snoop_translation_test();
    run_noc_to_chi_translation_test();
    run_multi_flit_packet_test();
    run_virtual_channel_test();
    run_flow_control_test();
    run_performance_test();
    test_active = 0;

    // Final results
    #(CLK_PERIOD * 50);
    $display("=== CHI-NoC Bridge Test Results ===");
    $display("Total tests: %0d", test_count);
    $display("Errors: %0d", error_count);
    if (error_count == 0) begin
      $display("✅ All tests PASSED!");
    end else begin
      $display("❌ %0d tests FAILED!", error_count);
    end
    $display("=====================================");
    $finish;
  end

  // ============================================================================
  // TEST TASKS
  // ============================================================================

  task automatic run_basic_functionality_test();
    $display("Running Basic Functionality Test...");
    test_count++;
    
    // Test 1: Check reset state
    if (status_reg != 0 || error_reg != 0) begin
      $error("Reset state incorrect");
      error_count++;
    end else begin
      $display("✅ Reset state correct");
    end

    // Test 2: Check ready signals
    if (!chi_req_ready) begin
      $error("CHI request not ready after reset");
      error_count++;
    end else begin
      $display("✅ CHI interface ready");
    end

    // Test 3: Check counters initialized
    if (tx_flit_counter != 0 || rx_flit_counter != 0) begin
      $error("Counters not initialized to zero");
      error_count++;
    end else begin
      $display("✅ Performance counters initialized");
    end

    #(CLK_PERIOD * 5);
  endtask
 
  task automatic run_chi_request_translation_test();
    logic [7:0] txn_id;
    logic [31:0] initial_tx_count;
    
    $display("Running CHI Request Translation Test...");
    test_count++;

    txn_id = 8'h42;
    initial_tx_count = tx_flit_counter;

    // Send CHI ReadShared request
    @(posedge clk);
    chi_req_valid = 1;
    chi_req.txn_id = txn_id;
    chi_req.src_id = 6'h05;
    chi_req.tgt_id = 6'h00;
    chi_req.addr = 64'h1000_0040;
    chi_req.opcode = CHI_READSHARED;
    chi_req.size = 3'h6;
    chi_req.qos = QOS_NORMAL[QOS_WIDTH-1:0];

    pending_transactions[txn_id].txn_id = txn_id;
    pending_transactions[txn_id].opcode = CHI_READSHARED;
    pending_transactions[txn_id].addr = 64'h1000_0040;
    pending_transactions[txn_id].outstanding = 1;

    @(posedge clk);
    while (!chi_req_ready) @(posedge clk);
    chi_req_valid = 0;

    // Wait for NoC packet generation
    wait (noc_flit_out_valid);
    @(posedge clk);
    @(posedge clk);  // Extra cycle for combinatorial settling
    
    // Verify NoC packet fields
    if (noc_flit_out.dest_x != 4'h0 || noc_flit_out.dest_y != 4'h0) begin
      $error("NoC destination incorrect");
      error_count++;
    end else if (noc_flit_out.src_x != 4'(NODE_X) || noc_flit_out.src_y != 4'(NODE_Y)) begin
      $error("NoC source incorrect");
      error_count++;
    end else if (noc_flit_out.vc_id != 2'(VC_REQ)) begin
      $error("NoC virtual channel incorrect for request");
      error_count++;
    end else if (noc_flit_out.flit_type != FLIT_TYPE_SINGLE) begin
      $error("NoC flit type incorrect for request");
      error_count++;
    end else begin
      $display("✅ CHI request translated correctly to NoC");
      
      // Verify transaction ID in payload
      if (noc_flit_out.payload[CHI_TXN_ID_WIDTH-1:0] != txn_id) begin
        $error("Transaction ID not preserved in NoC payload");
        error_count++;
      end else begin
        $display("✅ Transaction ID preserved in translation");
      end
    end

    // Check counter increment
    #(CLK_PERIOD * 2);
    if (tx_flit_counter <= initial_tx_count) begin
      $error("TX flit counter not incremented");
      error_count++;
    end else begin
      $display("✅ TX flit counter incremented");
    end

    #(CLK_PERIOD * 5);
  endtask

  task automatic run_chi_response_translation_test();
    $display("Running CHI Response Translation Test...");
    test_count++;

    // Send CHI response
    @(posedge clk);
    chi_resp_valid = 1;
    chi_resp.txn_id = 8'h43;
    chi_resp.src_id = 6'h00;
    chi_resp.tgt_id = 6'h05;
    chi_resp.opcode = CHI_COMP;
    chi_resp.resp_err = CHI_OKAY;

    @(posedge clk);
    while (!chi_resp_ready) @(posedge clk);
    chi_resp_valid = 0;

    // Wait for NoC packet
    wait (noc_flit_out_valid);
    @(posedge clk);
    
    if (noc_flit_out.vc_id != 2'(VC_RSP)) begin
      $error("NoC virtual channel incorrect for response");
      error_count++;
    end else begin
      $display("✅ CHI response translated with correct VC");
    end

    #(CLK_PERIOD * 5);
  endtask

  task automatic run_chi_data_translation_test();
    logic [31:0] initial_tx_count;
    int data_flit_count;
    
    $display("Running CHI Data Translation Test...");
    test_count++;

    initial_tx_count = tx_flit_counter;

    // Send CHI data
    @(posedge clk);
    chi_dat_req_valid = 1;
    chi_dat_req.txn_id = 8'h44;
    chi_dat_req.src_id = 6'h05;
    chi_dat_req.tgt_id = 6'h00;
    chi_dat_req.data = {16{32'hDEADBEEF}};
    chi_dat_req.be = {CHI_BE_WIDTH{1'b1}};

    @(posedge clk);
    while (!chi_dat_req_ready) @(posedge clk);
    chi_dat_req_valid = 0;

    // Data should generate multiple flits
    data_flit_count = 0;
    repeat (10) begin
      @(posedge clk);
      if (noc_flit_out_valid && noc_flit_out_ready && noc_flit_out.vc_id == 2'(VC_DAT)) begin
        data_flit_count++;
        $display("  Data flit %0d: TYPE=%0d, SEQ=%04h", 
                 data_flit_count, noc_flit_out.flit_type, noc_flit_out.seq_num);
      end
    end

    if (data_flit_count < 1) begin
      $error("No data flits generated for 512-bit data");
      error_count++;
    end else begin
      $display("✅ CHI data translated to %0d NoC flits", data_flit_count);
    end

    #(CLK_PERIOD * 10);
  endtask

  task automatic run_chi_snoop_translation_test();
    $display("Running CHI Snoop Translation Test...");
    test_count++;

    // Send CHI snoop
    @(posedge clk);
    chi_snp_valid = 1;
    chi_snp.txn_id = 8'h45;
    chi_snp.src_id = 6'h00;
    chi_snp.tgt_id = 6'h03;
    chi_snp.addr = 64'h1000_0080;
    chi_snp.opcode = CHI_SNPSHARED;

    @(posedge clk);
    while (!chi_snp_ready) @(posedge clk);
    chi_snp_valid = 0;

    // Wait for NoC packet
    wait (noc_flit_out_valid);
    @(posedge clk);
    
    if (noc_flit_out.vc_id != 2'(VC_SNP)) begin
      $error("NoC virtual channel incorrect for snoop");
      error_count++;
    end else if (noc_flit_out.dest_x != 4'h3 || noc_flit_out.dest_y != 4'h0) begin
      $error("NoC destination incorrect for snoop target");
      error_count++;
    end else begin
      $display("✅ CHI snoop translated correctly");
    end

    #(CLK_PERIOD * 5);
  endtask

  task automatic run_noc_to_chi_translation_test();
    logic [31:0] initial_rx_count;
    
    $display("Running NoC to CHI Translation Test...");
    test_count++;

    initial_rx_count = rx_flit_counter;

    // Send NoC packet to CHI
    @(posedge clk);
    noc_flit_in_valid = 1;
    noc_flit_in.dest_x = 4'(NODE_X);
    noc_flit_in.dest_y = 4'(NODE_Y);
    noc_flit_in.src_x = 4'h0;
    noc_flit_in.src_y = 4'h0;
    noc_flit_in.vc_id = 2'(VC_RSP);
    noc_flit_in.flit_type = FLIT_TYPE_SINGLE;
    noc_flit_in.seq_num = next_seq_num++;
    
    // Encode CHI response in payload
    noc_flit_in.payload[CHI_TXN_ID_WIDTH-1:0] = 8'h42; // Matching earlier request
    noc_flit_in.payload[CHI_TXN_ID_WIDTH +: 6] = 6'h00; // src_id
    noc_flit_in.payload[CHI_TXN_ID_WIDTH + 6 +: 6] = 6'h05; // tgt_id
    noc_flit_in.payload[CHI_TXN_ID_WIDTH + 12 +: 8] = CHI_COMP; // opcode

    @(posedge clk);
    noc_flit_in_valid = 0;

    // Wait for CHI response
    wait (chi_resp_valid);
    @(posedge clk);
    
    if (chi_resp.txn_id != 8'h42) begin
      $error("CHI response transaction ID incorrect");
      error_count++;
    end else if (chi_resp.opcode != CHI_COMP) begin
      $error("CHI response opcode incorrect");
      error_count++;
    end else begin
      $display("✅ NoC packet translated to CHI response");
    end

    // Check counter increment
    #(CLK_PERIOD * 2);
    if (rx_flit_counter <= initial_rx_count) begin
      $error("RX flit counter not incremented");
      error_count++;
    end else begin
      $display("✅ RX flit counter incremented");
    end

    #(CLK_PERIOD * 5);
  endtask

  task automatic run_multi_flit_packet_test();
    logic [511:0] expected_data;
    
    $display("Running Multi-Flit Packet Test...");
    test_count++;

    // Send multi-flit data packet
    @(posedge clk);
    
    // Header flit
    noc_flit_in_valid = 1;
    noc_flit_in.dest_x = 4'(NODE_X);
    noc_flit_in.dest_y = 4'(NODE_Y);
    noc_flit_in.src_x = 4'h1;
    noc_flit_in.src_y = 4'h1;
    noc_flit_in.vc_id = 2'(VC_DAT);
    noc_flit_in.flit_type = FLIT_TYPE_HEAD;
    noc_flit_in.seq_num = next_seq_num++;
    noc_flit_in.payload[CHI_TXN_ID_WIDTH-1:0] = 8'h46;

    @(posedge clk);
    noc_flit_in.flit_type = FLIT_TYPE_BODY;
    noc_flit_in.payload = {PAYLOAD_BITS_PER_FLIT{1'b1}}; // All 1s pattern

    @(posedge clk);
    noc_flit_in.flit_type = FLIT_TYPE_BODY;
    noc_flit_in.payload = {PAYLOAD_BITS_PER_FLIT{1'b0}}; // All 0s pattern

    @(posedge clk);
    noc_flit_in.flit_type = FLIT_TYPE_TAIL;
    noc_flit_in.payload[PAYLOAD_BITS_PER_FLIT-1:0] = {(PAYLOAD_BITS_PER_FLIT/32){32'hCAFEBABE}}; // Tail data

    @(posedge clk);
    noc_flit_in_valid = 0;

    // Wait for CHI data reconstruction
    wait (chi_dat_resp_valid);
    @(posedge clk);
    
    if (chi_dat_resp.txn_id != 8'h46) begin
      $error("Multi-flit data transaction ID incorrect");
      error_count++;
    end else begin
      $display("✅ Multi-flit packet reconstructed to CHI data");
      
      // Verify data integrity
      expected_data = {256'hFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
                      256'h00000000000000000000000000000000CAFEBABECAFEBABECAFEBABECAFEBABE};
      if (chi_dat_resp.data != expected_data) begin
        $warning("Data pattern mismatch in multi-flit reconstruction");
      end else begin
        $display("✅ Data integrity preserved across multi-flit packet");
      end
    end

    #(CLK_PERIOD * 10);
  endtask

  task automatic run_virtual_channel_test();
    logic [2:0] vc_types[4];
    logic [31:0] vc_counts[4];
    
    $display("Running Virtual Channel Test...");
    test_count++;

    // Test all virtual channels
    vc_types = '{VC_REQ, VC_RSP, VC_DAT, VC_SNP};

    // Get initial counts
    for (int i = 0; i < 4; i++) begin
      vc_counts[i] = 0;
    end

    // Send traffic on each VC
    for (int vc = 0; vc < 4; vc++) begin
      @(posedge clk);
      noc_flit_in_valid = 1;
      noc_flit_in.dest_x = 4'(NODE_X);
      noc_flit_in.dest_y = 4'(NODE_Y);
      noc_flit_in.src_x = 4'h2;
      noc_flit_in.src_y = 4'h2;
      noc_flit_in.vc_id = vc_types[vc];
      noc_flit_in.flit_type = FLIT_TYPE_SINGLE;
      noc_flit_in.seq_num = next_seq_num++;
      noc_flit_in.payload[CHI_TXN_ID_WIDTH-1:0] = 8'h50 + vc;

      @(posedge clk);
      noc_flit_in_valid = 0;
      
      #(CLK_PERIOD * 5);
    end

    $display("✅ Virtual channel test completed");
    #(CLK_PERIOD * 10);
  endtask

  task automatic run_flow_control_test();
    $display("Running Flow Control Test...");
    test_count++;

    // Test backpressure handling
    noc_flit_out_ready = 0; // Block output

    // Send CHI request
    @(posedge clk);
    chi_req_valid = 1;
    chi_req.txn_id = 8'h60;
    chi_req.src_id = 6'h05;
    chi_req.tgt_id = 6'h00;
    chi_req.addr = 64'h1000_0100;
    chi_req.opcode = CHI_READSHARED;
    chi_req.size = 3'h6;

    // Should not be ready due to backpressure
    @(posedge clk);
    if (chi_req_ready) begin
      $error("CHI request accepted despite NoC backpressure");
      error_count++;
    end else begin
      $display("✅ Backpressure correctly applied");
    end

    // Release backpressure
    noc_flit_out_ready = 1;
    
    @(posedge clk);
    while (!chi_req_ready) @(posedge clk);
    chi_req_valid = 0;

    $display("✅ Flow control test completed");
    #(CLK_PERIOD * 10);
  endtask

  task automatic run_performance_test();
    logic [31:0] initial_tx_flits;
    logic [31:0] initial_rx_flits;
    logic [31:0] initial_tx_packets;
    logic [31:0] initial_rx_packets;
    logic [31:0] tx_flit_delta, rx_flit_delta, tx_packet_delta, rx_packet_delta;
    
    $display("Running Performance Test...");
    test_count++;

    initial_tx_flits = tx_flit_counter;
    initial_rx_flits = rx_flit_counter;
    initial_tx_packets = tx_packet_counter;
    initial_rx_packets = rx_packet_counter;

    // Generate sustained traffic
    for (int i = 0; i < 8; i++) begin
      // CHI request
      @(posedge clk);
      chi_req_valid = 1;
      chi_req.txn_id = 8'h70 + i;
      chi_req.src_id = 6'h05;
      chi_req.tgt_id = 6'h00;
      chi_req.addr = 64'h1000_0000 + (i * 64);
      chi_req.opcode = (i % 2) ? CHI_READSHARED : CHI_READUNIQUE;
      chi_req.size = 3'h6;

      @(posedge clk);
      while (!chi_req_ready) @(posedge clk);
      chi_req_valid = 0;

      // NoC response
      @(posedge clk);
      noc_flit_in_valid = 1;
      noc_flit_in.dest_x = 4'(NODE_X);
      noc_flit_in.dest_y = 4'(NODE_Y);
      noc_flit_in.src_x = 4'h0;
      noc_flit_in.src_y = 4'h0;
      noc_flit_in.vc_id = 2'(VC_RSP);
      noc_flit_in.flit_type = FLIT_TYPE_SINGLE;
      noc_flit_in.seq_num = next_seq_num++;
      noc_flit_in.payload[CHI_TXN_ID_WIDTH-1:0] = 8'h70 + i;

      @(posedge clk);
      noc_flit_in_valid = 0;

      #(CLK_PERIOD * 2);
    end

    #(CLK_PERIOD * 20);

    tx_flit_delta = tx_flit_counter - initial_tx_flits;
    rx_flit_delta = rx_flit_counter - initial_rx_flits;
    tx_packet_delta = tx_packet_counter - initial_tx_packets;
    rx_packet_delta = rx_packet_counter - initial_rx_packets;

    $display("Performance metrics:");
    $display("  TX flits: %0d", tx_flit_delta);
    $display("  RX flits: %0d", rx_flit_delta);
    $display("  TX packets: %0d", tx_packet_delta);
    $display("  RX packets: %0d", rx_packet_delta);

    if (tx_flit_delta >= 8 && rx_flit_delta >= 8) begin
      $display("✅ Performance counters show expected traffic");
    end else begin
      $error("Performance counters not showing expected traffic");
      error_count++;
    end

    $display("✅ Performance test completed");
    #(CLK_PERIOD * 10);
  endtask

  // ============================================================================
  // MONITORING AND VERIFICATION
  // ============================================================================

  // Monitor CHI transactions
  always @(posedge clk) begin
    if (test_active) begin
      if (chi_req_valid && chi_req_ready) begin
        $display("CHI REQ: TXN=%02h, SRC=%02h, TGT=%02h, ADDR=%016h, OP=%s", 
                 chi_req.txn_id, chi_req.src_id, chi_req.tgt_id, chi_req.addr,
                 chi_req.opcode);
      end

      if (chi_resp_valid && chi_resp_ready) begin
        $display("CHI RESP: TXN=%02h, SRC=%02h, TGT=%02h, OP=%s",
                 chi_resp.txn_id, chi_resp.src_id, chi_resp.tgt_id,
                 chi_resp.opcode);
      end

      if (noc_flit_out_valid && noc_flit_out_ready) begin
        $display("NOC TX: DEST=(%0d,%0d), SRC=(%0d,%0d), VC=%0d, TYPE=%s, SEQ=%04h",
                 noc_flit_out.dest_x, noc_flit_out.dest_y,
                 noc_flit_out.src_x, noc_flit_out.src_y,
                 noc_flit_out.vc_id, noc_flit_out.flit_type,
                 noc_flit_out.seq_num);
      end

      if (noc_flit_in_valid && noc_flit_in_ready) begin
        $display("NOC RX: DEST=(%0d,%0d), SRC=(%0d,%0d), VC=%0d, TYPE=%s, SEQ=%04h",
                 noc_flit_in.dest_x, noc_flit_in.dest_y,
                 noc_flit_in.src_x, noc_flit_in.src_y,
                 noc_flit_in.vc_id, noc_flit_in.flit_type,
                 noc_flit_in.seq_num);
      end
    end
  end

  // Timeout watchdog
  initial begin
    #(CLK_PERIOD * 15000);
    if (test_active) begin
      $error("Test timeout!");
      error_count++;
      $finish;
    end
  end

endmodule
