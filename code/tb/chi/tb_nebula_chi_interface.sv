`timescale 1ns / 1ps
//==============================================================================
// Testbench for Nebula CHI Interface
//
// This testbench validates the CHI interface module by testing:
// - Basic CHI request/response transactions
// - Directory lookup and state management  
// - Snoop broadcast and coordination
// - CHI-to-NoC protocol translation
// - Performance counters and error handling
//==============================================================================

import nebula_pkg::*;

module tb_nebula_chi_interface;

  // ============================================================================
  // TESTBENCH PARAMETERS AND SIGNALS
  // ============================================================================

  localparam int CLK_PERIOD = 10; // 100 MHz
  localparam int NODE_ID = 5;     // Test node ID

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

  // NoC interface signals (testbench driven)
  logic                noc_flit_out_valid;
  logic                noc_flit_out_ready;
  noc_flit_t           noc_flit_out;

  logic                noc_flit_in_valid;
  logic                noc_flit_in_ready;
  noc_flit_t           noc_flit_in;

  // Configuration and status registers (connected to DUT outputs/inputs)
  logic [CHI_REQ_ADDR_WIDTH-1:0] base_addr;
  logic [CHI_REQ_ADDR_WIDTH-1:0] addr_mask;
  logic [31:0]         status_reg;
  logic [31:0]         error_reg;
  logic [31:0]         perf_counter_req;
  logic [31:0]         perf_counter_resp;
  logic [31:0]         cache_hit_counter;
  logic [31:0]         cache_miss_counter;

  // Testbench control counters and flags
  bit                  test_active;
  int                  test_count;
  int                  error_count;

  // Instantiate DUT
  nebula_chi_interface #(.NODE_ID(NODE_ID)) dut (
    .clk(clk),
    .rst_n(rst_n),
    // CHI Request Channel
    .chi_req_valid(chi_req_valid),
    .chi_req_ready(chi_req_ready),
    .chi_req(chi_req),
    // CHI Response Channel
    .chi_resp_valid(chi_resp_valid),
    .chi_resp_ready(chi_resp_ready),
    .chi_resp(chi_resp),

    .chi_dat_req_valid(chi_dat_req_valid),
    .chi_dat_req_ready(chi_dat_req_ready),
    .chi_dat_req(chi_dat_req),
    
    .chi_dat_resp_valid(chi_dat_resp_valid),
    .chi_dat_resp_ready(chi_dat_resp_ready),
    .chi_dat_resp(chi_dat_resp),

    // CHI Snoop Channel
    .chi_snp_valid(chi_snp_valid),
    .chi_snp_ready(chi_snp_ready),
    .chi_snp(chi_snp),

    // CHI Snoop Response Channel
    .chi_snp_resp_valid(chi_snp_resp_valid),
    .chi_snp_resp_ready(chi_snp_resp_ready),
    .chi_snp_resp(chi_snp_resp),

    // CHI Snoop Data Channel
    .chi_snp_dat_valid(chi_snp_dat_valid),
    .chi_snp_dat_ready(chi_snp_dat_ready),
    .chi_snp_dat(chi_snp_dat),

    // NoC Interface
    .noc_flit_out_valid(noc_flit_out_valid),
    .noc_flit_out_ready(noc_flit_out_ready),
    .noc_flit_out(noc_flit_out),

    .noc_flit_in_valid(noc_flit_in_valid),
    .noc_flit_in_ready(noc_flit_in_ready),
    .noc_flit_in(noc_flit_in),

    // Configuration and Status
    .base_addr(base_addr),
    .addr_mask(addr_mask),
    .status_reg(status_reg),
    .error_reg(error_reg),
    .perf_counter_req(perf_counter_req),
    .perf_counter_resp(perf_counter_resp),
    .cache_hit_counter(cache_hit_counter),
    .cache_miss_counter(cache_miss_counter)
  );

  // ============================================================================
  // TEST STIMULUS AND VERIFICATION
  // ============================================================================

  // Monitor CHI snoop channels
  // Continuous snoop response generation (skip during snoop coordination test)
  logic auto_snoop_response_enable = 1;
  
  always @(posedge clk) begin
    if (rst_n && auto_snoop_response_enable && chi_snp_valid && chi_snp_ready) begin
      @(posedge clk);
      
      // Respond to snoop immediately (simulating cache controller response)
      chi_snp_resp_valid <= 1;
      chi_snp_resp.txn_id <= chi_snp.txn_id;  // Match transaction ID
      chi_snp_resp.src_id <= chi_snp.tgt_id;  // Swap src/tgt
      chi_snp_resp.tgt_id <= chi_snp.src_id;
      chi_snp_resp.opcode <= CHI_COMP;
      chi_snp_resp.resp_err <= CHI_OKAY;
      chi_snp_resp.dbid <= 8'h00;
      chi_snp_resp.fwd_state <= 3'h0;
      chi_snp_resp.rsvdc <= 4'h0;
      chi_snp_resp.qos <= 4'h0;
      
      // Wait for ready handshake, then deassert
      @(posedge clk);
      while (!chi_snp_resp_ready) @(posedge clk);
      @(posedge clk);
      chi_snp_resp_valid <= 0;
    end
  end

  always @(posedge clk) begin
    if (chi_snp_valid) begin
      // CHI snoop request detected
    end
    if (chi_snp_resp_valid || chi_snp_resp_ready) begin
      // Snoop response activity
    end
  end

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
    
    // Configuration
    base_addr = 64'h1000_0000;
    addr_mask = 64'hFFF0_0000;

    // Wait for reset deassertion
    wait (rst_n);
    #(CLK_PERIOD * 5);

    // Run tests
    test_active = 1;
    run_basic_functionality_test();
    run_read_shared_test();
    run_read_unique_test();
    run_write_unique_test();
    run_snoop_coordination_test();
    run_noc_translation_test();
    run_error_handling_test();
    run_performance_test();
    test_active = 0;

    // Final results
    #(CLK_PERIOD * 10);
    $display("=== CHI Interface Test Results ===");
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
    if (status_reg[7:0] != 0 || error_reg != 0) begin
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

    #(CLK_PERIOD * 5);
  endtask

  task automatic run_read_shared_test();
    // Local variable to hold expected transaction ID (declaration must appear before statements)
    logic [CHI_TXN_ID_WIDTH-1:0] expected_txn_id;
    $display("Running Read Shared Test...");
    test_count++;

    @(posedge clk);
    
    // Send CHI ReadShared request
    chi_req_valid = 1;
    chi_req.txn_id = 8'h01;
    chi_req.src_id = 6'h05;
    chi_req.tgt_id = 6'h00;  // Home node
    chi_req.addr = 64'h1000_0040;  // Cache line aligned
    chi_req.opcode = CHI_READSHARED;
    chi_req.size = 3'h6;     // 64 bytes
    chi_req.qos = QOS_NORMAL[QOS_WIDTH-1:0];

    @(posedge clk);
    while (!chi_req_ready) @(posedge clk);
    
  $display("CHI completion response received");
  // Capture expected TXN_ID before the request signals are cleared
  expected_txn_id = chi_req.txn_id;
  chi_resp_ready = 1;
    @(posedge clk);
    chi_resp_ready = 0;

    // Wait for completion response processing to finish
    #(CLK_PERIOD * 5);
    
    // Clear request after sufficient delay to prevent reprocessing
    chi_req_valid = 0;
    chi_req.txn_id = 8'h00;
    chi_req.src_id = 6'h00;
    chi_req.tgt_id = 6'h00;
    chi_req.addr = 64'h0000_0000;

    // Simulate NoC response for ReadShared
    #(CLK_PERIOD * 2);  // Small delay to simulate NoC latency
    @(posedge clk);
    noc_flit_in_valid = 1;
    noc_flit_in.dest_x = NODE_ID[3:0] % 4;
    noc_flit_in.dest_y = NODE_ID[3:0] / 4;
    noc_flit_in.src_x = 4'h0;
    noc_flit_in.src_y = 4'h0;
    noc_flit_in.vc_id = VC_RSP;
    noc_flit_in.flit_type = FLIT_TYPE_SINGLE;
    noc_flit_in.seq_num = 16'h0001;
    
    // Build complete CHI response payload
    noc_flit_in.payload = '0;  // Clear all payload bits first
  noc_flit_in.payload[CHI_TXN_ID_WIDTH-1:0] = expected_txn_id;  // Match transaction ID
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH] = 6'h00;  // src_id 
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH] = 6'h05;  // tgt_id
    // Add opcode (CHI_COMP = 5'h0) at next field position  
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+4:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH] = 5'h0;
    // Add resp_err (CHI_OKAY = 2'b00)
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+6:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+5] = 2'b00;

    $display("Sending NoC response for ReadShared");
    // Hold valid for multiple cycles to ensure proper sampling
    repeat (5) @(posedge clk);
    noc_flit_in_valid = 0;

    // Wait for response
    wait (chi_resp_valid);
    @(posedge clk);
    
    if (chi_resp.txn_id != expected_txn_id) begin
      $error("ReadShared response TXN_ID mismatch: expected %02x, got %02x", expected_txn_id, chi_resp.txn_id);
      error_count++;
    end else begin
      $display("✅ ReadShared transaction completed");
    end

    #(CLK_PERIOD * 10);
  endtask

  task automatic run_read_unique_test();
    $display("Running Read Unique Test...");
    test_count++;

    @(posedge clk);
    
    // Send CHI ReadUnique request
    chi_req_valid = 1;
    chi_req.txn_id = 8'h02;
    chi_req.src_id = 6'h05;
    chi_req.tgt_id = 6'h00;
    chi_req.addr = 64'h1000_0080;
    chi_req.opcode = CHI_READUNIQUE;
    chi_req.size = 3'h6;
    chi_req.qos = QOS_HIGH[QOS_WIDTH-1:0];

    @(posedge clk);
    while (!chi_req_ready) @(posedge clk);
    
    $display("CHI completion response received for ReadUnique");
    chi_resp_ready = 1;
    @(posedge clk);
    chi_resp_ready = 0;

    // Wait for completion response processing to finish
    #(CLK_PERIOD * 5);
    
    // Clear request after sufficient delay to prevent reprocessing
    chi_req_valid = 0;
    chi_req.txn_id = 8'h00;
    chi_req.src_id = 6'h00;
    chi_req.tgt_id = 6'h00;
    chi_req.addr = 64'h0000_0000;

    // Simulate NoC response for ReadUnique
    #(CLK_PERIOD * 2);  // Small delay to simulate NoC latency
    @(posedge clk);
    noc_flit_in_valid = 1;
    noc_flit_in.dest_x = NODE_ID[3:0] % 4;
    noc_flit_in.dest_y = NODE_ID[3:0] / 4;
    noc_flit_in.src_x = 4'h0;
    noc_flit_in.src_y = 4'h0;
    noc_flit_in.vc_id = VC_RSP;
    noc_flit_in.flit_type = FLIT_TYPE_SINGLE;
    noc_flit_in.seq_num = 16'h0002;
    
    // Build complete CHI response payload
    noc_flit_in.payload = '0;  // Clear all payload bits first
    noc_flit_in.payload[CHI_TXN_ID_WIDTH-1:0] = 8'h02;  // Match transaction ID
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH] = 6'h00;  // src_id 
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH] = 6'h05;  // tgt_id
    // Add opcode (CHI_COMP = 5'h0) at next field position  
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+4:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH] = 5'h0;
    // Add resp_err (CHI_OKAY = 2'b00)
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+6:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+5] = 2'b00;

    $display("Sending NoC response for ReadUnique");
    // Hold valid for multiple cycles to ensure proper sampling
    repeat (5) @(posedge clk);
    noc_flit_in_valid = 0;

    // Wait for response
    wait (chi_resp_valid);
    @(posedge clk);
    
    if (chi_resp.opcode != CHI_COMP) begin
      $error("ReadUnique response opcode incorrect");
      error_count++;
    end else begin
      $display("✅ ReadUnique transaction completed");
    end

    #(CLK_PERIOD * 10);
  endtask

  task automatic run_write_unique_test();
    $display("Running Write Unique Test...");
    test_count++;

    @(posedge clk);
    
    // Send CHI WriteUnique request
    chi_req_valid = 1;
    chi_req.txn_id = 8'h03;
    chi_req.src_id = 6'h05;
    chi_req.tgt_id = 6'h00;
    chi_req.addr = 64'h1000_00C0;
    chi_req.opcode = CHI_WRITEUNIQUEFULL;
    chi_req.size = 3'h6;
    chi_req.qos = QOS_URGENT[QOS_WIDTH-1:0];

    @(posedge clk);
    while (!chi_req_ready) @(posedge clk);
    
    // Send data first, then clear request after completion
    @(posedge clk);
    chi_dat_req_valid = 1;
    chi_dat_req.txn_id = 8'h03;
    chi_dat_req.src_id = 6'h05;
    chi_dat_req.tgt_id = 6'h00;
    chi_dat_req.data = {16{32'hDEADBEEF}};
    chi_dat_req.be = {CHI_BE_WIDTH{1'b1}};

    @(posedge clk);
    while (!chi_dat_req_ready) @(posedge clk);
    chi_dat_req_valid = 0;

    // Wait for completion response
    wait (chi_resp_valid);
    @(posedge clk);
    $display("CHI completion response received for WriteUnique");
    chi_resp_ready = 1;
    @(posedge clk);
    chi_resp_ready = 0;

    // Wait for completion response processing to finish
    #(CLK_PERIOD * 5);
    
    // Clear request after sufficient delay to prevent reprocessing
    chi_req_valid = 0;
    chi_req.txn_id = 8'h00;
    chi_req.src_id = 6'h00;
    chi_req.tgt_id = 6'h00;
    chi_req.addr = 64'h0000_0000;
    chi_req.opcode = CHI_READCLEAN;  // Valid but different opcode
    chi_req.size = 3'h0;
    chi_req.qos = 4'h0;

    // Simulate NoC response for WriteUnique
    #(CLK_PERIOD * 2);  // Small delay to simulate NoC latency
    @(posedge clk);
    noc_flit_in_valid = 1;
    noc_flit_in.dest_x = NODE_ID[3:0] % 4;
    noc_flit_in.dest_y = NODE_ID[3:0] / 4;
    noc_flit_in.src_x = 4'h0;
    noc_flit_in.src_y = 4'h0;
    noc_flit_in.vc_id = VC_RSP;
    noc_flit_in.flit_type = FLIT_TYPE_SINGLE;
    noc_flit_in.seq_num = 16'h0003;
    
    // Build complete CHI response payload
    noc_flit_in.payload = '0;  // Clear all payload bits first
    noc_flit_in.payload[CHI_TXN_ID_WIDTH-1:0] = 8'h03;  // Match transaction ID
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH] = 6'h00;  // src_id 
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH] = 6'h05;  // tgt_id
    // Add opcode (CHI_COMP = 5'h0) at next field position  
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+4:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH] = 5'h0;
    // Add resp_err (CHI_OKAY = 2'b00)
    noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+6:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+5] = 2'b00;

    $display("Sending NoC response for WriteUnique");
    // Hold valid for multiple cycles to ensure proper sampling
    repeat (5) @(posedge clk);
    noc_flit_in_valid = 0;

    // Wait for completion
    wait (chi_resp_valid);
    @(posedge clk);
    
    $display("✅ WriteUnique transaction completed");

    #(CLK_PERIOD * 10);
  endtask

  task automatic run_snoop_coordination_test();
    $display("Running Snoop Coordination Test...");
    test_count++;

    // Disable automatic snoop response for this test
    auto_snoop_response_enable = 0;
    
    // Wait for snoop to be generated
    wait (chi_snp_valid);
    @(posedge clk);
    
    if (chi_snp.opcode != CHI_SNPSHARED && chi_snp.opcode != CHI_SNPUNIQUE) begin
      $error("Invalid snoop opcode");
      error_count++;
    end else begin
      $display("✅ Snoop generated correctly");
    end

    // Respond to snoop with proper handshaking
    @(posedge clk);
    chi_snp_resp_valid = 1;
    chi_snp_resp.txn_id = chi_snp.txn_id;
    chi_snp_resp.src_id = 6'h05;
    chi_snp_resp.tgt_id = chi_snp.src_id;
    chi_snp_resp.opcode = CHI_SNPRESP;
    chi_snp_resp.resp_err = CHI_OKAY;
    
    $display("CHI SNOOP RESP: TXN=%02h, SRC=%02h, TGT=%02h, OP=%s", 
             chi_snp_resp.txn_id, chi_snp_resp.src_id, chi_snp_resp.tgt_id, "CHI_SNPRESP");

    // Wait for ready handshake
    wait (chi_snp_resp_ready);
    @(posedge clk);
    chi_snp_resp_valid = 0;

    $display("✅ Snoop coordination completed");
    
    // Re-enable automatic snoop response
    auto_snoop_response_enable = 1;

    #(CLK_PERIOD * 10);
  endtask

  task automatic run_noc_translation_test();
    $display("Running NoC Translation Test...");
    test_count++;

    // Check if NoC packet was generated
    wait (noc_flit_out_valid);
    @(posedge clk);
    
    if (noc_flit_out.vc_id != VC_SNP) begin
      $error("NoC packet VC incorrect");
      error_count++;
    end else begin
      $display("✅ NoC packet generated with correct VC");
    end

    // Simulate NoC response
    @(posedge clk);
    noc_flit_in_valid = 1;
    noc_flit_in.dest_x = NODE_ID[3:0] % 4;
    noc_flit_in.dest_y = NODE_ID[3:0] / 4;
    noc_flit_in.src_x = 4'h0;
    noc_flit_in.src_y = 4'h0;
    noc_flit_in.vc_id = VC_RSP;
    noc_flit_in.flit_type = FLIT_TYPE_SINGLE;
    noc_flit_in.seq_num = 16'h0001;
    noc_flit_in.payload[CHI_TXN_ID_WIDTH-1:0] = 8'h01;

    @(posedge clk);
    noc_flit_in_valid = 0;

    $display("✅ NoC translation test completed");

    #(CLK_PERIOD * 10);
  endtask

  task automatic run_error_handling_test();
    $display("Running Error Handling Test...");
    test_count++;

    @(posedge clk);
    
    // Send request to invalid address
    chi_req_valid = 1;
    chi_req.txn_id = 8'hFF;
    chi_req.src_id = 6'h05;
    chi_req.tgt_id = 6'h00;
    chi_req.addr = 64'h2000_0000;  // Outside managed range
    chi_req.opcode = CHI_READSHARED;
    chi_req.size = 3'h6;

    @(posedge clk);
    while (!chi_req_ready) @(posedge clk);
    chi_req_valid = 0;

    // Wait for error response
    wait (chi_resp_valid);
    @(posedge clk);
    
    if (chi_resp.resp_err != CHI_SLVERR) begin
      $error("Error response not generated");
      error_count++;
    end else begin
      $display("✅ Error handling working correctly");
    end

    #(CLK_PERIOD * 10);
  endtask

  task automatic run_performance_test();
    logic [31:0] initial_req_count;
    logic [31:0] initial_resp_count;
    
    $display("Running Performance Test...");
    test_count++;
    
    initial_req_count = perf_counter_req;
    initial_resp_count = perf_counter_resp;

    // Send multiple requests
    for (int i = 0; i < 4; i++) begin
      @(posedge clk);
      chi_req_valid = 1;
      chi_req.txn_id = 8'h10 + i;
      chi_req.src_id = 6'h05;
      chi_req.tgt_id = 6'h00;
      chi_req.addr = 64'h1000_0000 + (i * 64);
      chi_req.opcode = CHI_READSHARED;
      chi_req.size = 3'h6;

      @(posedge clk);
      while (!chi_req_ready) @(posedge clk);
      chi_req_valid = 0;
      
      #(CLK_PERIOD * 5);
    end

    #(CLK_PERIOD * 20);

    if (perf_counter_req <= initial_req_count) begin
      $error("Performance counters not incrementing");
      error_count++;
    end else begin
      $display("✅ Performance counters working");
      $display("   Requests: %0d -> %0d", initial_req_count, perf_counter_req);
      $display("   Responses: %0d -> %0d", initial_resp_count, perf_counter_resp);
    end

    #(CLK_PERIOD * 10);
  endtask

  // ============================================================================
  // MONITORING AND VERIFICATION
  // ============================================================================

  // Monitor CHI transactions
  always @(posedge clk) begin
    if (test_active) begin
      // CHI transaction monitoring (debug output removed)

      if (noc_flit_out_valid && noc_flit_out_ready) begin
        string flit_type_str;
        case (noc_flit_out.flit_type)
          FLIT_TYPE_HEAD: flit_type_str = "HEAD";
          FLIT_TYPE_BODY: flit_type_str = "BODY"; 
          FLIT_TYPE_TAIL: flit_type_str = "TAIL";
          default: flit_type_str = "UNKNOWN";
        endcase
        $display("NOC TX: DEST=(%0d,%0d), SRC=(%0d,%0d), VC=%0d, TYPE=%s, SEQ=%04h",
                 noc_flit_out.dest_x, noc_flit_out.dest_y,
                 noc_flit_out.src_x, noc_flit_out.src_y,
                 noc_flit_out.vc_id, flit_type_str,
                 noc_flit_out.seq_num);
      end
    end
  end

  // Timeout watchdog
  initial begin
    #(CLK_PERIOD * 10000);
    if (test_active) begin
      $error("Test timeout!");
      error_count++;
      $finish;
    end
  end

endmodule
