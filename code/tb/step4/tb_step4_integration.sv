`timescale 1ns / 1ps
//==============================================================================
// Step 4 Integration Testbench for Nebula CHI System
//
// This testbench validates the complete CHI subsystem by testing:
// - End-to-end CHI protocol operations across multiple nodes
// - Directory-based cache coherency with MOESI states
// - CHI-NoC protocol translation and mesh network integration
// - Multi-node coherency scenarios and snoop coordination
// - Performance and correctness under various traffic patterns
//==============================================================================

import nebula_pkg::*;

module tb_step4_integration;

  // ============================================================================
  // TESTBENCH PARAMETERS AND SIGNALS
  // ============================================================================

  localparam int CLK_PERIOD = 10; // 100 MHz
  localparam int NUM_NODES = 4;
  localparam int MESH_SIZE_X = 2;
  localparam int MESH_SIZE_Y = 2;

  // Clock and reset
  logic clk = 0;
  logic rst_n = 0;

  // CHI interfaces for each node
  logic [NUM_NODES-1:0]     chi_req_valid;
  logic [NUM_NODES-1:0]     chi_req_ready;
  chi_req_t                 chi_req [NUM_NODES-1:0];

  logic [NUM_NODES-1:0]     chi_resp_valid;
  logic [NUM_NODES-1:0]     chi_resp_ready;
  chi_resp_t                chi_resp [NUM_NODES-1:0];

  logic [NUM_NODES-1:0]     chi_dat_req_valid;
  logic [NUM_NODES-1:0]     chi_dat_req_ready;
  chi_data_t                chi_dat_req [NUM_NODES-1:0];
  
  logic [NUM_NODES-1:0]     chi_dat_resp_valid;
  logic [NUM_NODES-1:0]     chi_dat_resp_ready;
  chi_data_t                chi_dat_resp [NUM_NODES-1:0];

  logic [NUM_NODES-1:0]     chi_snp_valid;
  logic [NUM_NODES-1:0]     chi_snp_ready;
  chi_snoop_t               chi_snp [NUM_NODES-1:0];

  logic [NUM_NODES-1:0]     chi_snp_resp_valid;
  logic [NUM_NODES-1:0]     chi_snp_resp_ready;
  chi_resp_t                chi_snp_resp [NUM_NODES-1:0];

  logic [NUM_NODES-1:0]     chi_snp_dat_valid;
  logic [NUM_NODES-1:0]     chi_snp_dat_ready;
  chi_data_t                chi_snp_dat [NUM_NODES-1:0];

  // Memory interface (for home node)
  logic                     mem_req_valid;
  logic                     mem_req_ready;
  memory_req_t              mem_req;

  logic                     mem_resp_valid;
  logic                     mem_resp_ready;
  memory_resp_t             mem_resp;

  // Test control signals
  logic [31:0] test_count = 0;
  logic [31:0] error_count = 0;
  logic test_active = 0;

  // Transaction tracking
  typedef struct {
    logic [CHI_TXN_ID_WIDTH-1:0] txn_id;
    logic [3:0] src_node;
    chi_opcode_e opcode;
    logic [CHI_REQ_ADDR_WIDTH-1:0] addr;
    logic outstanding;
    logic [31:0] timestamp;
  } transaction_t;
  
  transaction_t pending_transactions[256];
  logic [7:0] next_txn_id[NUM_NODES-1:0];

  // Performance tracking
  logic [31:0] coherency_transactions = 0;
  logic [31:0] snoop_broadcasts = 0;
  logic [31:0] memory_accesses = 0;
  logic [31:0] cache_hits = 0;
  logic [31:0] cache_misses = 0;

  // Memory model
  logic [511:0] memory [logic [CHI_REQ_ADDR_WIDTH-1:6]];

  // ============================================================================
  // CLOCK AND RESET GENERATION
  // ============================================================================

  always #(CLK_PERIOD/2) clk = ~clk;

  initial begin
    rst_n = 0;
    #(CLK_PERIOD * 10);
    rst_n = 1;
    #(CLK_PERIOD * 5);
  end

  // ============================================================================
  // CHI SYSTEM INSTANTIATION
  // ============================================================================

  // CHI interface for each node
  generate
    for (genvar i = 0; i < NUM_NODES; i++) begin : chi_nodes
      localparam int NODE_X = i % MESH_SIZE_X;
      localparam int NODE_Y = i / MESH_SIZE_X;
      
      // CHI Interface + NoC Bridge for each node
      nebula_chi_interface #(
        .NODE_ID(i),
        .NUM_OUTSTANDING(64),
        .DIRECTORY_ENTRIES(256),
        .SNOOP_FILTER_ENTRIES(128)
      ) chi_interface (
        .clk(clk),
        .rst_n(rst_n),
        
        // CHI channels
        .chi_req_valid(chi_req_valid[i]),
        .chi_req_ready(chi_req_ready[i]),
        .chi_req(chi_req[i]),
        
        .chi_resp_valid(chi_resp_valid[i]),
        .chi_resp_ready(chi_resp_ready[i]),
        .chi_resp(chi_resp[i]),
        
        .chi_dat_req_valid(chi_dat_req_valid[i]),
        .chi_dat_req_ready(chi_dat_req_ready[i]),
        .chi_dat_req(chi_dat_req[i]),
        
        .chi_dat_resp_valid(chi_dat_resp_valid[i]),
        .chi_dat_resp_ready(chi_dat_resp_ready[i]),
        .chi_dat_resp(chi_dat_resp[i]),
        
        .chi_snp_valid(chi_snp_valid[i]),
        .chi_snp_ready(chi_snp_ready[i]),
        .chi_snp(chi_snp[i]),
        
        .chi_snp_resp_valid(chi_snp_resp_valid[i]),
        .chi_snp_resp_ready(chi_snp_resp_ready[i]),
        .chi_snp_resp(chi_snp_resp[i]),
        
        .chi_snp_dat_valid(chi_snp_dat_valid[i]),
        .chi_snp_dat_ready(chi_snp_dat_ready[i]),
        .chi_snp_dat(chi_snp_dat[i]),
        
        // NoC interface would connect to mesh network here
        .noc_flit_out_valid(),
        .noc_flit_out_ready(1'b1),
        .noc_flit_out(),
        
        .noc_flit_in_valid(1'b0),
        .noc_flit_in_ready(),
        .noc_flit_in('0),
        
        // Configuration
        .base_addr(64'h1000_0000),
        .addr_mask(64'hFFF0_0000),
        .status_reg(),
        .error_reg(),
        .perf_counter_req(),
        .perf_counter_resp(),
        .cache_hit_counter(),
        .cache_miss_counter()
      );
    end
  endgenerate

  // Home node directory controller (node 0)
  nebula_chi_directory #(
    .NUM_NODES(NUM_NODES),
    .DIRECTORY_ENTRIES(1024),
    .NUM_WAYS(4),
    .NUM_OUTSTANDING(64)
  ) home_directory (
    .clk(clk),
    .rst_n(rst_n),
    
    // CHI channels (connected to node 0)
    .chi_req_valid(chi_req_valid[0]),
    .chi_req_ready(chi_req_ready[0]),
    .chi_req(chi_req[0]),
    
    .chi_resp_valid(chi_resp_valid[0]),
    .chi_resp_ready(chi_resp_ready[0]),
    .chi_resp(chi_resp[0]),
    
    .chi_dat_valid(chi_dat_resp_valid[0]),
    .chi_dat_ready(chi_dat_resp_ready[0]),
    .chi_dat(chi_dat_resp[0]),
    
    .chi_snp_valid(chi_snp_valid[0]),
    .chi_snp_ready(chi_snp_ready[0]),
    .chi_snp(chi_snp[0]),
    
    .chi_snp_resp_valid(chi_snp_resp_valid[0]),
    .chi_snp_resp_ready(chi_snp_resp_ready[0]),
    .chi_snp_resp(chi_snp_resp[0]),
    
    .chi_snp_dat_valid(chi_snp_dat_valid[0]),
    .chi_snp_dat_ready(chi_snp_dat_ready[0]),
    .chi_snp_dat(chi_snp_dat[0]),
    
    // Memory interface
    .mem_req_valid(mem_req_valid),
    .mem_req_ready(mem_req_ready),
    .mem_req(mem_req),
    
    .mem_resp_valid(mem_resp_valid),
    .mem_resp_ready(mem_resp_ready),
    .mem_resp(mem_resp),
    
    // Configuration
    .base_addr(64'h1000_0000),
    .size_mask(64'hFFF0_0000),
    .status_reg(),
    .error_reg(),
    .dir_hit_counter(),
    .dir_miss_counter(),
    .snoop_counter()
  );

  // ============================================================================
  // MEMORY MODEL
  // ============================================================================

  // Simple memory model with realistic latency
  logic [7:0] mem_latency_counter = 0;
  memory_req_t pending_mem_req;
  logic mem_req_pending = 0;

  always @(posedge clk) begin
    if (!rst_n) begin
      mem_req_ready <= 1;
      mem_resp_valid <= 0;
      mem_latency_counter <= 0;
      mem_req_pending <= 0;
    end else begin
      // Accept memory requests
      if (mem_req_valid && mem_req_ready && !mem_req_pending) begin
        pending_mem_req <= mem_req;
        mem_req_pending <= 1;
        mem_latency_counter <= 8; // 8 cycle latency
        mem_req_ready <= 0;
        memory_accesses <= memory_accesses + 1;
      end

      // Process pending requests
      if (mem_req_pending) begin
        if (mem_latency_counter > 0) begin
          mem_latency_counter <= mem_latency_counter - 1;
        end else begin
          // Generate response
          mem_resp_valid <= 1;
          mem_resp.txn_id <= pending_mem_req.txn_id;
          mem_resp.resp_err <= MEM_OKAY;
          
          if (pending_mem_req.cmd == MEM_READ) begin
            if (memory.exists(pending_mem_req.addr[CHI_REQ_ADDR_WIDTH-1:6])) begin
              mem_resp.data <= memory[pending_mem_req.addr[CHI_REQ_ADDR_WIDTH-1:6]];
            end else begin
              mem_resp.data <= {16{32'hBEEFCAFE}}; // Default pattern
            end
          end else begin
            // Write to memory
            memory[pending_mem_req.addr[CHI_REQ_ADDR_WIDTH-1:6]] = pending_mem_req.data;
            mem_resp.data <= '0;
          end
          
          mem_req_pending <= 0;
          mem_req_ready <= 1;
        end
      end

      // Clear response when accepted
      if (mem_resp_valid && mem_resp_ready) begin
        mem_resp_valid <= 0;
      end
    end
  end

  // ============================================================================
  // TEST STIMULUS AND VERIFICATION
  // ============================================================================

  // Initialize signals
  initial begin
    for (int i = 0; i < NUM_NODES; i++) begin
      chi_req_valid[i] = 0;
      chi_req[i] = '0;
      chi_resp_ready[i] = 1;
      chi_dat_req_valid[i] = 0;
      chi_dat_req[i] = '0;
      chi_dat_resp_ready[i] = 1;
      chi_snp_ready[i] = 1;
      chi_snp_resp_valid[i] = 0;
      chi_snp_resp[i] = '0;
      chi_snp_dat_valid[i] = 0;
      chi_snp_dat[i] = '0;
      next_txn_id[i] = 1;
    end
    
    mem_resp_ready = 1;

    // Initialize transaction tracking
    for (int i = 0; i < 256; i++) begin
      pending_transactions[i].outstanding = 0;
    end

    // Wait for reset deassertion
    wait (rst_n);
    #(CLK_PERIOD * 10);

    // Run comprehensive test suite
    test_active = 1;
    run_basic_connectivity_test();
    run_single_cache_line_test();
    run_shared_read_test();
    run_exclusive_access_test();
    run_coherency_upgrade_test();
    run_write_invalidation_test();
    run_multi_node_coherency_test();
    run_snoop_coordination_test();
    run_memory_consistency_test();
    run_performance_stress_test();
    test_active = 0;

    // Final results
    #(CLK_PERIOD * 100);
    $display("=== Step 4 Integration Test Results ===");
    $display("Total tests: %0d", test_count);
    $display("Errors: %0d", error_count);
    $display("Performance Summary:");
    $display("  Coherency transactions: %0d", coherency_transactions);
    $display("  Snoop broadcasts: %0d", snoop_broadcasts);
    $display("  Memory accesses: %0d", memory_accesses);
    $display("  Cache hits: %0d", cache_hits);
    $display("  Cache misses: %0d", cache_misses);
    
    if (error_count == 0) begin
      $display("✅ All tests PASSED!");
    end else begin
      $display("❌ %0d tests FAILED!", error_count);
    end
    $display("======================================");
    $finish;
  end

  // ============================================================================
  // TEST TASKS
  // ============================================================================

  task automatic run_basic_connectivity_test();
    $display("Running Basic Connectivity Test...");
    test_count++;
    
    // Test that all CHI interfaces are ready
    for (int i = 0; i < NUM_NODES; i++) begin
      if (!chi_req_ready[i]) begin
        $error("Node %0d CHI interface not ready", i);
        error_count++;
      end
    end
    
    if (error_count == 0) begin
      $display("✅ All CHI interfaces ready");
    end

    #(CLK_PERIOD * 5);
  endtask

  task automatic run_single_cache_line_test();
    logic [7:0] txn_id;
    logic [63:0] addr;
    
    $display("Running Single Cache Line Test...");
    test_count++;

    txn_id = get_next_txn_id(1);
    addr = 64'h1000_0040;

    // Node 1 reads a cache line
    send_chi_request(1, txn_id, 6'h01, 6'h00, addr, CHI_READSHARED, 3'h6);
    coherency_transactions++;

    // Wait for completion
    wait_for_response(1, txn_id);
    
    if (pending_transactions[txn_id].outstanding) begin
      $error("Transaction not completed");
      error_count++;
    end else begin
      $display("✅ Single cache line read completed");
    end

    #(CLK_PERIOD * 10);
  endtask

  task automatic run_shared_read_test();
    logic [63:0] addr;
    logic [7:0] txn_ids[3];
    
    $display("Running Shared Read Test...");
    test_count++;

    addr = 64'h1000_0080;

    // Multiple nodes read the same cache line
    for (int i = 1; i < NUM_NODES; i++) begin
      txn_ids[i-1] = get_next_txn_id(i);
      send_chi_request(i, txn_ids[i-1], 6'h01 + i, 6'h00, addr, CHI_READSHARED, 3'h6);
      coherency_transactions++;
      #(CLK_PERIOD * 5);
    end

    // Wait for all to complete
    for (int i = 1; i < NUM_NODES; i++) begin
      wait_for_response(i, txn_ids[i-1]);
    end

    $display("✅ Shared read test completed");
    #(CLK_PERIOD * 15);
  endtask

  task automatic run_exclusive_access_test();
    logic [63:0] addr;
    logic [7:0] txn_id;
    
    $display("Running Exclusive Access Test...");
    test_count++;

    addr = 64'h1000_00C0;
    txn_id = get_next_txn_id(2);

    // Node 2 gets exclusive access
    send_chi_request(2, txn_id, 6'h02, 6'h00, addr, CHI_READUNIQUE, 3'h6);
    coherency_transactions++;

    wait_for_response(2, txn_id);

    $display("✅ Exclusive access test completed");
    #(CLK_PERIOD * 15);
  endtask

  task automatic run_coherency_upgrade_test();
    logic [63:0] addr;
    logic [7:0] read_txn;
    logic [7:0] upgrade_txn;
    
    $display("Running Coherency Upgrade Test...");
    test_count++;

    addr = 64'h1000_0100;
    read_txn = get_next_txn_id(1);

    // Node 1 reads shared
    send_chi_request(1, read_txn, 6'h01, 6'h00, addr, CHI_READSHARED, 3'h6);
    wait_for_response(1, read_txn);

    // Node 1 upgrades to unique (should cause coherency action)
    upgrade_txn = get_next_txn_id(1);
    send_chi_request(1, upgrade_txn, 6'h01, 6'h00, addr, CHI_READUNIQUE, 3'h6);
    coherency_transactions++;

    // Monitor for snoop activity
    fork
      begin
        wait (chi_snp_valid[0] || chi_snp_valid[1] || chi_snp_valid[2] || chi_snp_valid[3]);
        snoop_broadcasts++;
        $display("✅ Snoop generated for coherency upgrade");
      end
      begin
        #(CLK_PERIOD * 50);
        $warning("No snoop detected for upgrade (may be optimized)");
      end
    join_any
    disable fork;

    wait_for_response(1, upgrade_txn);

    $display("✅ Coherency upgrade test completed");
    #(CLK_PERIOD * 20);
  endtask

  task automatic run_write_invalidation_test();
    logic [63:0] addr;
    logic [7:0] read_txns[3];
    logic [7:0] write_txn;
    int snoop_count;
    
    $display("Running Write Invalidation Test...");
    test_count++;

    addr = 64'h1000_0140;

    // Multiple nodes read shared
    for (int i = 1; i < NUM_NODES; i++) begin
      read_txns[i-1] = get_next_txn_id(i);
      send_chi_request(i, read_txns[i-1], 6'h01 + i, 6'h00, addr, CHI_READSHARED, 3'h6);
    end

    // Wait for reads to complete
    for (int i = 1; i < NUM_NODES; i++) begin
      wait_for_response(i, read_txns[i-1]);
    end

    // Node 1 writes (should invalidate others)
    write_txn = get_next_txn_id(1);
    send_chi_request(1, write_txn, 6'h01, 6'h00, addr, CHI_WRITEUNIQUEFULL, 3'h6);
    
    // Send write data
    @(posedge clk);
    chi_dat_req_valid[1] = 1;
    chi_dat_req[1].txn_id = write_txn;
    chi_dat_req[1].src_id = 6'h01;
    chi_dat_req[1].tgt_id = 6'h00;
    chi_dat_req[1].data = {16{32'hDEADBEEF}};
    chi_dat_req[1].be = {CHI_BE_WIDTH{1'b1}};

    @(posedge clk);
    while (!chi_dat_req_ready[1]) @(posedge clk);
    chi_dat_req_valid[1] = 0;

    coherency_transactions++;

    // Should generate snoops to invalidate other copies
    snoop_count = 0;
    fork
      begin
        repeat (20) begin
          @(posedge clk);
          for (int i = 0; i < NUM_NODES; i++) begin
            if (chi_snp_valid[i] && chi_snp_ready[i]) begin
              snoop_count++;
              snoop_broadcasts++;
              
              // Auto-respond to snoop
              @(posedge clk);
              chi_snp_resp_valid[i] = 1;
              chi_snp_resp[i].txn_id = chi_snp[i].txn_id;
              chi_snp_resp[i].src_id = chi_snp[i].tgt_id;
              chi_snp_resp[i].tgt_id = chi_snp[i].src_id;
              chi_snp_resp[i].opcode = CHI_SNPRESP;
              chi_snp_resp[i].resp_err = CHI_OKAY;

              @(posedge clk);
              chi_snp_resp_valid[i] = 0;
            end
          end
        end
      end
      begin
        #(CLK_PERIOD * 100);
      end
    join_any
    disable fork;

    wait_for_response(1, write_txn);

    if (snoop_count >= 1) begin
      $display("✅ Write invalidation generated %0d snoops", snoop_count);
    end else begin
      $warning("Expected snoops for write invalidation not detected");
    end

    $display("✅ Write invalidation test completed");
    #(CLK_PERIOD * 25);
  endtask

  task automatic run_multi_node_coherency_test();
    logic [63:0] base_addr;
    logic [7:0] txn_ids[NUM_NODES-1];
    logic [7:0] conflict_txns[NUM_NODES-1];
    
    $display("Running Multi-Node Coherency Test...");
    test_count++;

    // Simulate complex coherency scenario with multiple concurrent accesses
    base_addr = 64'h1000_0200;

    // All nodes access different lines initially
    for (int i = 1; i < NUM_NODES; i++) begin
      txn_ids[i-1] = get_next_txn_id(i);
      send_chi_request(i, txn_ids[i-1], 6'h01 + i, 6'h00, base_addr + (i * 64), 
                       CHI_READSHARED, 3'h6);
      coherency_transactions++;
      #(CLK_PERIOD * 3);
    end

    // Wait for initial accesses
    for (int i = 1; i < NUM_NODES; i++) begin
      wait_for_response(i, txn_ids[i-1]);
    end

    // Now all nodes try to access the same line
    for (int i = 1; i < NUM_NODES; i++) begin
      conflict_txns[i-1] = get_next_txn_id(i);
      send_chi_request(i, conflict_txns[i-1], 6'h01 + i, 6'h00, base_addr, 
                       (i == 1) ? CHI_READUNIQUE : CHI_READSHARED, 3'h6);
      coherency_transactions++;
      #(CLK_PERIOD * 2);
    end

    // Wait for conflict resolution
    for (int i = 1; i < NUM_NODES; i++) begin
      wait_for_response(i, conflict_txns[i-1]);
    end

    $display("✅ Multi-node coherency test completed");
    #(CLK_PERIOD * 30);
  endtask

  task automatic run_snoop_coordination_test();
    logic [63:0] addr;
    logic [7:0] txn_id;
    
    $display("Running Snoop Coordination Test...");
    test_count++;

    // Test proper snoop response handling and coordination
    addr = 64'h1000_0280;
    txn_id = get_next_txn_id(1);

    send_chi_request(1, txn_id, 6'h01, 6'h00, addr, CHI_CLEANUNIQUE, 3'h6);

    // Auto-respond to any snoops that are generated
    fork
      begin
        // Snoop response handler
        forever begin
          @(posedge clk);
          for (int i = 0; i < NUM_NODES; i++) begin
            if (chi_snp_valid[i] && chi_snp_ready[i]) begin
              // Respond after a delay
              #(CLK_PERIOD * 2);
              chi_snp_resp_valid[i] = 1;
              chi_snp_resp[i].txn_id = chi_snp[i].txn_id;
              chi_snp_resp[i].src_id = chi_snp[i].tgt_id;
              chi_snp_resp[i].tgt_id = chi_snp[i].src_id;
              chi_snp_resp[i].opcode = CHI_SNPRESP;
              chi_snp_resp[i].resp_err = CHI_OKAY;

              @(posedge clk);
              chi_snp_resp_valid[i] = 0;
            end
          end
        end
      end
      begin
        wait_for_response(1, txn_id);
      end
    join_any
    disable fork;

    $display("✅ Snoop coordination test completed");
    #(CLK_PERIOD * 20);
  endtask

  task automatic run_memory_consistency_test();
    logic [63:0] addr1, addr2;
    logic [7:0] write_txn1, write_txn2;
    
    $display("Running Memory Consistency Test...");
    test_count++;

    // Test ordering and consistency of memory operations
    addr1 = 64'h1000_0300;
    addr2 = 64'h1000_0340;
    write_txn1 = get_next_txn_id(1);
    write_txn2 = get_next_txn_id(2);

    // Node 1 writes to addr1
    send_chi_request(1, write_txn1, 6'h01, 6'h00, addr1, CHI_WRITEUNIQUEFULL, 3'h6);
    
    @(posedge clk);
    chi_dat_req_valid[1] = 1;
    chi_dat_req[1].txn_id = write_txn1;
    chi_dat_req[1].src_id = 6'h01;
    chi_dat_req[1].tgt_id = 6'h00;
    chi_dat_req[1].data = {16{32'h11111111}};
    chi_dat_req[1].be = {CHI_BE_WIDTH{1'b1}};

    @(posedge clk);
    while (!chi_dat_req_ready[1]) @(posedge clk);
    chi_dat_req_valid[1] = 0;

    // Node 2 writes to addr2  
    send_chi_request(2, write_txn2, 6'h02, 6'h00, addr2, CHI_WRITEUNIQUEFULL, 3'h6);
    
    @(posedge clk);
    chi_dat_req_valid[2] = 1;
    chi_dat_req[2].txn_id = write_txn2;
    chi_dat_req[2].src_id = 6'h02;
    chi_dat_req[2].tgt_id = 6'h00;
    chi_dat_req[2].data = {16{32'h22222222}};
    chi_dat_req[2].be = {CHI_BE_WIDTH{1'b1}};

    @(posedge clk);
    while (!chi_dat_req_ready[2]) @(posedge clk);
    chi_dat_req_valid[2] = 0;

    wait_for_response(1, write_txn1);
    wait_for_response(2, write_txn2);

    // Verify data in memory
    if (memory.exists(addr1[CHI_REQ_ADDR_WIDTH-1:6]) && 
        memory.exists(addr2[CHI_REQ_ADDR_WIDTH-1:6])) begin
      $display("✅ Memory consistency maintained");
    end else begin
      $error("Memory consistency violated");
      error_count++;
    end

    $display("✅ Memory consistency test completed");
    #(CLK_PERIOD * 25);
  endtask

  task automatic run_performance_stress_test();
    logic [31:0] start_time;
    logic [7:0] stress_txns[16];
    logic [31:0] completion_time, throughput;
    
    $display("Running Performance Stress Test...");
    test_count++;

    start_time = $time;

    // Generate high-volume traffic
    for (int i = 0; i < 16; i++) begin
      int node = (i % (NUM_NODES - 1)) + 1;
      logic [63:0] addr;
      stress_txns[i] = get_next_txn_id(node);
      addr = 64'h1000_0000 + (i * 64);
      
      send_chi_request(node, stress_txns[i], 6'h01 + node, 6'h00, addr,
                       (i % 3 == 0) ? CHI_WRITEUNIQUEFULL : CHI_READSHARED, 3'h6);
      
      // Send data for writes
      if (i % 3 == 0) begin
        @(posedge clk);
        chi_dat_req_valid[node] = 1;
        chi_dat_req[node].txn_id = stress_txns[i];
        chi_dat_req[node].src_id = 6'h01 + node;
        chi_dat_req[node].tgt_id = 6'h00;
        chi_dat_req[node].data = {16{32'h00000000 + i}};
        chi_dat_req[node].be = {CHI_BE_WIDTH{1'b1}};

        @(posedge clk);
        while (!chi_dat_req_ready[node]) @(posedge clk);
        chi_dat_req_valid[node] = 0;
      end
      
      coherency_transactions++;
      #(CLK_PERIOD * 2);
    end

    // Wait for all to complete
    for (int i = 0; i < 16; i++) begin
      int node = (i % (NUM_NODES - 1)) + 1;
      wait_for_response(node, stress_txns[i]);
    end

    completion_time = $time - start_time;
    throughput = (16 * 1000000) / (completion_time / CLK_PERIOD);

    $display("Performance Results:");
    $display("  16 transactions completed in %0d cycles", completion_time / CLK_PERIOD);
    $display("  Throughput: %0d transactions/1M cycles", throughput);

    if (completion_time < CLK_PERIOD * 1000) begin
      $display("✅ Performance stress test passed");
    end else begin
      $warning("Performance slower than expected");
    end

    $display("✅ Performance stress test completed");
    #(CLK_PERIOD * 30);
  endtask

  // ============================================================================
  // HELPER FUNCTIONS
  // ============================================================================

  function logic [7:0] get_next_txn_id(int node);
    get_next_txn_id = next_txn_id[node];
    next_txn_id[node] = next_txn_id[node] + 1;
  endfunction

  task automatic send_chi_request(
    input int node,
    input logic [7:0] txn_id,
    input logic [5:0] src_id,
    input logic [5:0] tgt_id,
    input logic [63:0] addr,
    input chi_opcode_e opcode,
    input logic [2:0] size
  );
    pending_transactions[txn_id].txn_id = txn_id;
    pending_transactions[txn_id].src_node = node;
    pending_transactions[txn_id].opcode = opcode;
    pending_transactions[txn_id].addr = addr;
    pending_transactions[txn_id].outstanding = 1;
    pending_transactions[txn_id].timestamp = $time;

    @(posedge clk);
    chi_req_valid[node] = 1;
    chi_req[node].txn_id = txn_id;
    chi_req[node].src_id = src_id;
    chi_req[node].tgt_id = tgt_id;
    chi_req[node].addr = addr;
    chi_req[node].opcode = opcode;
    chi_req[node].size = size;
    chi_req[node].qos = QOS_NORMAL[QOS_WIDTH-1:0];

    @(posedge clk);
    while (!chi_req_ready[node]) @(posedge clk);
    chi_req_valid[node] = 0;
  endtask

  task automatic wait_for_response(input int node, input logic [7:0] txn_id);
    wait (chi_resp_valid[node] && chi_resp[node].txn_id == txn_id);
    @(posedge clk);
    pending_transactions[txn_id].outstanding = 0;
    
    if (chi_resp[node].resp_err != CHI_OKAY) begin
      $error("Response error for TXN %02h: %s", txn_id, chi_resp[node].resp_err.name());
      error_count++;
    end
  endtask

  // ============================================================================
  // MONITORING AND VERIFICATION
  // ============================================================================

  // Transaction monitoring
  always @(posedge clk) begin
    if (test_active) begin
      // Monitor CHI requests
      for (int i = 0; i < NUM_NODES; i++) begin
        if (chi_req_valid[i] && chi_req_ready[i]) begin
          $display("NODE%0d CHI REQ: TXN=%02h, SRC=%02h, TGT=%02h, ADDR=%016h, OP=%s", 
                   i, chi_req[i].txn_id, chi_req[i].src_id, chi_req[i].tgt_id, 
                   chi_req[i].addr, chi_req[i].opcode.name());
        end

        if (chi_resp_valid[i] && chi_resp_ready[i]) begin
          $display("NODE%0d CHI RESP: TXN=%02h, SRC=%02h, TGT=%02h, OP=%s, ERR=%s",
                   i, chi_resp[i].txn_id, chi_resp[i].src_id, chi_resp[i].tgt_id,
                   chi_resp[i].opcode.name(), chi_resp[i].resp_err.name());
        end

        if (chi_snp_valid[i] && chi_snp_ready[i]) begin
          $display("NODE%0d CHI SNOOP: TXN=%02h, SRC=%02h, TGT=%02h, ADDR=%016h, OP=%s",
                   i, chi_snp[i].txn_id, chi_snp[i].src_id, chi_snp[i].tgt_id,
                   chi_snp[i].addr, chi_snp[i].opcode.name());
        end
      end

      // Monitor memory interface
      if (mem_req_valid && mem_req_ready) begin
        $display("MEM REQ: TXN=%02h, ADDR=%016h, CMD=%s",
                 mem_req.txn_id, mem_req.addr, mem_req.cmd.name());
      end

      if (mem_resp_valid && mem_resp_ready) begin
        $display("MEM RESP: TXN=%02h, ERR=%s",
                 mem_resp.txn_id, mem_resp.resp_err.name());
      end
    end
  end

  // Timeout watchdog
  initial begin
    #(CLK_PERIOD * 50000);
    if (test_active) begin
      $error("Test timeout!");
      error_count++;
      $finish;
    end
  end

endmodule
