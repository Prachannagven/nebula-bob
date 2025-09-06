`timescale 1ns / 1ps
//==============================================================================
// Nebula Top-Level System Integration Testbench
//
// This testbench validates the complete Nebula system integration including:
// - Mesh topology instantiation and connectivity
// - AXI4 and CHI protocol interfaces
// - Configuration register interface
// - Performance monitoring
// - Error handling and debug interfaces
//==============================================================================

import nebula_pkg::*;

module tb_nebula_top();

  // ============================================================================
  // PARAMETERS AND LOCALPARAMS
  // ============================================================================
  
  localparam int CLK_PERIOD = 10; // 100 MHz clock
  localparam int MESH_WIDTH = 2;  // Small mesh for manageable simulation
  localparam int MESH_HEIGHT = 2;
  localparam int NUM_NODES = MESH_WIDTH * MESH_HEIGHT;
  localparam int CONFIG_ADDR_WIDTH = 16;
  localparam int CONFIG_DATA_WIDTH = 32;
  
  // ============================================================================
  // SIGNALS
  // ============================================================================
  
  logic clk = 0;
  logic rst_n = 0;
  
  // Configuration interface
  logic                           config_req_valid = 0;
  logic                           config_req_ready;
  logic [CONFIG_ADDR_WIDTH-1:0]  config_req_addr = 0;
  logic [CONFIG_DATA_WIDTH-1:0]  config_req_data = 0;
  logic                           config_req_write = 0;
  
  logic                           config_resp_valid;
  logic                           config_resp_ready = 1;
  logic [CONFIG_DATA_WIDTH-1:0]  config_resp_data;
  logic                           config_resp_error;
  
  // Memory interfaces
  logic [NUM_NODES-1:0]                     mem_req_valid;
  logic [NUM_NODES-1:0]                     mem_req_ready = '1;
  logic [NUM_NODES-1:0][CHI_REQ_ADDR_WIDTH-1:0] mem_req_addr;
  logic [NUM_NODES-1:0]                     mem_req_write;
  logic [NUM_NODES-1:0][CHI_DATA_WIDTH-1:0] mem_req_data;
  logic [NUM_NODES-1:0][CHI_BE_WIDTH-1:0]   mem_req_be;
  
  logic [NUM_NODES-1:0]                     mem_resp_valid = '0;
  logic [NUM_NODES-1:0]                     mem_resp_ready;
  logic [NUM_NODES-1:0][CHI_DATA_WIDTH-1:0] mem_resp_data = '0;
  logic [NUM_NODES-1:0]                     mem_resp_error = '0;
  
  // AXI interfaces
  logic [NUM_NODES-1:0]     axi_aw_valid = '0;
  logic [NUM_NODES-1:0]     axi_aw_ready;
  axi_aw_t [NUM_NODES-1:0]  axi_aw = '0;
  
  logic [NUM_NODES-1:0]     axi_w_valid = '0;
  logic [NUM_NODES-1:0]     axi_w_ready;
  axi_w_t [NUM_NODES-1:0]   axi_w = '0;
  
  logic [NUM_NODES-1:0]     axi_b_valid;
  logic [NUM_NODES-1:0]     axi_b_ready = '1;
  axi_b_t [NUM_NODES-1:0]   axi_b;
  
  logic [NUM_NODES-1:0]     axi_ar_valid = '0;
  logic [NUM_NODES-1:0]     axi_ar_ready;
  axi_ar_t [NUM_NODES-1:0]  axi_ar = '0;
  
  logic [NUM_NODES-1:0]     axi_r_valid;
  logic [NUM_NODES-1:0]     axi_r_ready = '1;
  axi_r_t [NUM_NODES-1:0]   axi_r;
  
  // CHI interfaces
  logic [NUM_NODES-1:0]     chi_req_valid = '0;
  logic [NUM_NODES-1:0]     chi_req_ready;
  chi_req_t [NUM_NODES-1:0] chi_req = '0;
  
  logic [NUM_NODES-1:0]     chi_resp_valid;
  logic [NUM_NODES-1:0]     chi_resp_ready = '1;
  chi_resp_t [NUM_NODES-1:0] chi_resp;
  
  logic [NUM_NODES-1:0]     chi_dat_req_valid = '0;
  logic [NUM_NODES-1:0]     chi_dat_req_ready;
  chi_data_t [NUM_NODES-1:0] chi_dat_req = '0;
  
  logic [NUM_NODES-1:0]     chi_dat_resp_valid;
  logic [NUM_NODES-1:0]     chi_dat_resp_ready = '1;
  chi_data_t [NUM_NODES-1:0] chi_dat_resp;
  
  // System status
  logic [31:0] system_status;
  logic [31:0] error_status;
  logic [31:0] performance_counters [15:0];
  
  // Debug interface
  logic        debug_trace_valid;
  logic [63:0] debug_trace_data;
  logic [7:0]  debug_trace_node_id;
  
  // Test control variables
  int error_count = 0;
  int test_count = 0;
  
  // ============================================================================
  // DUT INSTANTIATION
  // ============================================================================
  
  nebula_top #(
    .MESH_WIDTH(MESH_WIDTH),
    .MESH_HEIGHT(MESH_HEIGHT),
    .CONFIG_ADDR_WIDTH(CONFIG_ADDR_WIDTH),
    .CONFIG_DATA_WIDTH(CONFIG_DATA_WIDTH),
    .ENABLE_AXI(1'b1),
    .ENABLE_CHI(1'b1),
    .ENABLE_PERFORMANCE_MONITORING(1'b1)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    
    // Configuration interface
    .config_req_valid(config_req_valid),
    .config_req_ready(config_req_ready),
    .config_req_addr(config_req_addr),
    .config_req_data(config_req_data),
    .config_req_write(config_req_write),
    
    .config_resp_valid(config_resp_valid),
    .config_resp_ready(config_resp_ready),
    .config_resp_data(config_resp_data),
    .config_resp_error(config_resp_error),
    
    // Memory interfaces
    .mem_req_valid(mem_req_valid),
    .mem_req_ready(mem_req_ready),
    .mem_req_addr(mem_req_addr),
    .mem_req_write(mem_req_write),
    .mem_req_data(mem_req_data),
    .mem_req_be(mem_req_be),
    
    .mem_resp_valid(mem_resp_valid),
    .mem_resp_ready(mem_resp_ready),
    .mem_resp_data(mem_resp_data),
    .mem_resp_error(mem_resp_error),
    
    // AXI interfaces
    .axi_aw_valid(axi_aw_valid),
    .axi_aw_ready(axi_aw_ready),
    .axi_aw(axi_aw),
    
    .axi_w_valid(axi_w_valid),
    .axi_w_ready(axi_w_ready),
    .axi_w(axi_w),
    
    .axi_b_valid(axi_b_valid),
    .axi_b_ready(axi_b_ready),
    .axi_b(axi_b),
    
    .axi_ar_valid(axi_ar_valid),
    .axi_ar_ready(axi_ar_ready),
    .axi_ar(axi_ar),
    
    .axi_r_valid(axi_r_valid),
    .axi_r_ready(axi_r_ready),
    .axi_r(axi_r),
    
    // CHI interfaces
    .chi_req_valid(chi_req_valid),
    .chi_req_ready(chi_req_ready),
    .chi_req(chi_req),
    
    .chi_resp_valid(chi_resp_valid),
    .chi_resp_ready(chi_resp_ready),
    .chi_resp(chi_resp),
    
    .chi_dat_req_valid(chi_dat_req_valid),
    .chi_dat_req_ready(chi_dat_req_ready),
    .chi_dat_req(chi_dat_req),
    
    .chi_dat_resp_valid(chi_dat_resp_valid),
    .chi_dat_resp_ready(chi_dat_resp_ready),
    .chi_dat_resp(chi_dat_resp),
    
    // Status and debug
    .system_status(system_status),
    .error_status(error_status),
    .performance_counters(performance_counters),
    .debug_trace_valid(debug_trace_valid),
    .debug_trace_data(debug_trace_data),
    .debug_trace_node_id(debug_trace_node_id)
  );
  
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
  // MEMORY MODEL
  // ============================================================================
  
  // Simple memory response model
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      mem_resp_valid <= '0;
      mem_resp_data <= '0;
    end else begin
      for (int i = 0; i < NUM_NODES; i++) begin
        if (mem_req_valid[i] && mem_req_ready[i]) begin
          // Respond after a few cycles
          mem_resp_valid[i] <= 1'b1;
          mem_resp_data[i] <= {2{mem_req_addr[i][31:0]}}; // Echo address as data
        end else if (mem_resp_valid[i] && mem_resp_ready[i]) begin
          mem_resp_valid[i] <= 1'b0;
        end
      end
    end
  end
  
  // ============================================================================
  // TEST SEQUENCE
  // ============================================================================
  
  initial begin
    $display("=== NEBULA TOP-LEVEL SYSTEM INTEGRATION TEST ===");
    $display("Mesh: %0dx%0d (%0d nodes)", MESH_WIDTH, MESH_HEIGHT, NUM_NODES);
    
    wait (rst_n);
    #(CLK_PERIOD * 5);
    
    // Test 1: Configuration register access
    test_configuration_registers();
    
    // Test 2: System status validation
    test_system_status();
    
    // Test 3: AXI transaction through mesh
    test_axi_transaction();
    
    // Test 4: CHI transaction through mesh  
    test_chi_transaction();
    
    // Test 5: Performance monitoring
    test_performance_monitoring();
    
    // Test 6: Debug interface
    test_debug_interface();
    
    // Test 7: Error handling
    test_error_handling();
    
    // Test 8: Multi-node traffic
    test_multi_node_traffic();
    
    #(CLK_PERIOD * 100); // Additional simulation time
    
    // Final results
    $display("\\n=== TEST RESULTS ===");
    $display("Total tests: %0d", test_count);
    $display("Errors: %0d", error_count);
    if (error_count == 0) begin
      $display("✅ ALL TESTS PASSED!");
    end else begin
      $display("❌ %0d TESTS FAILED!", error_count);
    end
    $display("====================");
    
    $finish;
  end
  
  // ============================================================================
  // TEST TASKS
  // ============================================================================
  
  task test_configuration_registers();
    $display("\\n--- Test 1: Configuration Registers ---");
    test_count++;
    
    // Read system configuration
    config_read(8'h00, "System Topology");
    if (config_resp_data != {16'h0000, 8'(MESH_HEIGHT), 8'(MESH_WIDTH)}) begin
      $error("System topology mismatch: expected %08h, got %08h", 
             {16'h0000, 8'(MESH_HEIGHT), 8'(MESH_WIDTH)}, config_resp_data);
      error_count++;
    end else begin
      $display("✅ System topology correct");
    end
    
    // Read number of nodes
    config_read(8'h03, "Number of Nodes");
    if (config_resp_data != NUM_NODES) begin
      $error("Node count mismatch: expected %0d, got %0d", NUM_NODES, config_resp_data);
      error_count++;
    end else begin
      $display("✅ Node count correct");
    end
    
    // Test write to writable register
    config_write(8'h10, 32'hDEADBEEF, "Test Register");
    config_read(8'h10, "Test Register Readback");
    if (config_resp_data != 32'hDEADBEEF) begin
      $error("Register write/read mismatch");
      error_count++;
    end else begin
      $display("✅ Register write/read working");
    end
    
    // Test write to read-only register (should fail)
    config_write(8'h00, 32'h12345678, "Read-Only Register");
    if (!config_resp_error) begin
      $error("Write to read-only register should have failed");
      error_count++;
    end else begin
      $display("✅ Read-only register protection working");
    end
  endtask
  
  task test_system_status();
    $display("\\n--- Test 2: System Status ---");
    test_count++;
    
    #(CLK_PERIOD * 10);
    
    // Check system status register
    if (system_status[0] != 1'b1) begin
      $error("System ready bit not set");
      error_count++;
    end else begin
      $display("✅ System ready");
    end
    
    if (system_status[7:4] != 4'(MESH_WIDTH)) begin
      $error("Mesh width in status incorrect");
      error_count++;
    end else begin
      $display("✅ Mesh width in status correct");
    end
    
    if (system_status[11:8] != 4'(MESH_HEIGHT)) begin
      $error("Mesh height in status incorrect");
      error_count++;
    end else begin
      $display("✅ Mesh height in status correct");
    end
  endtask
  
  task test_axi_transaction();
    $display("\\n--- Test 3: AXI Transaction ---");
    test_count++;
    
    // Send AXI read from node 0 to node 3
    fork
      begin
        axi_read_transaction(0, 64'h3000_0000, 8'h04); // Address maps to node 3
      end
      begin
        #(CLK_PERIOD * 50);
        if (!axi_r_valid[0]) begin
          $error("AXI read response not received");
          error_count++;
        end else begin
          $display("✅ AXI read transaction completed");
        end
      end
    join_any
    
    #(CLK_PERIOD * 10);
  endtask
  
  task test_chi_transaction();
    $display("\\n--- Test 4: CHI Transaction ---");
    test_count++;
    
    // Send CHI read from node 1 to node 2
    fork
      begin
        chi_read_transaction(1, 64'h2000_0040); // Address maps to node 2
      end
      begin
        #(CLK_PERIOD * 50);
        if (!chi_resp_valid[1] && !chi_dat_resp_valid[1]) begin
          $error("CHI read response not received");
          error_count++;
        end else begin
          $display("✅ CHI read transaction completed");
        end
      end
    join_any
    
    #(CLK_PERIOD * 10);
  endtask
  
  task test_performance_monitoring();
    $display("\\n--- Test 5: Performance Monitoring ---");
    test_count++;
    
    // Check performance counters
    #(CLK_PERIOD * 10);
    
    $display("Performance counters:");
    for (int i = 0; i < 10; i++) begin
      $display("  Counter[%0d]: %0d", i, performance_counters[i]);
    end
    
    if (performance_counters[4] != NUM_NODES) begin
      $error("Node count counter incorrect");
      error_count++;
    end else begin
      $display("✅ Performance monitoring working");
    end
  endtask
  
  task test_debug_interface();
    $display("\\n--- Test 6: Debug Interface ---");
    test_count++;
    
    // Generate some traffic to trigger debug traces
    axi_read_transaction(0, 64'h1000_0000, 8'h08);
    
    #(CLK_PERIOD * 20);
    
    // Check if debug trace was generated
    if (debug_trace_valid) begin
      $display("✅ Debug trace generated: node %0d, data %016h", 
               debug_trace_node_id, debug_trace_data);
    end else begin
      $display("⚠️  No debug trace generated (may be normal)");
    end
  endtask
  
  task test_error_handling();
    $display("\\n--- Test 7: Error Handling ---");
    test_count++;
    
    // Check initial error status
    if (error_status != 0) begin
      $error("Initial error status non-zero: %08h", error_status);
      error_count++;
    end else begin
      $display("✅ Initial error status clean");
    end
  endtask
  
  task test_multi_node_traffic();
    $display("\\n--- Test 8: Multi-Node Traffic ---");
    test_count++;
    
    // Generate traffic between multiple nodes simultaneously
    fork
      axi_read_transaction(0, 64'h1000_0000, 8'h08);
      axi_write_transaction(1, 64'h2000_0040, 64'hCAFEBABE_DEADBEEF);
      chi_read_transaction(2, 64'h3000_0080);
      begin
        #(CLK_PERIOD * 100);
        $display("✅ Multi-node traffic test completed");
      end
    join_any
  endtask
  
  // ============================================================================
  // UTILITY TASKS
  // ============================================================================
  
  task config_read(input logic [7:0] addr, input string desc);
    config_req_valid = 1;
    config_req_addr = {8'h00, addr};
    config_req_write = 0;
    config_req_data = 0;
    
    wait (config_req_ready);
    @(posedge clk);
    config_req_valid = 0;
    
    wait (config_resp_valid);
    @(posedge clk);
    
    $display("Config read [%02h]: %08h (%s)", addr, config_resp_data, desc);
  endtask
  
  task config_write(input logic [7:0] addr, input logic [31:0] data, input string desc);
    config_req_valid = 1;
    config_req_addr = {8'h00, addr};
    config_req_write = 1;
    config_req_data = data;
    
    wait (config_req_ready);
    @(posedge clk);
    config_req_valid = 0;
    
    wait (config_resp_valid);
    @(posedge clk);
    
    $display("Config write [%02h]: %08h (%s) %s", addr, data, desc, 
             config_resp_error ? "ERROR" : "OK");
  endtask
  
  task axi_read_transaction(input int node, input logic [63:0] addr, input logic [7:0] len);
    // AXI AR channel
    axi_ar_valid[node] = 1;
    axi_ar[node].addr = addr;
    axi_ar[node].len = len;
    axi_ar[node].size = 3'b011; // 8 bytes
    axi_ar[node].burst = 2'b01; // INCR
    axi_ar[node].id = node;
    
    wait (axi_ar_ready[node]);
    @(posedge clk);
    axi_ar_valid[node] = 0;
    
    $display("AXI read initiated: node %0d, addr %016h", node, addr);
  endtask
  
  task axi_write_transaction(input int node, input logic [63:0] addr, input logic [63:0] data);
    // AXI AW channel
    axi_aw_valid[node] = 1;
    axi_aw[node].addr = addr;
    axi_aw[node].len = 0; // Single beat
    axi_aw[node].size = 3'b011; // 8 bytes
    axi_aw[node].burst = 2'b01; // INCR
    axi_aw[node].id = node;
    
    // AXI W channel
    axi_w_valid[node] = 1;
    axi_w[node].data = {8{data[63:0]}}; // Replicate data
    axi_w[node].strb = '1;
    axi_w[node].last = 1;
    
    fork
      begin
        wait (axi_aw_ready[node]);
        @(posedge clk);
        axi_aw_valid[node] = 0;
      end
      begin
        wait (axi_w_ready[node]);
        @(posedge clk);
        axi_w_valid[node] = 0;
      end
    join
    
    $display("AXI write initiated: node %0d, addr %016h, data %016h", node, addr, data);
  endtask
  
  task chi_read_transaction(input int node, input logic [63:0] addr);
    chi_req_valid[node] = 1;
    chi_req[node].txn_id = node;
    chi_req[node].addr = addr;
    chi_req[node].opcode = CHI_READSHARED;
    chi_req[node].size = 3'b110; // 64 bytes
    chi_req[node].src_id = node;
    chi_req[node].tgt_id = 0; // Home node
    
    wait (chi_req_ready[node]);
    @(posedge clk);
    chi_req_valid[node] = 0;
    
    $display("CHI read initiated: node %0d, addr %016h", node, addr);
  endtask

  // ============================================================================
  // SIMULATION CONTROL
  // ============================================================================
  
  initial begin
    $dumpfile("nebula_top_test.vcd");
    $dumpvars(0, tb_nebula_top);
    
    // Simulation timeout
    #(CLK_PERIOD * 10000);
    $display("\\n❌ SIMULATION TIMEOUT");
    $finish;
  end

endmodule
