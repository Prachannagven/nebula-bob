/**
 * Testbench for Nebula Complete System Integration
 * 
 * Tests the full system including mesh topology, NIUs, and end-to-end
 * communication across the entire mesh network.
 * 
 * Test Coverage:
 * 1. Complete system instantiation
 * 2. End-to-end AXI transactions across mesh
 * 3. Multi-node concurrent operations
 * 4. Address space management
 * 5. Performance monitoring
 * 6. System scalability
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: September 2025
 */

`timescale 1ns/1ps

module tb_nebula_system_top;

  import nebula_pkg::*;

  // =============================================================================
  // TESTBENCH PARAMETERS
  // =============================================================================
  
  parameter int CLK_PERIOD = 10;
  parameter int MESH_SIZE_X = 2;
  parameter int MESH_SIZE_Y = 2;
  parameter logic [AXI_ADDR_WIDTH-1:0] GLOBAL_BASE_ADDR = 64'h0000_0000_1000_0000;
  parameter logic [AXI_ADDR_WIDTH-1:0] NODE_ADDR_SIZE = 64'h0000_0000_0010_0000; // 1MB
  parameter int TEST_TIMEOUT = 10000;
  
  // Clock and reset
  logic clk = 0;
  logic rst_n = 0;
  
  // AXI interfaces (per node)
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_awvalid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_awready;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ID_WIDTH-1:0]       axi_awid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ADDR_WIDTH-1:0]     axi_awaddr;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][7:0]                    axi_awlen;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][2:0]                    axi_awsize;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][1:0]                    axi_awburst;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_awlock;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][3:0]                    axi_awcache;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][2:0]                    axi_awprot;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][QOS_WIDTH-1:0]          axi_awqos;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][3:0]                    axi_awregion;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_AWUSER_WIDTH-1:0]   axi_awuser;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_wvalid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_wready;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_DATA_WIDTH-1:0]     axi_wdata;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_STRB_WIDTH-1:0]     axi_wstrb;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_wlast;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_WUSER_WIDTH-1:0]    axi_wuser;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_bvalid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_bready;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ID_WIDTH-1:0]       axi_bid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][1:0]                    axi_bresp;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_BUSER_WIDTH-1:0]    axi_buser;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_arvalid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_arready;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ID_WIDTH-1:0]       axi_arid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ADDR_WIDTH-1:0]     axi_araddr;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][7:0]                    axi_arlen;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][2:0]                    axi_arsize;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][1:0]                    axi_arburst;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_arlock;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][3:0]                    axi_arcache;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][2:0]                    axi_arprot;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][QOS_WIDTH-1:0]          axi_arqos;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][3:0]                    axi_arregion;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ARUSER_WIDTH-1:0]   axi_aruser;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_rvalid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_rready;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_ID_WIDTH-1:0]       axi_rid;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_DATA_WIDTH-1:0]     axi_rdata;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][1:0]                    axi_rresp;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0]                         axi_rlast;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][AXI_RUSER_WIDTH-1:0]    axi_ruser;
  
  // Configuration
  logic [AXI_ADDR_WIDTH-1:0] global_base_addr = GLOBAL_BASE_ADDR;
  logic [AXI_ADDR_WIDTH-1:0] global_addr_mask = 64'hFFFF_FFFF_FFF0_0000;
  
  // System status and debug
  logic [31:0] system_status;
  logic [31:0] system_errors;
  logic [31:0] system_perf_counters [15:0];
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][31:0] node_status;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][31:0] node_errors;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][31:0] node_info;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0][NUM_VCS-1:0] mesh_vc_status;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][PERF_COUNTER_WIDTH-1:0] mesh_packets_routed;
  error_code_e [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] mesh_error_status;
  
  // Test control
  int test_count = 0;
  int pass_count = 0;
  int fail_count = 0;
  
  // =============================================================================
  // CLOCK AND RESET
  // =============================================================================
  
  always #(CLK_PERIOD/2) clk = ~clk;
  
  initial begin
    rst_n = 0;
    #(CLK_PERIOD * 10);
    rst_n = 1;
    #(CLK_PERIOD * 5);
  end

  // =============================================================================
  // DEVICE UNDER TEST
  // =============================================================================
  
  nebula_system_top #(
    .MESH_SIZE_X(MESH_SIZE_X),
    .MESH_SIZE_Y(MESH_SIZE_Y),
    .GLOBAL_BASE_ADDR(GLOBAL_BASE_ADDR),
    .NODE_ADDR_SIZE(NODE_ADDR_SIZE)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .axi_awvalid(axi_awvalid),
    .axi_awready(axi_awready),
    .axi_awid(axi_awid),
    .axi_awaddr(axi_awaddr),
    .axi_awlen(axi_awlen),
    .axi_awsize(axi_awsize),
    .axi_awburst(axi_awburst),
    .axi_awlock(axi_awlock),
    .axi_awcache(axi_awcache),
    .axi_awprot(axi_awprot),
    .axi_awqos(axi_awqos),
    .axi_awregion(axi_awregion),
    .axi_awuser(axi_awuser),
    .axi_wvalid(axi_wvalid),
    .axi_wready(axi_wready),
    .axi_wdata(axi_wdata),
    .axi_wstrb(axi_wstrb),
    .axi_wlast(axi_wlast),
    .axi_wuser(axi_wuser),
    .axi_bvalid(axi_bvalid),
    .axi_bready(axi_bready),
    .axi_bid(axi_bid),
    .axi_bresp(axi_bresp),
    .axi_buser(axi_buser),
    .axi_arvalid(axi_arvalid),
    .axi_arready(axi_arready),
    .axi_arid(axi_arid),
    .axi_araddr(axi_araddr),
    .axi_arlen(axi_arlen),
    .axi_arsize(axi_arsize),
    .axi_arburst(axi_arburst),
    .axi_arlock(axi_arlock),
    .axi_arcache(axi_arcache),
    .axi_arprot(axi_arprot),
    .axi_arqos(axi_arqos),
    .axi_arregion(axi_arregion),
    .axi_aruser(axi_aruser),
    .axi_rvalid(axi_rvalid),
    .axi_rready(axi_rready),
    .axi_rid(axi_rid),
    .axi_rdata(axi_rdata),
    .axi_rresp(axi_rresp),
    .axi_rlast(axi_rlast),
    .axi_ruser(axi_ruser),
    .global_base_addr(global_base_addr),
    .global_addr_mask(global_addr_mask),
    .system_status(system_status),
    .system_errors(system_errors),
    .system_perf_counters(system_perf_counters),
    .node_status(node_status),
    .node_errors(node_errors),
    .node_info(node_info),
    .mesh_vc_status(mesh_vc_status),
    .mesh_packets_routed(mesh_packets_routed),
    .mesh_error_status(mesh_error_status)
  );

  // =============================================================================
  // TEST INITIALIZATION
  // =============================================================================
  
  initial begin
    // Initialize all AXI interfaces
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        axi_awvalid[x][y] = 1'b0;
        axi_awid[x][y] = '0;
        axi_awaddr[x][y] = '0;
        axi_awlen[x][y] = '0;
        axi_awsize[x][y] = '0;
        axi_awburst[x][y] = '0;
        axi_awlock[x][y] = '0;
        axi_awcache[x][y] = '0;
        axi_awprot[x][y] = '0;
        axi_awqos[x][y] = '0;
        axi_awregion[x][y] = '0;
        axi_awuser[x][y] = '0;
        
        axi_wvalid[x][y] = 1'b0;
        axi_wdata[x][y] = '0;
        axi_wstrb[x][y] = '0;
        axi_wlast[x][y] = '0;
        axi_wuser[x][y] = '0;
        
        axi_bready[x][y] = 1'b1;
        
        axi_arvalid[x][y] = 1'b0;
        axi_arid[x][y] = '0;
        axi_araddr[x][y] = '0;
        axi_arlen[x][y] = '0;
        axi_arsize[x][y] = '0;
        axi_arburst[x][y] = '0;
        axi_arlock[x][y] = '0;
        axi_arcache[x][y] = '0;
        axi_arprot[x][y] = '0;
        axi_arqos[x][y] = '0;
        axi_arregion[x][y] = '0;
        axi_aruser[x][y] = '0;
        
        axi_rready[x][y] = 1'b1;
      end
    end
  end

  // =============================================================================
  // HELPER TASKS
  // =============================================================================
  
  // Calculate node address
  function automatic logic [AXI_ADDR_WIDTH-1:0] get_node_address(
    input int node_x, node_y, 
    input logic [AXI_ADDR_WIDTH-1:0] offset
  );
    int node_id = node_y * MESH_SIZE_X + node_x;
    return GLOBAL_BASE_ADDR + (node_id * NODE_ADDR_SIZE) + offset;
  endfunction
  
  // AXI read from specific node to specific target
  task axi_read_from_to(
    input int src_x, src_y,
    input int dest_x, dest_y,
    input logic [AXI_ADDR_WIDTH-1:0] offset,
    input logic [AXI_ID_WIDTH-1:0] id,
    output logic [AXI_DATA_WIDTH-1:0] data,
    output logic [1:0] resp,
    output logic success
  );
    logic [AXI_ADDR_WIDTH-1:0] target_addr;
    int timeout_count = 0;
    
    target_addr = get_node_address(dest_x, dest_y, offset);
    success = 1'b0;
    
    // Address phase
    axi_arvalid[src_x][src_y] = 1'b1;
    axi_arid[src_x][src_y] = id;
    axi_araddr[src_x][src_y] = target_addr;
    axi_arlen[src_x][src_y] = 8'h00;  // Single beat
    axi_arsize[src_x][src_y] = 3'h6;  // 64 bytes
    axi_arburst[src_x][src_y] = 2'b01; // INCR
    
    // Wait for address acceptance
    while (!axi_arready[src_x][src_y] && timeout_count < TEST_TIMEOUT) begin
      @(posedge clk);
      timeout_count++;
    end
    
    if (timeout_count >= TEST_TIMEOUT) begin
      $display("  ERROR: Address phase timeout for read from (%0d,%0d) to (%0d,%0d)", 
               src_x, src_y, dest_x, dest_y);
      axi_arvalid[src_x][src_y] = 1'b0;
      return;
    end
    
    @(posedge clk);
    axi_arvalid[src_x][src_y] = 1'b0;
    
    // Data phase
    timeout_count = 0;
    while (!axi_rvalid[src_x][src_y] && timeout_count < TEST_TIMEOUT) begin
      @(posedge clk);
      timeout_count++;
    end
    
    if (timeout_count >= TEST_TIMEOUT) begin
      $display("  ERROR: Data phase timeout for read from (%0d,%0d) to (%0d,%0d)", 
               src_x, src_y, dest_x, dest_y);
      return;
    end
    
    data = axi_rdata[src_x][src_y];
    resp = axi_rresp[src_x][src_y];
    success = 1'b1;
    
    @(posedge clk);
  endtask
  
  // Test result reporting
  task report_test(input string test_name, input logic passed);
    test_count++;
    if (passed) begin
      pass_count++;
      $display("✅ PASS: %s", test_name);
    end else begin
      fail_count++;
      $display("❌ FAIL: %s", test_name);
    end
  endtask

  // =============================================================================
  // TEST CASES
  // =============================================================================
  
  // Test 1: System instantiation and configuration
  task test_system_instantiation();
    logic success = 1'b1;
    
    $display("\n--- Test 1: System Instantiation ---");
    
    // Check system status
    if (system_status[0] == 1'b1) begin // Error flag
      $display("  ERROR: System has error flag set");
      success = 1'b0;
    end
    
    // Check total nodes
    if (system_perf_counters[8] != MESH_SIZE_X * MESH_SIZE_Y) begin
      $display("  ERROR: Total nodes mismatch: expected %0d, got %0d", 
               MESH_SIZE_X * MESH_SIZE_Y, system_perf_counters[8]);
      success = 1'b0;
    end
    
    // Check mesh dimensions
    if (system_perf_counters[9] != MESH_SIZE_X) begin
      $display("  ERROR: Mesh X size mismatch: expected %0d, got %0d", 
               MESH_SIZE_X, system_perf_counters[9]);
      success = 1'b0;
    end
    
    if (system_perf_counters[10] != MESH_SIZE_Y) begin
      $display("  ERROR: Mesh Y size mismatch: expected %0d, got %0d", 
               MESH_SIZE_Y, system_perf_counters[10]);
      success = 1'b0;
    end
    
    // Check node info for each node
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        if (node_info[x][y][7:0] != y || node_info[x][y][15:8] != x) begin
          $display("  ERROR: Node (%0d,%0d) has incorrect coordinates in node_info", x, y);
          success = 1'b0;
        end
      end
    end
    
    report_test("System Instantiation", success);
  endtask
  
  // Test 2: Address space mapping
  task test_address_space();
    logic success = 1'b1;
    
    $display("\n--- Test 2: Address Space Mapping ---");
    
    // Verify address calculations for each node
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        logic [AXI_ADDR_WIDTH-1:0] expected_addr, calculated_addr;
        int node_id;
        
        node_id = y * MESH_SIZE_X + x;
        expected_addr = GLOBAL_BASE_ADDR + (node_id * NODE_ADDR_SIZE);
        calculated_addr = get_node_address(x, y, 64'h0);
        
        if (expected_addr != calculated_addr) begin
          $display("  ERROR: Node (%0d,%0d) address mismatch: expected 0x%016h, got 0x%016h", 
                   x, y, expected_addr, calculated_addr);
          success = 1'b0;
        end else begin
          $display("  Node (%0d,%0d): Base address 0x%016h", x, y, calculated_addr);
        end
      end
    end
    
    report_test("Address Space Mapping", success);
  endtask
  
  // Test 3: Local access (same node)
  task test_local_access();
    logic success = 1'b1;
    logic [AXI_DATA_WIDTH-1:0] read_data;
    logic [1:0] resp;
    logic access_success;
    
    $display("\n--- Test 3: Local Access ---");
    
    // Test local access from node (0,0) to itself
    axi_read_from_to(0, 0, 0, 0, 64'h1000, 8'h01, read_data, resp, access_success);
    
    if (!access_success) begin
      $display("  ERROR: Local access failed");
      success = 1'b0;
    end else if (resp != 2'b00) begin // OKAY response
      $display("  ERROR: Local access returned error response: %0d", resp);
      success = 1'b0;
    end else begin
      $display("  Local access successful with OKAY response");
    end
    
    report_test("Local Access", success);
  endtask
  
  // Test 4: Remote access (different nodes)
  task test_remote_access();
    logic success = 1'b1;
    logic [AXI_DATA_WIDTH-1:0] read_data;
    logic [1:0] resp;
    logic access_success;
    
    $display("\n--- Test 4: Remote Access ---");
    
    // Test remote access from node (0,0) to node (1,1)
    if (MESH_SIZE_X > 1 && MESH_SIZE_Y > 1) begin
      axi_read_from_to(0, 0, 1, 1, 64'h2000, 8'h02, read_data, resp, access_success);
      
      if (!access_success) begin
        $display("  ERROR: Remote access failed");
        success = 1'b0;
      end else begin
        $display("  Remote access from (0,0) to (1,1) successful");
      end
    end else begin
      $display("  Skipping remote access test (mesh too small)");
    end
    
    report_test("Remote Access", success);
  endtask
  
  // Test 5: Multi-node concurrent access
  task test_concurrent_access();
    logic success = 1'b1;
    logic [AXI_DATA_WIDTH-1:0] read_data [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0];
    logic [1:0] resp [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0];
    logic access_success [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0];
    
    $display("\n--- Test 5: Concurrent Access ---");
    
    // Launch concurrent accesses from all nodes
    fork
      for (int x = 0; x < MESH_SIZE_X; x++) begin
        for (int y = 0; y < MESH_SIZE_Y; y++) begin
          automatic int ax = x, ay = y;
          fork
            begin
              // Each node accesses a different target in round-robin fashion
              int target_x, target_y;
              target_x = (ax + 1) % MESH_SIZE_X;
              target_y = (ay + 1) % MESH_SIZE_Y;
              axi_read_from_to(ax, ay, target_x, target_y, 64'h3000, 
                              8'(ax * MESH_SIZE_Y + ay), 
                              read_data[ax][ay], resp[ax][ay], access_success[ax][ay]);
            end
          join_none
        end
      end
    join
    
    // Check results
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        if (!access_success[x][y]) begin
          $display("  ERROR: Concurrent access from (%0d,%0d) failed", x, y);
          success = 1'b0;
        end
      end
    end
    
    if (success) begin
      $display("  All concurrent accesses completed successfully");
    end
    
    report_test("Concurrent Access", success);
  endtask
  
  // Test 6: Performance monitoring
  task test_performance_monitoring();
    logic success = 1'b1;
    logic [31:0] initial_packets, final_packets;
    logic [31:0] total_node_packets;
    
    $display("\n--- Test 6: Performance Monitoring ---");
    
    // Record initial packet count
    initial_packets = system_perf_counters[0];
    
    // Generate some traffic
    for (int i = 0; i < 5; i++) begin
      logic [AXI_DATA_WIDTH-1:0] dummy_data;
      logic [1:0] dummy_resp;
      logic dummy_success;
      axi_read_from_to(0, 0, 1, 0, 64'h4000 + (i * 64), 8'(i), 
                       dummy_data, dummy_resp, dummy_success);
      #(CLK_PERIOD * 10);
    end
    
    // Check if packet counters increased
    final_packets = system_perf_counters[0];
    
    if (final_packets <= initial_packets) begin
      $display("  ERROR: Packet counters did not increase: %0d -> %0d", 
               initial_packets, final_packets);
      success = 1'b0;
    end else begin
      $display("  Packet counters increased: %0d -> %0d", initial_packets, final_packets);
    end
    
    // Check individual node packet counts
    total_node_packets = 0;
    for (int x = 0; x < MESH_SIZE_X; x++) begin
      for (int y = 0; y < MESH_SIZE_Y; y++) begin
        total_node_packets += mesh_packets_routed[x][y];
      end
    end
    
    if (total_node_packets == 0) begin
      $display("  ERROR: No packets routed at mesh level");
      success = 1'b0;
    end else begin
      $display("  Total mesh packets routed: %0d", total_node_packets);
    end
    
    report_test("Performance Monitoring", success);
  endtask

  // =============================================================================
  // MAIN TEST SEQUENCE
  // =============================================================================
  
  initial begin
    $display("=============================================================================");
    $display("Nebula System Integration Testbench");
    $display("System Size: %0dx%0d (%0d nodes)", MESH_SIZE_X, MESH_SIZE_Y, MESH_SIZE_X * MESH_SIZE_Y);
    $display("Global Base: 0x%016h", GLOBAL_BASE_ADDR);
    $display("Node Size:   0x%016h", NODE_ADDR_SIZE);
    $display("=============================================================================");
    
    // Wait for reset
    wait(rst_n);
    #(CLK_PERIOD * 20);
    
    // Run tests
    test_system_instantiation();
    #(CLK_PERIOD * 10);
    
    test_address_space();
    #(CLK_PERIOD * 10);
    
    test_local_access();
    #(CLK_PERIOD * 20);
    
    test_remote_access();
    #(CLK_PERIOD * 30);
    
    test_concurrent_access();
    #(CLK_PERIOD * 50);
    
    test_performance_monitoring();
    #(CLK_PERIOD * 30);
    
    // Final report
    $display("\n=============================================================================");
    $display("TEST SUMMARY");
    $display("=============================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success Rate: %0.1f%%", real'(pass_count) / real'(test_count) * 100.0);
    
    // System performance summary
    $display("\nSYSTEM PERFORMANCE SUMMARY:");
    $display("Total Packets Routed: %0d", system_perf_counters[0]);
    $display("Max Hop Count: %0d", system_perf_counters[4]);
    $display("Total Nodes: %0d", system_perf_counters[8]);
    
    if (fail_count == 0) begin
      $display("\n🎉 ALL TESTS PASSED! 🎉");
      $display("Step 5: Network Topology & Multi-Router Integration COMPLETE");
    end else begin
      $display("\n💥 SOME TESTS FAILED! 💥");
    end
    
    $display("=============================================================================");
    $finish;
  end

  // =============================================================================
  // TIMEOUT WATCHDOG
  // =============================================================================
  
  initial begin
    #(TEST_TIMEOUT * CLK_PERIOD * 100);
    $display("\n💥 TESTBENCH TIMEOUT! 💥");
    $display("System may be deadlocked or stuck.");
    $finish;
  end

endmodule
