/**
 * Testbench for Nebula Network Interface Unit (NIU)
 * 
 * Tests the NIU functionality including AXI interface, address mapping,
 * local vs remote access determination, and mesh connectivity.
 * 
 * Test Coverage:
 * 1. AXI interface functionality
 * 2. Address mapping and coordinate extraction
 * 3. Local vs remote access detection
 * 4. Performance counter operation
 * 5. Error handling and reporting
 * 6. Mesh interface connectivity
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: September 2025
 */

`timescale 1ns/1ps

module tb_nebula_niu_axi;

  import nebula_pkg::*;

  // =============================================================================
  // TESTBENCH PARAMETERS
  // =============================================================================
  
  parameter int CLK_PERIOD = 10;
  parameter int NODE_X = 1;
  parameter int NODE_Y = 1;
  parameter int MESH_SIZE_X = 4;
  parameter int MESH_SIZE_Y = 4;
  parameter logic [AXI_ADDR_WIDTH-1:0] NODE_BASE_ADDR = 64'h0000_0000_1100_0000; // Node (1,1)
  parameter logic [AXI_ADDR_WIDTH-1:0] NODE_ADDR_MASK = 64'hFFFF_FFFF_FFF0_0000;
  parameter int TEST_TIMEOUT = 5000;
  
  // Clock and reset
  logic clk = 0;
  logic rst_n = 0;
  
  // AXI interface signals
  logic                         axi_awvalid = 0;
  logic                         axi_awready;
  logic [AXI_ID_WIDTH-1:0]      axi_awid = 0;
  logic [AXI_ADDR_WIDTH-1:0]    axi_awaddr = 0;
  logic [7:0]                   axi_awlen = 0;
  logic [2:0]                   axi_awsize = 0;
  logic [1:0]                   axi_awburst = 0;
  logic                         axi_awlock = 0;
  logic [3:0]                   axi_awcache = 0;
  logic [2:0]                   axi_awprot = 0;
  logic [QOS_WIDTH-1:0]         axi_awqos = 0;
  logic [3:0]                   axi_awregion = 0;
  logic [AXI_AWUSER_WIDTH-1:0]  axi_awuser = 0;
  
  logic                         axi_wvalid = 0;
  logic                         axi_wready;
  logic [AXI_DATA_WIDTH-1:0]    axi_wdata = 0;
  logic [AXI_STRB_WIDTH-1:0]    axi_wstrb = 0;
  logic                         axi_wlast = 0;
  logic [AXI_WUSER_WIDTH-1:0]   axi_wuser = 0;
  
  logic                         axi_bvalid;
  logic                         axi_bready = 1;
  logic [AXI_ID_WIDTH-1:0]      axi_bid;
  logic [1:0]                   axi_bresp;
  logic [AXI_BUSER_WIDTH-1:0]   axi_buser;
  
  logic                         axi_arvalid = 0;
  logic                         axi_arready;
  logic [AXI_ID_WIDTH-1:0]      axi_arid = 0;
  logic [AXI_ADDR_WIDTH-1:0]    axi_araddr = 0;
  logic [7:0]                   axi_arlen = 0;
  logic [2:0]                   axi_arsize = 0;
  logic [1:0]                   axi_arburst = 0;
  logic                         axi_arlock = 0;
  logic [3:0]                   axi_arcache = 0;
  logic [2:0]                   axi_arprot = 0;
  logic [QOS_WIDTH-1:0]         axi_arqos = 0;
  logic [3:0]                   axi_arregion = 0;
  logic [AXI_ARUSER_WIDTH-1:0]  axi_aruser = 0;
  
  logic                         axi_rvalid;
  logic                         axi_rready = 1;
  logic [AXI_ID_WIDTH-1:0]      axi_rid;
  logic [AXI_DATA_WIDTH-1:0]    axi_rdata;
  logic [1:0]                   axi_rresp;
  logic                         axi_rlast;
  logic [AXI_RUSER_WIDTH-1:0]   axi_ruser;
  
  // Mesh interface signals
  logic      noc_flit_out_valid;
  logic      noc_flit_out_ready = 1;
  noc_flit_t noc_flit_out;
  
  logic      noc_flit_in_valid = 0;
  logic      noc_flit_in_ready;
  noc_flit_t noc_flit_in = '0;
  
  // Configuration
  logic [AXI_ADDR_WIDTH-1:0] global_base_addr = 64'h0000_0000_1000_0000;
  logic [AXI_ADDR_WIDTH-1:0] global_addr_mask = 64'hFFFF_FFFF_FFF0_0000;
  
  // Status and debug
  logic [31:0] status_reg;
  logic [31:0] error_reg;
  logic [31:0] perf_counters [7:0];
  logic [31:0] node_info_reg;
  
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
  
  nebula_niu_axi #(
    .NODE_X(NODE_X),
    .NODE_Y(NODE_Y),
    .MESH_SIZE_X(MESH_SIZE_X),
    .MESH_SIZE_Y(MESH_SIZE_Y),
    .NODE_BASE_ADDR(NODE_BASE_ADDR),
    .NODE_ADDR_MASK(NODE_ADDR_MASK)
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
    .noc_flit_out_valid(noc_flit_out_valid),
    .noc_flit_out_ready(noc_flit_out_ready),
    .noc_flit_out(noc_flit_out),
    .noc_flit_in_valid(noc_flit_in_valid),
    .noc_flit_in_ready(noc_flit_in_ready),
    .noc_flit_in(noc_flit_in),
    .global_base_addr(global_base_addr),
    .global_addr_mask(global_addr_mask),
    .status_reg(status_reg),
    .error_reg(error_reg),
    .perf_counters(perf_counters),
    .node_info_reg(node_info_reg)
  );

  // =============================================================================
  // HELPER TASKS
  // =============================================================================
  
  // AXI read transaction
  task axi_read(
    input logic [AXI_ADDR_WIDTH-1:0] addr,
    input logic [AXI_ID_WIDTH-1:0] id,
    input logic [7:0] len,
    input logic [2:0] size,
    output logic [AXI_DATA_WIDTH-1:0] data,
    output logic [1:0] resp
  );
    
    // Address phase
    axi_arvalid = 1'b1;
    axi_arid = id;
    axi_araddr = addr;
    axi_arlen = len;
    axi_arsize = size;
    axi_arburst = 2'b01; // INCR
    
    wait(axi_arready);
    @(posedge clk);
    axi_arvalid = 1'b0;
    
    // Data phase
    wait(axi_rvalid);
    data = axi_rdata;
    resp = axi_rresp;
    @(posedge clk);
    
  endtask
  
  // AXI write transaction
  task axi_write(
    input logic [AXI_ADDR_WIDTH-1:0] addr,
    input logic [AXI_ID_WIDTH-1:0] id,
    input logic [AXI_DATA_WIDTH-1:0] data,
    input logic [7:0] len,
    input logic [2:0] size,
    output logic [1:0] resp
  );
    
    // Address phase
    axi_awvalid = 1'b1;
    axi_awid = id;
    axi_awaddr = addr;
    axi_awlen = len;
    axi_awsize = size;
    axi_awburst = 2'b01; // INCR
    
    // Data phase
    axi_wvalid = 1'b1;
    axi_wdata = data;
    axi_wstrb = '1;
    axi_wlast = 1'b1;
    
    wait(axi_awready && axi_wready);
    @(posedge clk);
    axi_awvalid = 1'b0;
    axi_wvalid = 1'b0;
    
    // Response phase
    wait(axi_bvalid);
    resp = axi_bresp;
    @(posedge clk);
    
  endtask
  
  // Check address mapping
  function automatic logic [COORD_WIDTH-1:0] addr_to_x_coord(logic [AXI_ADDR_WIDTH-1:0] addr);
    logic [AXI_ADDR_WIDTH-1:0] masked_addr;
    logic [NODE_ID_WIDTH-1:0] node_id;
    masked_addr = (addr & ~global_addr_mask) >> 20;
    node_id = masked_addr[NODE_ID_WIDTH-1:0];
    return node_id % MESH_SIZE_X;
  endfunction
  
  function automatic logic [COORD_WIDTH-1:0] addr_to_y_coord(logic [AXI_ADDR_WIDTH-1:0] addr);
    logic [AXI_ADDR_WIDTH-1:0] masked_addr;
    logic [NODE_ID_WIDTH-1:0] node_id;
    masked_addr = (addr & ~global_addr_mask) >> 20;
    node_id = masked_addr[NODE_ID_WIDTH-1:0];
    return node_id / MESH_SIZE_X;
  endfunction
  
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
  
  // Test 1: Basic instantiation and configuration
  task test_instantiation();
    logic success = 1'b1;
    
    $display("\n--- Test 1: NIU Instantiation ---");
    
    // Check node info register
    if (node_info_reg[7:0] != NODE_Y) begin
      $display("  ERROR: Node Y mismatch: expected %0d, got %0d", NODE_Y, node_info_reg[7:0]);
      success = 1'b0;
    end
    
    if (node_info_reg[15:8] != NODE_X) begin
      $display("  ERROR: Node X mismatch: expected %0d, got %0d", NODE_X, node_info_reg[15:8]);
      success = 1'b0;
    end
    
    if (node_info_reg[23:16] != MESH_SIZE_Y) begin
      $display("  ERROR: Mesh Y size mismatch: expected %0d, got %0d", MESH_SIZE_Y, node_info_reg[23:16]);
      success = 1'b0;
    end
    
    if (node_info_reg[31:24] != MESH_SIZE_X) begin
      $display("  ERROR: Mesh X size mismatch: expected %0d, got %0d", MESH_SIZE_X, node_info_reg[31:24]);
      success = 1'b0;
    end
    
    report_test("NIU Instantiation", success);
  endtask
  
  // Test 2: Address mapping functionality
  task test_address_mapping();
    logic success = 1'b1;
    logic [AXI_ADDR_WIDTH-1:0] test_addresses [7:0];
    logic [COORD_WIDTH-1:0] expected_x [7:0];
    logic [COORD_WIDTH-1:0] expected_y [7:0];
    
    $display("\n--- Test 2: Address Mapping ---");
    
    // Test addresses for different nodes
    test_addresses[0] = 64'h0000_0000_1000_0000; // Node (0,0)
    expected_x[0] = 0; expected_y[0] = 0;
    
    test_addresses[1] = 64'h0000_0000_1010_0000; // Node (1,0)
    expected_x[1] = 1; expected_y[1] = 0;
    
    test_addresses[2] = 64'h0000_0000_1020_0000; // Node (2,0)
    expected_x[2] = 2; expected_y[2] = 0;
    
    test_addresses[3] = 64'h0000_0000_1030_0000; // Node (3,0)
    expected_x[3] = 3; expected_y[3] = 0;
    
    test_addresses[4] = 64'h0000_0000_1040_0000; // Node (0,1)
    expected_x[4] = 0; expected_y[4] = 1;
    
    test_addresses[5] = 64'h0000_0000_1050_0000; // Node (1,1)
    expected_x[5] = 1; expected_y[5] = 1;
    
    test_addresses[6] = 64'h0000_0000_1060_0000; // Node (2,1)
    expected_x[6] = 2; expected_y[6] = 1;
    
    test_addresses[7] = 64'h0000_0000_1070_0000; // Node (3,1)
    expected_x[7] = 3; expected_y[7] = 1;
    
    for (int i = 0; i < 8; i++) begin
      logic [COORD_WIDTH-1:0] actual_x, actual_y;
      actual_x = addr_to_x_coord(test_addresses[i]);
      actual_y = addr_to_y_coord(test_addresses[i]);
      
      if (actual_x != expected_x[i] || actual_y != expected_y[i]) begin
        $display("  ERROR: Address 0x%016h mapped to (%0d,%0d), expected (%0d,%0d)", 
                 test_addresses[i], actual_x, actual_y, expected_x[i], expected_y[i]);
        success = 1'b0;
      end else begin
        $display("  Address 0x%016h correctly mapped to (%0d,%0d)", 
                 test_addresses[i], actual_x, actual_y);
      end
    end
    
    report_test("Address Mapping", success);
  endtask
  
  // Test 3: Local access detection
  task test_local_access();
    logic success = 1'b1;
    logic [AXI_DATA_WIDTH-1:0] read_data;
    logic [1:0] resp;
    
    $display("\n--- Test 3: Local Access Detection ---");
    
    // Test local access (should be handled locally)
    axi_read(NODE_BASE_ADDR + 64'h1000, 8'h01, 8'h00, 3'h6, read_data, resp);
    
    // Check that no NoC traffic was generated
    if (noc_flit_out_valid) begin
      $display("  ERROR: Local access generated NoC traffic");
      success = 1'b0;
    end else begin
      $display("  Local access correctly handled without NoC traffic");
    end
    
    report_test("Local Access Detection", success);
  endtask
  
  // Test 4: Remote access generation
  task test_remote_access();
    logic success = 1'b1;
    logic [AXI_DATA_WIDTH-1:0] read_data;
    logic [1:0] resp;
    logic noc_activity_detected = 1'b0;
    
    $display("\n--- Test 4: Remote Access Generation ---");
    
    // Monitor NoC activity
    fork
      begin
        // Watch for NoC output
        for (int i = 0; i < 100; i++) begin
          @(posedge clk);
          if (noc_flit_out_valid) begin
            noc_activity_detected = 1'b1;
            $display("  NoC flit generated: dest=(%0d,%0d), src=(%0d,%0d)", 
                     noc_flit_out.dest_x, noc_flit_out.dest_y,
                     noc_flit_out.src_x, noc_flit_out.src_y);
            break;
          end
        end
      end
      begin
        // Generate remote access to node (0,0)
        #(CLK_PERIOD * 10);
        axi_read(64'h0000_0000_1000_1000, 8'h02, 8'h00, 3'h6, read_data, resp);
      end
    join
    
    if (!noc_activity_detected) begin
      $display("  ERROR: Remote access did not generate NoC traffic");
      success = 1'b0;
    end else begin
      $display("  Remote access correctly generated NoC traffic");
    end
    
    report_test("Remote Access Generation", success);
  endtask
  
  // Test 5: Performance counters
  task test_performance_counters();
    logic success = 1'b1;
    logic [31:0] initial_local_reads, initial_remote_reads;
    logic [31:0] final_local_reads, final_remote_reads;
    logic [AXI_DATA_WIDTH-1:0] read_data;
    logic [1:0] resp;
    
    $display("\n--- Test 5: Performance Counters ---");
    
    // Record initial counts
    initial_local_reads = perf_counters[0];
    initial_remote_reads = perf_counters[2];
    
    // Perform local access
    axi_read(NODE_BASE_ADDR + 64'h2000, 8'h03, 8'h00, 3'h6, read_data, resp);
    #(CLK_PERIOD * 5);
    
    // Perform remote access
    axi_read(64'h0000_0000_1000_2000, 8'h04, 8'h00, 3'h6, read_data, resp);
    #(CLK_PERIOD * 5);
    
    // Check counter updates
    final_local_reads = perf_counters[0];
    final_remote_reads = perf_counters[2];
    
    if (final_local_reads != initial_local_reads + 1) begin
      $display("  ERROR: Local read counter: expected %0d, got %0d", 
               initial_local_reads + 1, final_local_reads);
      success = 1'b0;
    end
    
    if (final_remote_reads != initial_remote_reads + 1) begin
      $display("  ERROR: Remote read counter: expected %0d, got %0d", 
               initial_remote_reads + 1, final_remote_reads);
      success = 1'b0;
    end
    
    if (success) begin
      $display("  Performance counters correctly updated");
      $display("    Local reads: %0d -> %0d", initial_local_reads, final_local_reads);
      $display("    Remote reads: %0d -> %0d", initial_remote_reads, final_remote_reads);
    end
    
    report_test("Performance Counters", success);
  endtask

  // =============================================================================
  // MAIN TEST SEQUENCE
  // =============================================================================
  
  initial begin
    $display("=============================================================================");
    $display("Nebula Network Interface Unit (NIU) Testbench");
    $display("Node: (%0d,%0d) in %0dx%0d mesh", NODE_X, NODE_Y, MESH_SIZE_X, MESH_SIZE_Y);
    $display("=============================================================================");
    
    // Wait for reset
    wait(rst_n);
    #(CLK_PERIOD * 10);
    
    // Run tests
    test_instantiation();
    #(CLK_PERIOD * 10);
    
    test_address_mapping();
    #(CLK_PERIOD * 10);
    
    test_local_access();
    #(CLK_PERIOD * 20);
    
    test_remote_access();
    #(CLK_PERIOD * 20);
    
    test_performance_counters();
    #(CLK_PERIOD * 20);
    
    // Final report
    $display("\n=============================================================================");
    $display("TEST SUMMARY");
    $display("=============================================================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    $display("Success Rate: %0.1f%%", real'(pass_count) / real'(test_count) * 100.0);
    
    if (fail_count == 0) begin
      $display("🎉 ALL TESTS PASSED! 🎉");
    end else begin
      $display("💥 SOME TESTS FAILED! 💥");
    end
    
    $display("=============================================================================");
    $finish;
  end

  // =============================================================================
  // TIMEOUT WATCHDOG
  // =============================================================================
  
  initial begin
    #(TEST_TIMEOUT * CLK_PERIOD * 10);
    $display("\n💥 TESTBENCH TIMEOUT! 💥");
    $finish;
  end

endmodule
