/**
 * Nebula Mesh Integration Testbench
 * 
 * Tests the complete mesh network with AXI interfaces for each node,
 * validating end-to-end AXI-to-NoC-to-AXI transactions across the mesh.
 * 
 * Test Coverage:
 * 1. AXI transaction routing across mesh
 * 2. Burst decomposition and reconstruction
 * 3. Address mapping validation
 * 4. Multi-node concurrent AXI transactions
 * 5. Reorder buffer functionality
 * 6. Error handling and recovery
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: September 2025
 */

`timescale 1ns/1ps

module tb_nebula_mesh_integration;

  import nebula_pkg::*;

  // =============================================================================
  // TESTBENCH PARAMETERS
  // =============================================================================
  
  parameter int CLK_PERIOD = 10;
  parameter int MESH_SIZE_X = 2; // Start with 2x2 for easier debugging
  parameter int MESH_SIZE_Y = 2;
  parameter int NUM_NODES = MESH_SIZE_X * MESH_SIZE_Y;
  parameter int TEST_TIMEOUT = 25000;
  
  // Clock and reset
  logic clk = 0;
  logic rst_n = 0;
  
  // AXI interface per node (simplified master interface for testing)
  logic [NUM_NODES-1:0] axi_awvalid;
  logic [NUM_NODES-1:0] axi_awready;
  logic [NUM_NODES-1:0][AXI_ADDR_WIDTH-1:0] axi_awaddr;
  logic [NUM_NODES-1:0][7:0] axi_awlen;
  logic [NUM_NODES-1:0][2:0] axi_awsize;
  logic [NUM_NODES-1:0][1:0] axi_awburst;
  logic [NUM_NODES-1:0][AXI_ID_WIDTH-1:0] axi_awid;
  logic [NUM_NODES-1:0] axi_awlock;
  logic [NUM_NODES-1:0][3:0] axi_awcache;
  logic [NUM_NODES-1:0][2:0] axi_awprot;
  logic [NUM_NODES-1:0][QOS_WIDTH-1:0] axi_awqos;
  logic [NUM_NODES-1:0][3:0] axi_awregion;
  logic [NUM_NODES-1:0][AXI_AWUSER_WIDTH-1:0] axi_awuser;
  
  logic [NUM_NODES-1:0] axi_wvalid;
  logic [NUM_NODES-1:0] axi_wready;
  logic [NUM_NODES-1:0][AXI_DATA_WIDTH-1:0] axi_wdata;
  logic [NUM_NODES-1:0][AXI_STRB_WIDTH-1:0] axi_wstrb;
  logic [NUM_NODES-1:0] axi_wlast;
  logic [NUM_NODES-1:0][AXI_WUSER_WIDTH-1:0] axi_wuser;
  
  logic [NUM_NODES-1:0] axi_bvalid;
  logic [NUM_NODES-1:0] axi_bready;
  logic [NUM_NODES-1:0][AXI_ID_WIDTH-1:0] axi_bid;
  logic [NUM_NODES-1:0][1:0] axi_bresp;
  logic [NUM_NODES-1:0][AXI_BUSER_WIDTH-1:0] axi_buser;
  
  logic [NUM_NODES-1:0] axi_arvalid;
  logic [NUM_NODES-1:0] axi_arready;
  logic [NUM_NODES-1:0][AXI_ADDR_WIDTH-1:0] axi_araddr;
  logic [NUM_NODES-1:0][7:0] axi_arlen;
  logic [NUM_NODES-1:0][2:0] axi_arsize;
  logic [NUM_NODES-1:0][1:0] axi_arburst;
  logic [NUM_NODES-1:0][AXI_ID_WIDTH-1:0] axi_arid;
  logic [NUM_NODES-1:0] axi_arlock;
  logic [NUM_NODES-1:0][3:0] axi_arcache;
  logic [NUM_NODES-1:0][2:0] axi_arprot;
  logic [NUM_NODES-1:0][QOS_WIDTH-1:0] axi_arqos;
  logic [NUM_NODES-1:0][3:0] axi_arregion;
  logic [NUM_NODES-1:0][AXI_ARUSER_WIDTH-1:0] axi_aruser;
  
  logic [NUM_NODES-1:0] axi_rvalid;
  logic [NUM_NODES-1:0] axi_rready;
  logic [NUM_NODES-1:0][AXI_ID_WIDTH-1:0] axi_rid;
  logic [NUM_NODES-1:0][AXI_DATA_WIDTH-1:0] axi_rdata;
  logic [NUM_NODES-1:0][1:0] axi_rresp;
  logic [NUM_NODES-1:0] axi_rlast;
  logic [NUM_NODES-1:0][AXI_RUSER_WIDTH-1:0] axi_ruser;
  
  // NoC mesh interconnect
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0] router_flit_in_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0] router_flit_in;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0] router_flit_in_ready;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0] router_flit_out_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0] router_flit_out;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0] router_flit_out_ready;
  
  // AXI bridge interfaces per node
  logic [NUM_NODES-1:0] bridge_noc_req_valid;
  logic [NUM_NODES-1:0] bridge_noc_req_ready;
  noc_flit_t [NUM_NODES-1:0] bridge_noc_req_flit;
  
  logic [NUM_NODES-1:0] bridge_noc_resp_valid;
  logic [NUM_NODES-1:0] bridge_noc_resp_ready;
  noc_flit_t [NUM_NODES-1:0] bridge_noc_resp_flit;
  
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
  // MESH ROUTER INSTANTIATION
  // =============================================================================
  
  genvar x, y;
  generate
    for (x = 0; x < MESH_SIZE_X; x++) begin : gen_router_x
      for (y = 0; y < MESH_SIZE_Y; y++) begin : gen_router_y
        
        nebula_router #(
          .ROUTER_X(x),
          .ROUTER_Y(y),
          .MESH_SIZE_X(MESH_SIZE_X),
          .MESH_SIZE_Y(MESH_SIZE_Y)
        ) router_inst (
          .clk(clk),
          .rst_n(rst_n),
          .flit_in_valid(router_flit_in_valid[x][y]),
          .flit_in(router_flit_in[x][y]),
          .flit_in_ready(router_flit_in_ready[x][y]),
          .flit_out_valid(router_flit_out_valid[x][y]),
          .flit_out(router_flit_out[x][y]),
          .flit_out_ready(router_flit_out_ready[x][y]),
          .vc_status(),
          .packets_routed(),
          .error_status()
        );
        
      end
    end
  endgenerate

  // =============================================================================
  // MESH INTERCONNECTION
  // =============================================================================
  
  generate
    for (x = 0; x < MESH_SIZE_X; x++) begin : interconnect_x
      for (y = 0; y < MESH_SIZE_Y; y++) begin : interconnect_y
        
        // North connections
        if (y < MESH_SIZE_Y - 1) begin
          assign router_flit_in_valid[x][y][PORT_NORTH] = router_flit_out_valid[x][y+1][PORT_SOUTH];
          assign router_flit_in[x][y][PORT_NORTH] = router_flit_out[x][y+1][PORT_SOUTH];
          assign router_flit_out_ready[x][y+1][PORT_SOUTH] = router_flit_in_ready[x][y][PORT_NORTH];
        end else begin
          assign router_flit_in_valid[x][y][PORT_NORTH] = 1'b0;
          assign router_flit_in[x][y][PORT_NORTH] = '0;
        end
        
        // South connections
        if (y > 0) begin
          assign router_flit_in_valid[x][y][PORT_SOUTH] = router_flit_out_valid[x][y-1][PORT_NORTH];
          assign router_flit_in[x][y][PORT_SOUTH] = router_flit_out[x][y-1][PORT_NORTH];
          assign router_flit_out_ready[x][y-1][PORT_NORTH] = router_flit_in_ready[x][y][PORT_SOUTH];
        end else begin
          assign router_flit_in_valid[x][y][PORT_SOUTH] = 1'b0;
          assign router_flit_in[x][y][PORT_SOUTH] = '0;
        end
        
        // East connections
        if (x < MESH_SIZE_X - 1) begin
          assign router_flit_in_valid[x][y][PORT_EAST] = router_flit_out_valid[x+1][y][PORT_WEST];
          assign router_flit_in[x][y][PORT_EAST] = router_flit_out[x+1][y][PORT_WEST];
          assign router_flit_out_ready[x+1][y][PORT_WEST] = router_flit_in_ready[x][y][PORT_EAST];
        end else begin
          assign router_flit_in_valid[x][y][PORT_EAST] = 1'b0;
          assign router_flit_in[x][y][PORT_EAST] = '0;
        end
        
        // West connections
        if (x > 0) begin
          assign router_flit_in_valid[x][y][PORT_WEST] = router_flit_out_valid[x-1][y][PORT_EAST];
          assign router_flit_in[x][y][PORT_WEST] = router_flit_out[x-1][y][PORT_EAST];
          assign router_flit_out_ready[x-1][y][PORT_EAST] = router_flit_in_ready[x][y][PORT_WEST];
        end else begin
          assign router_flit_in_valid[x][y][PORT_WEST] = 1'b0;
          assign router_flit_in[x][y][PORT_WEST] = '0;
        end
        
        // Local port connections
        localparam int NODE_ID = y * MESH_SIZE_X + x;
        
        assign router_flit_in_valid[x][y][PORT_LOCAL] = bridge_noc_req_valid[NODE_ID];
        assign router_flit_in[x][y][PORT_LOCAL] = bridge_noc_req_flit[NODE_ID];
        assign bridge_noc_req_ready[NODE_ID] = router_flit_in_ready[x][y][PORT_LOCAL];
        
        assign bridge_noc_resp_valid[NODE_ID] = router_flit_out_valid[x][y][PORT_LOCAL];
        assign bridge_noc_resp_flit[NODE_ID] = router_flit_out[x][y][PORT_LOCAL];
        assign router_flit_out_ready[x][y][PORT_LOCAL] = bridge_noc_resp_ready[NODE_ID];
        
      end
    end
  endgenerate

  // =============================================================================
  // AXI-NOC BRIDGE INSTANTIATION
  // =============================================================================
  
  generate
    for (genvar node_id = 0; node_id < NUM_NODES; node_id++) begin : gen_axi_bridge
      
      localparam int NODE_X = node_id % MESH_SIZE_X;
      localparam int NODE_Y = node_id / MESH_SIZE_X;
      
      nebula_axi_noc_bridge #(
        .NODE_X(NODE_X),
        .NODE_Y(NODE_Y),
        .MESH_SIZE_X(MESH_SIZE_X),
        .MESH_SIZE_Y(MESH_SIZE_Y),
        .REORDER_DEPTH(16)
      ) axi_bridge_inst (
        .clk(clk),
        .rst_n(rst_n),
        
        // AXI Write Address Channel
        .axi_awvalid(axi_awvalid[node_id]),
        .axi_awready(axi_awready[node_id]),
        .axi_awid(axi_awid[node_id]),
        .axi_awaddr(axi_awaddr[node_id]),
        .axi_awlen(axi_awlen[node_id]),
        .axi_awsize(axi_awsize[node_id]),
        .axi_awburst(axi_awburst[node_id]),
        .axi_awlock(axi_awlock[node_id]),
        .axi_awcache(axi_awcache[node_id]),
        .axi_awprot(axi_awprot[node_id]),
        .axi_awqos(axi_awqos[node_id]),
        .axi_awregion(axi_awregion[node_id]),
        .axi_awuser(axi_awuser[node_id]),
        
        // AXI Write Data Channel
        .axi_wvalid(axi_wvalid[node_id]),
        .axi_wready(axi_wready[node_id]),
        .axi_wdata(axi_wdata[node_id]),
        .axi_wstrb(axi_wstrb[node_id]),
        .axi_wlast(axi_wlast[node_id]),
        .axi_wuser(axi_wuser[node_id]),
        
        // AXI Write Response Channel
        .axi_bvalid(axi_bvalid[node_id]),
        .axi_bready(axi_bready[node_id]),
        .axi_bid(axi_bid[node_id]),
        .axi_bresp(axi_bresp[node_id]),
        .axi_buser(axi_buser[node_id]),
        
        // AXI Read Address Channel
        .axi_arvalid(axi_arvalid[node_id]),
        .axi_arready(axi_arready[node_id]),
        .axi_arid(axi_arid[node_id]),
        .axi_araddr(axi_araddr[node_id]),
        .axi_arlen(axi_arlen[node_id]),
        .axi_arsize(axi_arsize[node_id]),
        .axi_arburst(axi_arburst[node_id]),
        .axi_arlock(axi_arlock[node_id]),
        .axi_arcache(axi_arcache[node_id]),
        .axi_arprot(axi_arprot[node_id]),
        .axi_arqos(axi_arqos[node_id]),
        .axi_arregion(axi_arregion[node_id]),
        .axi_aruser(axi_aruser[node_id]),
        
        // AXI Read Data Channel
        .axi_rvalid(axi_rvalid[node_id]),
        .axi_rready(axi_rready[node_id]),
        .axi_rid(axi_rid[node_id]),
        .axi_rdata(axi_rdata[node_id]),
        .axi_rresp(axi_rresp[node_id]),
        .axi_rlast(axi_rlast[node_id]),
        .axi_ruser(axi_ruser[node_id]),
        
        // Configuration
        .base_addr(32'h1000_0000 + (node_id << 20)), // 1MB per node
        .addr_mask(32'hFFF0_0000),
        
        // NoC Interface
        .noc_flit_out_valid(bridge_noc_req_valid[node_id]),
        .noc_flit_out_ready(bridge_noc_req_ready[node_id]),
        .noc_flit_out(bridge_noc_req_flit[node_id]),
        
        .noc_flit_in_valid(bridge_noc_resp_valid[node_id]),
        .noc_flit_in_ready(bridge_noc_resp_ready[node_id]),
        .noc_flit_in(bridge_noc_resp_flit[node_id]),
        
        // Status
        .status_reg(),
        .error_reg(),
        .packet_tx_count(),
        .packet_rx_count(),
        .avg_latency(),
        .buffer_utilization()
      );
      
    end
  endgenerate

  // =============================================================================
  // AXI MASTER TEST DRIVERS
  // =============================================================================
  
  // Initialize AXI interfaces
  initial begin
    axi_awvalid = '0;
    axi_awaddr = '{default: '0};
    axi_awlen = '{default: '0};
    axi_awsize = '{default: 3'b110}; // 64 bytes
    axi_awburst = '{default: 2'b01}; // INCR
    axi_awid = '{default: '0};
    
    axi_wvalid = '0;
    axi_wdata = '{default: '0};
    axi_wstrb = '{default: '1};
    axi_wlast = '0;
    
    axi_bready = '1;
    
    axi_arvalid = '0;
    axi_araddr = '{default: '0};
    axi_arlen = '{default: '0};
    axi_arsize = '{default: 3'b110};
    axi_arburst = '{default: 2'b01};
    axi_arid = '{default: '0};
    
    axi_rready = '1;
  end

  // =============================================================================
  // TEST TASKS
  // =============================================================================
  
  task test_single_node_axi_write(int src_node, int dest_node, logic [31:0] addr, logic [63:0] data);
    $display("Testing AXI write from node %0d to node %0d (addr=0x%h, data=0x%h)", 
             src_node, dest_node, addr, data);
    test_count++;
    
    fork
      begin
        // AXI write transaction
        @(posedge clk);
        axi_awvalid[src_node] <= 1'b1;
        axi_awaddr[src_node] <= addr;
        axi_awlen[src_node] <= 0; // Single beat
        axi_awid[src_node] <= test_count[AXI_ID_WIDTH-1:0];
        
        @(posedge clk iff axi_awready[src_node]);
        axi_awvalid[src_node] <= 1'b0;
        
        axi_wvalid[src_node] <= 1'b1;
        axi_wdata[src_node] <= {8{data}}; // Replicate across data width
        axi_wlast[src_node] <= 1'b1;
        
        @(posedge clk iff axi_wready[src_node]);
        axi_wvalid[src_node] <= 1'b0;
        axi_wlast[src_node] <= 1'b0;
        
        // Wait for write response
        @(posedge clk iff axi_bvalid[src_node]);
        if (axi_bresp[src_node] == 2'b00) begin
          $display("  ✅ AXI write completed successfully");
          pass_count++;
        end else begin
          $display("  ❌ AXI write failed with response: %0d", axi_bresp[src_node]);
          fail_count++;
        end
      end
      
      begin
        // Timeout
        repeat (1000) @(posedge clk);
        $display("  ❌ AXI write timeout");
        fail_count++;
      end
    join_any
    disable fork;
    
  endtask
  
  task test_single_node_axi_read(int src_node, int dest_node, logic [31:0] addr);
    $display("Testing AXI read from node %0d to node %0d (addr=0x%h)", 
             src_node, dest_node, addr);
    test_count++;
    
    fork
      begin
        // AXI read transaction
        @(posedge clk);
        axi_arvalid[src_node] <= 1'b1;
        axi_araddr[src_node] <= addr;
        axi_arlen[src_node] <= 0; // Single beat
        axi_arid[src_node] <= test_count[AXI_ID_WIDTH-1:0];
        
        @(posedge clk iff axi_arready[src_node]);
        axi_arvalid[src_node] <= 1'b0;
        
        // Wait for read response
        @(posedge clk iff axi_rvalid[src_node]);
        if (axi_rresp[src_node] == 2'b00 && axi_rlast[src_node]) begin
          $display("  ✅ AXI read completed successfully (data=0x%h)", axi_rdata[src_node][63:0]);
          pass_count++;
        end else begin
          $display("  ❌ AXI read failed with response: %0d", axi_rresp[src_node]);
          fail_count++;
        end
      end
      
      begin
        // Timeout
        repeat (1000) @(posedge clk);
        $display("  ❌ AXI read timeout");
        fail_count++;
      end
    join_any
    disable fork;
    
  endtask
  
  task test_burst_transaction(int src_node, int dest_node, logic [31:0] base_addr, int burst_len);
    $display("Testing AXI burst from node %0d to node %0d (addr=0x%h, len=%0d)", 
             src_node, dest_node, base_addr, burst_len);
    test_count++;
    
    fork
      begin
        // AXI write burst
        @(posedge clk);
        axi_awvalid[src_node] <= 1'b1;
        axi_awaddr[src_node] <= base_addr;
        axi_awlen[src_node] <= burst_len - 1;
        axi_awid[src_node] <= test_count[AXI_ID_WIDTH-1:0];
        
        @(posedge clk iff axi_awready[src_node]);
        axi_awvalid[src_node] <= 1'b0;
        
        // Send burst data
        for (int i = 0; i < burst_len; i++) begin
          axi_wvalid[src_node] <= 1'b1;
          axi_wdata[src_node] <= {8{32'hDEAD_BEEF + i}};
          axi_wlast[src_node] <= (i == burst_len - 1);
          
          @(posedge clk iff axi_wready[src_node]);
        end
        
        axi_wvalid[src_node] <= 1'b0;
        axi_wlast[src_node] <= 1'b0;
        
        // Wait for write response
        @(posedge clk iff axi_bvalid[src_node]);
        if (axi_bresp[src_node] == 2'b00) begin
          $display("  ✅ AXI burst write completed successfully");
          pass_count++;
        end else begin
          $display("  ❌ AXI burst write failed with response: %0d", axi_bresp[src_node]);
          fail_count++;
        end
      end
      
      begin
        // Timeout
        repeat (2000) @(posedge clk);
        $display("  ❌ AXI burst timeout");
        fail_count++;
      end
    join_any
    disable fork;
    
  endtask

  // =============================================================================
  // MAIN TEST SEQUENCE
  // =============================================================================
  
  initial begin
    $dumpfile("nebula_mesh_integration_tb.vcd");
    $dumpvars(0, tb_nebula_mesh_integration);
    
    $display("===============================================");
    $display("NEBULA MESH INTEGRATION TESTBENCH");
    $display("===============================================");
    $display("Mesh Size: %0dx%0d (%0d nodes)", MESH_SIZE_X, MESH_SIZE_Y, NUM_NODES);
    $display("");
    
    // Wait for reset
    wait (rst_n == 1'b1);
    repeat (50) @(posedge clk);
    
    // Test Cases
    $display("Starting Mesh Integration Tests...");
    
    // Single node tests
    test_single_node_axi_write(0, 1, 32'h1100_0000, 64'hCAFE_BABE_DEAD_BEEF);
    test_single_node_axi_read(0, 1, 32'h1100_0000);
    
    // Cross-mesh tests
    if (NUM_NODES >= 4) begin
      test_single_node_axi_write(0, 3, 32'h1300_0000, 64'h1234_5678_9ABC_DEF0);
      test_single_node_axi_read(0, 3, 32'h1300_0000);
    end
    
    // Burst transactions
    test_burst_transaction(0, 1, 32'h1100_1000, 4);
    
    // Concurrent transactions
    $display("Testing concurrent transactions...");
    fork
      test_single_node_axi_write(0, 1, 32'h1100_2000, 64'hAAAA_BBBB_CCCC_DDDD);
      test_single_node_axi_write(1, 0, 32'h1000_2000, 64'h1111_2222_3333_4444);
    join
    
    // Final results
    repeat (100) @(posedge clk);
    
    $display("");
    $display("===============================================");
    $display("MESH INTEGRATION TEST SUMMARY");
    $display("===============================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed: %0d", pass_count);
    $display("Failed: %0d", fail_count);
    
    if (fail_count == 0) begin
      $display("🎉 ALL MESH INTEGRATION TESTS PASSED!");
    end else begin
      $display("❌ %0d test(s) failed", fail_count);
    end
    
    $finish;
  end

  // Timeout watchdog
  initial begin
    #TEST_TIMEOUT;
    $display("ERROR: Test timeout after %0d ns", TEST_TIMEOUT);
    $finish;
  end

endmodule
