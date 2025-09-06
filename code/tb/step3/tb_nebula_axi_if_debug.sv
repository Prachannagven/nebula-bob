`timescale 1ns / 1ps

module tb_nebula_axi_if_debug;

  import nebula_pkg::*;

  parameter CLK_PERIOD = 10;
  parameter TIMEOUT_CYCLES = 1000;
  
  // DUT Interface signals
  logic clk;
  logic rst_n;
  
  // AXI Write Address Channel
  logic [AXI_ID_WIDTH-1:0]     axi_awid;
  logic [AXI_ADDR_WIDTH-1:0]   axi_awaddr;
  logic [7:0]                  axi_awlen;
  logic [2:0]                  axi_awsize;
  logic [1:0]                  axi_awburst;
  logic                        axi_awlock;
  logic [3:0]                  axi_awcache;
  logic [2:0]                  axi_awprot;
  logic [3:0]                  axi_awqos;
  logic [3:0]                  axi_awregion;
  logic [AXI_AWUSER_WIDTH-1:0] axi_awuser;
  logic                        axi_awvalid;
  logic                        axi_awready;

  // AXI Write Data Channel
  logic [AXI_DATA_WIDTH-1:0]   axi_wdata;
  logic [AXI_STRB_WIDTH-1:0]   axi_wstrb;
  logic                        axi_wlast;
  logic [AXI_WUSER_WIDTH-1:0]  axi_wuser;
  logic                        axi_wvalid;
  logic                        axi_wready;

  // AXI Write Response Channel
  logic [AXI_ID_WIDTH-1:0]     axi_bid;
  logic [1:0]                  axi_bresp;
  logic [AXI_BUSER_WIDTH-1:0]  axi_buser;
  logic                        axi_bvalid;
  logic                        axi_bready;

  // NoC interface signals
  logic                        noc_req_valid;
  logic                        noc_req_ready;
  noc_flit_t                   noc_req_flit;
  
  logic                        noc_resp_valid;
  logic                        noc_resp_ready;
  noc_flit_t                   noc_resp_flit;

  // Debug counters
  int cycle_count = 0;

  // Clock generation
  initial begin
    clk = 0;
    forever #(CLK_PERIOD/2) clk = ~clk;
  end

  // Cycle counter
  always_ff @(posedge clk) begin
    cycle_count <= cycle_count + 1;
  end

  // DUT instantiation
  nebula_axi_if dut (
    .clk(clk),
    .rst_n(rst_n),
    
    // AXI interface
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
    .axi_awvalid(axi_awvalid),
    .axi_awready(axi_awready),
    
    .axi_wdata(axi_wdata),
    .axi_wstrb(axi_wstrb),
    .axi_wlast(axi_wlast),
    .axi_wuser(axi_wuser),
    .axi_wvalid(axi_wvalid),
    .axi_wready(axi_wready),
    
    .axi_bid(axi_bid),
    .axi_bresp(axi_bresp),
    .axi_buser(axi_buser),
    .axi_bvalid(axi_bvalid),
    .axi_bready(axi_bready),
    
    .axi_arid('0),      // Unused for debug
    .axi_araddr('0),    // Unused for debug
    .axi_arlen('0),     // Unused for debug
    .axi_arsize('0),    // Unused for debug
    .axi_arburst('0),   // Unused for debug
    .axi_arlock('0),    // Unused for debug
    .axi_arcache('0),   // Unused for debug
    .axi_arprot('0),    // Unused for debug
    .axi_arqos('0),     // Unused for debug
    .axi_arregion('0),  // Unused for debug
    .axi_aruser('0),    // Unused for debug
    .axi_arvalid(1'b0), // Unused for debug
    .axi_arready(),     // Unused for debug
    
    .axi_rid(),         // Unused for debug
    .axi_rdata(),       // Unused for debug
    .axi_rresp(),       // Unused for debug
    .axi_rlast(),       // Unused for debug
    .axi_ruser(),       // Unused for debug
    .axi_rvalid(),      // Unused for debug
    .axi_rready(1'b0),  // Unused for debug
    
    // NoC interface
    .noc_req_valid(noc_req_valid),
    .noc_req_ready(noc_req_ready),
    .noc_req_flit(noc_req_flit),
    .noc_resp_valid(noc_resp_valid),
    .noc_resp_ready(noc_resp_ready),
    .noc_resp_flit(noc_resp_flit),
    
    .outstanding_count(),
    .error_status(),
    .perf_read_count(),
    .perf_write_count()
  );

  // Simple NoC mock - always ready, responds after 2 cycles
  logic [1:0] resp_delay;
  noc_flit_t pending_req;
  logic req_captured = 1'b0;
  
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      noc_req_ready <= 1'b1;
      noc_resp_valid <= 1'b0;
      noc_resp_flit <= '0;
      resp_delay <= 0;
      pending_req <= '0;
      req_captured <= 1'b0;
    end else begin
      // Capture request
      if (noc_req_valid && noc_req_ready && !req_captured) begin
        pending_req <= noc_req_flit;
        req_captured <= 1'b1;
        resp_delay <= 2;
        $display("NoC: Captured request at cycle %0d", cycle_count);
      end
      
      // Count down and respond
      if (req_captured) begin
        if (resp_delay > 0) begin
          resp_delay <= resp_delay - 1;
        end else begin
          noc_resp_valid <= 1'b1;
          noc_resp_flit <= pending_req; // Echo back
          noc_resp_flit.payload <= {AXI_DATA_WIDTH{1'b1}}; // Dummy data
          $display("NoC: Sending response at cycle %0d", cycle_count);
        end
      end
      
      // Clear response after ready handshake (separate from sending logic)
      if (noc_resp_valid && noc_resp_ready) begin
        noc_resp_valid <= 1'b0;
        req_captured <= 1'b0;
        $display("NoC: Response acknowledged at cycle %0d", cycle_count);
      end
    end
  end

  // Test stimulus
  initial begin
    // Initialize
    rst_n = 0;
    axi_awvalid = 0;
    axi_awid = 0;
    axi_awaddr = 0;
    axi_awlen = 0;
    axi_awsize = 0;
    axi_awburst = 0;
    axi_awlock = 0;
    axi_awcache = 0;
    axi_awprot = 0;
    axi_awqos = 0;
    axi_awregion = 0;
    axi_awuser = 0;
    
    axi_wvalid = 0;
    axi_wdata = 0;
    axi_wstrb = 0;
    axi_wlast = 0;
    axi_wuser = 0;
    
    axi_bready = 1; // Always ready to accept write responses
    noc_resp_ready = 1; // Always ready to accept NoC responses
    
    repeat(10) @(posedge clk);
    rst_n = 1;
    $display("Debug: Reset released at cycle %0d", cycle_count);
    repeat(5) @(posedge clk);
    
    // Simple write transaction
    $display("Debug: Starting write transaction at cycle %0d", cycle_count);
    axi_awvalid = 1;
    axi_awid = 8'h01;
    axi_awaddr = 64'h1000;
    axi_awlen = 8'h00; // Single beat
    axi_awsize = 3'b110; // 64 bytes
    axi_awburst = AXI_BURST_INCR;
    axi_awqos = QOS_NORMAL;
    
    // Wait for address acceptance
    wait(axi_awready);
    @(posedge clk);
    $display("Debug: Address accepted at cycle %0d", cycle_count);
    axi_awvalid = 0;
    
    // Send data
    axi_wvalid = 1;
    axi_wdata = {AXI_DATA_WIDTH{1'b1}}; // All 1s for easy debugging
    axi_wstrb = {AXI_STRB_WIDTH{1'b1}}; // All bytes valid
    axi_wlast = 1;
    
    // Keep signals active until write response is received
    // This allows W state machine to properly transition from W_DATA to W_WAIT_LAST
    $display("Debug: Data sent, waiting for write response at cycle %0d", cycle_count);
    
    // Monitor state for a few cycles while waiting
    repeat(15) @(posedge clk) begin
      $display("Debug: Cycle %0d - aw_state=%0d, w_state=%0d, b_state=%0d", 
               cycle_count, dut.aw_state, dut.w_state, dut.b_state);
      $display("  AW condition (w_state == W_WAIT_LAST): %0d == 2 = %0b", dut.w_state, (dut.w_state == 2));
      $display("  W condition (aw_state == AW_SEND_REQ && noc_req_ready): %0d == 2 && %0b = %0b", dut.aw_state, noc_req_ready, (dut.aw_state == 2 && noc_req_ready));
      $display("  W transition condition (axi_wvalid && axi_wlast): %0b && %0b = %0b", axi_wvalid, axi_wlast, (axi_wvalid && axi_wlast));
      $display("  axi_wready=%0b, axi_wvalid=%0b, axi_wlast=%0b", axi_wready, axi_wvalid, axi_wlast);
      $display("  noc_req_valid = %0b, int_req_valid = %0b", noc_req_valid, dut.int_req_valid);
      
      // Always show NoC response status
      $display("  noc_resp_valid = %0b, noc_resp_ready = %0b", noc_resp_valid, noc_resp_ready);
      
      // Debug outstanding table and lookup when NoC response is present
      if (noc_resp_valid) begin
        $display("  Outstanding table lookup: packet_id=%0d, lookup_valid=%0d, lookup_idx=%0d",
                 noc_resp_flit.packet_id, dut.lookup_valid, dut.lookup_idx);
        for (int i = 0; i < 4; i++) begin
          if (dut.outstanding_table[i].valid) begin
            $display("    Entry[%0d]: valid=%0d, packet_id=%0d, axi_id=%0d, is_write=%0d",
                     i, dut.outstanding_table[i].valid, dut.outstanding_table[i].packet_id,
                     dut.outstanding_table[i].axi_id, dut.outstanding_table[i].is_write);
          end
        end
        if (dut.lookup_valid) begin
          $display("  B state condition: lookup_valid=%0d && noc_resp_valid=%0d && is_write=%0d = %0d",
                   dut.lookup_valid, noc_resp_valid, 
                   dut.outstanding_table[dut.lookup_idx].is_write,
                   dut.lookup_valid && noc_resp_valid && dut.outstanding_table[dut.lookup_idx].is_write);
        end
      end
      
      if (axi_bvalid) begin
        $display("  axi_bvalid detected! Breaking monitoring loop.");
        break;
      end
    end
    
    wait(axi_bvalid);
    @(posedge clk);
    $display("Debug: Write response received, clearing data signals at cycle %0d", cycle_count);
    axi_wvalid = 0;
    axi_wlast = 0;
    
    // Monitor state for a few cycles
    repeat(10) @(posedge clk) begin
      $display("Debug: Cycle %0d - aw_state=%0d, w_state=%0d, b_state=%0d", 
               cycle_count, dut.aw_state, dut.w_state, dut.b_state);
      $display("  AW condition (w_state == W_WAIT_LAST): %0d == 2 = %0b", dut.w_state, (dut.w_state == 2));
      $display("  W condition (aw_state == AW_SEND_REQ && noc_req_ready): %0d == 2 && %0b = %0b", dut.aw_state, noc_req_ready, (dut.aw_state == 2 && noc_req_ready));
      $display("  W transition condition (axi_wvalid && axi_wlast): %0b && %0b = %0b", axi_wvalid, axi_wlast, (axi_wvalid && axi_wlast));
      $display("  axi_wready=%0b, axi_wvalid=%0b, axi_wlast=%0b", axi_wready, axi_wvalid, axi_wlast);
      $display("  noc_req_valid = %0b, int_req_valid = %0b", noc_req_valid, dut.int_req_valid);
    end
    
    // Wait for write response
    $display("Debug: Waiting for write response at cycle %0d", cycle_count);
    wait(axi_bvalid);
    @(posedge clk);
    $display("Debug: Write response received at cycle %0d, ID=%0h, RESP=%0h", cycle_count, axi_bid, axi_bresp);
    
    repeat(10) @(posedge clk);
    $display("SUCCESS: Basic write transaction completed!");
    $finish;
  end

  // Timeout
  initial begin
    repeat(TIMEOUT_CYCLES) @(posedge clk);
    $display("ERROR: Test timeout at cycle %0d", cycle_count);
    $display("  axi_awready = %0b", axi_awready);
    $display("  axi_wready = %0b", axi_wready);
    $display("  axi_bvalid = %0b", axi_bvalid);
    $display("  noc_req_valid = %0b", noc_req_valid);
    $display("  noc_req_ready = %0b", noc_req_ready);
    $display("  noc_resp_valid = %0b", noc_resp_valid);
    $display("  noc_resp_ready = %0b", noc_resp_ready);
    $finish;
  end

endmodule
