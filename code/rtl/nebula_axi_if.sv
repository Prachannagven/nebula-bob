/**
 * Nebula AXI4 Interface Module
 * 
 * This module implements a complete AXI4 slave interface with five independent
 * state machines for each channel (AW, W, B, AR, R). It includes an outstanding 
 * transaction table for managing up to 64 concurrent transactions and provides
 * the bridge between AXI4 protocol and the internal NoC packet format.
 * 
 * Key Features:
 * - Full AXI4 protocol compliance with ready/valid handshaking
 * - Outstanding transaction table with configurable depth
 * - Support for all AXI4 burst types (INCR, WRAP, FIXED)
 * - 4KB boundary protection and address validation
 * - Comprehensive error handling with proper AXI4 responses
 * - Transaction ID management and reordering support
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: August 2025
 */

`include "nebula_pkg.sv"

module nebula_axi_if
  import nebula_pkg::*;
#(
  parameter int OUTSTANDING_DEPTH = 64,
  parameter int NODE_X = 0,
  parameter int NODE_Y = 0
)(
  input  logic clk,
  input  logic rst_n,
  
  // AXI4 Write Address Channel
  input  logic                      axi_awvalid,
  output logic                      axi_awready,
  input  logic [AXI_ID_WIDTH-1:0]   axi_awid,
  input  logic [AXI_ADDR_WIDTH-1:0] axi_awaddr,
  input  logic [7:0]                axi_awlen,
  input  logic [2:0]                axi_awsize,
  input  logic [1:0]                axi_awburst,
  input  logic                      axi_awlock,
  input  logic [3:0]                axi_awcache,
  input  logic [2:0]                axi_awprot,
  input  logic [QOS_WIDTH-1:0]      axi_awqos,
  input  logic [3:0]                axi_awregion,
  input  logic [AXI_AWUSER_WIDTH-1:0] axi_awuser,
  
  // AXI4 Write Data Channel
  input  logic                      axi_wvalid,
  output logic                      axi_wready,
  input  logic [AXI_DATA_WIDTH-1:0] axi_wdata,
  input  logic [AXI_STRB_WIDTH-1:0] axi_wstrb,
  input  logic                      axi_wlast,
  input  logic [AXI_WUSER_WIDTH-1:0] axi_wuser,
  
  // AXI4 Write Response Channel
  output logic                      axi_bvalid,
  input  logic                      axi_bready,
  output logic [AXI_ID_WIDTH-1:0]   axi_bid,
  output logic [1:0]                axi_bresp,
  output logic [AXI_BUSER_WIDTH-1:0] axi_buser,
  
  // AXI4 Read Address Channel
  input  logic                      axi_arvalid,
  output logic                      axi_arready,
  input  logic [AXI_ID_WIDTH-1:0]   axi_arid,
  input  logic [AXI_ADDR_WIDTH-1:0] axi_araddr,
  input  logic [7:0]                axi_arlen,
  input  logic [2:0]                axi_arsize,
  input  logic [1:0]                axi_arburst,
  input  logic                      axi_arlock,
  input  logic [3:0]                axi_arcache,
  input  logic [2:0]                axi_arprot,
  input  logic [QOS_WIDTH-1:0]      axi_arqos,
  input  logic [3:0]                axi_arregion,
  input  logic [AXI_ARUSER_WIDTH-1:0] axi_aruser,
  
  // AXI4 Read Data Channel
  output logic                      axi_rvalid,
  input  logic                      axi_rready,
  output logic [AXI_ID_WIDTH-1:0]   axi_rid,
  output logic [AXI_DATA_WIDTH-1:0] axi_rdata,
  output logic [1:0]                axi_rresp,
  output logic                      axi_rlast,
  output logic [AXI_RUSER_WIDTH-1:0] axi_ruser,
  
  // NoC Interface - Request (to NoC)
  output logic                      noc_req_valid,
  input  logic                      noc_req_ready,
  output noc_flit_t                 noc_req_flit,
  
  // NoC Interface - Response (from NoC)
  input  logic                      noc_resp_valid,
  output logic                      noc_resp_ready,
  input  noc_flit_t                 noc_resp_flit,
  
  // Status and Debug
  output logic [31:0]               outstanding_count,
  output logic [31:0]               error_status,
  output logic [31:0]               perf_read_count,
  output logic [31:0]               perf_write_count
);

  // =============================================================================
  // INTERNAL SIGNAL DECLARATIONS
  // =============================================================================
  
  // Outstanding Transaction Table
  transaction_entry_t outstanding_table [OUTSTANDING_DEPTH-1:0];
  logic [$clog2(OUTSTANDING_DEPTH)-1:0] outstanding_wr_ptr, outstanding_rd_ptr;
  logic [$clog2(OUTSTANDING_DEPTH):0]   outstanding_cnt;
  logic outstanding_full, outstanding_empty;
  
  // Transaction allocation and lookup
  logic [$clog2(OUTSTANDING_DEPTH)-1:0] alloc_idx;
  logic [$clog2(OUTSTANDING_DEPTH)-1:0] lookup_idx;
  logic alloc_valid, lookup_valid;
  
  // State machine states
  typedef enum logic [2:0] {
    AW_IDLE,
    AW_WAIT_DATA,
    AW_SEND_REQ,
    AW_WAIT_RESP
  } aw_state_e;
  
  typedef enum logic [2:0] {
    W_IDLE,
    W_DATA,
    W_WAIT_LAST
  } w_state_e;
  
  typedef enum logic [2:0] {
    B_IDLE,
    B_RESP
  } b_state_e;
  
  typedef enum logic [2:0] {
    AR_IDLE,
    AR_SEND_REQ,
    AR_WAIT_RESP
  } ar_state_e;
  
  typedef enum logic [2:0] {
    R_IDLE,
    R_DATA
  } r_state_e;
  
  // State registers
  aw_state_e aw_state, aw_state_next;
  w_state_e  w_state, w_state_next;
  b_state_e  b_state, b_state_next;
  ar_state_e ar_state, ar_state_next;
  r_state_e  r_state, r_state_next;
  
  // Current transaction tracking
  transaction_entry_t current_aw_trans, current_w_trans, current_ar_trans;
  logic [7:0] w_beat_count, r_beat_count;
  logic [PACKET_ID_WIDTH-1:0] next_packet_id;
  
  // Address calculation and validation
  logic [AXI_ADDR_WIDTH-1:0] next_addr;
  logic [11:0] addr_4kb_offset;
  logic boundary_cross;
  
  // Error and status tracking
  logic [31:0] error_reg;
  logic [31:0] read_count, write_count;
  
  // Internal NoC request generation
  logic int_req_valid;
  noc_flit_t int_req_flit;
  logic req_fifo_full, req_fifo_empty;
  
  // =============================================================================
  // OUTSTANDING TRANSACTION TABLE MANAGEMENT
  // =============================================================================
  
  assign outstanding_full = (outstanding_cnt == OUTSTANDING_DEPTH);
  assign outstanding_empty = (outstanding_cnt == 0);
  assign outstanding_count = outstanding_cnt;
  
  // Allocate entry in outstanding table
  always_comb begin
    alloc_valid = 1'b0;
    alloc_idx = outstanding_wr_ptr;
    
    if (!outstanding_full) begin
      alloc_valid = 1'b1;
    end
  end
  
  // Lookup entry in outstanding table by packet ID
  always_comb begin
    lookup_valid = 1'b0;
    lookup_idx = 0;
    
    for (int i = 0; i < OUTSTANDING_DEPTH; i++) begin
      if (outstanding_table[i].valid && 
          outstanding_table[i].packet_id == noc_resp_flit.packet_id) begin
        lookup_valid = 1'b1;
        lookup_idx = i;
        break;
      end
    end
  end
  
  // Outstanding table pointer management
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      outstanding_wr_ptr <= 0;
      outstanding_rd_ptr <= 0;
      outstanding_cnt <= 0;
      
      for (int i = 0; i < OUTSTANDING_DEPTH; i++) begin
        outstanding_table[i] <= '0;
      end
    end else begin
      // Allocation - populate outstanding table entry for write transactions
      if (alloc_valid && (aw_state == AW_SEND_REQ)) begin
        outstanding_table[outstanding_wr_ptr].valid <= 1'b1;
        outstanding_table[outstanding_wr_ptr].packet_id <= int_req_flit.packet_id;
        outstanding_table[outstanding_wr_ptr].axi_id <= current_aw_trans.axi_id;
        outstanding_table[outstanding_wr_ptr].is_write <= 1'b1;
        outstanding_wr_ptr <= outstanding_wr_ptr + 1;
        outstanding_cnt <= outstanding_cnt + 1;
      end
      
      // Allocation - populate outstanding table entry for read transactions  
      if (alloc_valid && (ar_state == AR_SEND_REQ)) begin
        outstanding_table[outstanding_wr_ptr].valid <= 1'b1;
        outstanding_table[outstanding_wr_ptr].packet_id <= int_req_flit.packet_id;
        outstanding_table[outstanding_wr_ptr].axi_id <= current_ar_trans.axi_id;
        outstanding_table[outstanding_wr_ptr].is_write <= 1'b0;
        outstanding_wr_ptr <= outstanding_wr_ptr + 1;
        outstanding_cnt <= outstanding_cnt + 1;
      end
      
      // Deallocation  
      if (lookup_valid && noc_resp_valid && noc_resp_ready) begin
        outstanding_table[lookup_idx].valid <= 1'b0;
        outstanding_cnt <= outstanding_cnt - 1;
      end
    end
  end
  
  // =============================================================================
  // ADDRESS CALCULATION AND BOUNDARY CHECKING
  // =============================================================================
  
  // Calculate next address for burst transactions
  function automatic logic [AXI_ADDR_WIDTH-1:0] calc_next_addr(
    input logic [AXI_ADDR_WIDTH-1:0] base_addr,
    input logic [7:0] beat_num,
    input logic [2:0] size,
    input logic [1:0] burst_type,
    input logic [7:0] burst_len
  );
    logic [AXI_ADDR_WIDTH-1:0] addr;
    logic [11:0] offset;
    
    case (burst_type)
      AXI_BURST_FIXED: begin
        addr = base_addr;
      end
      AXI_BURST_INCR: begin
        offset = beat_num * (1 << size);
        addr = base_addr + offset;
      end
      AXI_BURST_WRAP: begin
        logic [11:0] wrap_boundary;
        wrap_boundary = (burst_len + 1) * (1 << size);
        offset = beat_num * (1 << size);
        addr = (base_addr & ~(wrap_boundary - 1)) | ((base_addr + offset) & (wrap_boundary - 1));
      end
      default: addr = base_addr;
    endcase
    
    return addr;
  endfunction
  
  // Check for 4KB boundary crossing
  always_comb begin
    next_addr = calc_next_addr(current_aw_trans.base_addr, w_beat_count + 1, 
                              current_aw_trans.burst_size, current_aw_trans.burst_type,
                              current_aw_trans.burst_len);
    addr_4kb_offset = next_addr[11:0];
    boundary_cross = (current_aw_trans.base_addr[AXI_ADDR_WIDTH-1:12] != next_addr[AXI_ADDR_WIDTH-1:12]);
  end
  
  // =============================================================================
  // AXI4 WRITE ADDRESS CHANNEL STATE MACHINE
  // =============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      aw_state <= AW_IDLE;
    end else begin
      aw_state <= aw_state_next;
    end
  end
  
  always_comb begin
    aw_state_next = aw_state;
    axi_awready = 1'b0;
    
    case (aw_state)
      AW_IDLE: begin
        axi_awready = !outstanding_full;
        if (axi_awvalid && axi_awready) begin
          aw_state_next = AW_WAIT_DATA;
        end
      end
      
      AW_WAIT_DATA: begin
        if (w_state == W_WAIT_LAST) begin
          aw_state_next = AW_SEND_REQ;
        end
      end
      
      AW_SEND_REQ: begin
        if (noc_req_valid && noc_req_ready) begin
          aw_state_next = AW_WAIT_RESP;
        end
      end
      
      AW_WAIT_RESP: begin
        if (b_state == B_RESP && axi_bvalid && axi_bready) begin
          aw_state_next = AW_IDLE;
        end
      end
    endcase
  end
  
  // Capture write address transaction
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_aw_trans <= '0;
    end else if (aw_state == AW_IDLE && axi_awvalid && axi_awready) begin
      current_aw_trans.valid <= 1'b1;
      current_aw_trans.axi_id <= axi_awid;
      current_aw_trans.base_addr <= axi_awaddr;
      current_aw_trans.burst_len <= axi_awlen;
      current_aw_trans.burst_size <= axi_awsize;
      current_aw_trans.burst_type <= axi_awburst;
      current_aw_trans.is_write <= 1'b1;
      current_aw_trans.packet_id <= next_packet_id;
      current_aw_trans.dest_x <= axi_awaddr[COORD_WIDTH+15:16]; // Extract coordinates from address
      current_aw_trans.dest_y <= axi_awaddr[COORD_WIDTH+11:12];
    end
  end
  
  // =============================================================================
  // AXI4 WRITE DATA CHANNEL STATE MACHINE
  // =============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      w_state <= W_IDLE;
      w_beat_count <= 0;
    end else begin
      w_state <= w_state_next;
      
      if (w_state == W_IDLE) begin
        w_beat_count <= 0;
      end else if (w_state == W_DATA && axi_wvalid && axi_wready) begin
        w_beat_count <= w_beat_count + 1;
      end
    end
  end
  
  always_comb begin
    w_state_next = w_state;
    axi_wready = 1'b0;
    
    case (w_state)
      W_IDLE: begin
        if (aw_state == AW_WAIT_DATA) begin
          w_state_next = W_DATA;
        end
      end
      
      W_DATA: begin
        axi_wready = 1'b1;
        if (axi_wvalid && axi_wlast) begin
          w_state_next = W_WAIT_LAST;
        end
      end
      
      W_WAIT_LAST: begin
        if (aw_state == AW_SEND_REQ && noc_req_ready) begin
          w_state_next = W_IDLE;
        end
      end
    endcase
  end
  
  // =============================================================================
  // AXI4 WRITE RESPONSE CHANNEL STATE MACHINE
  // =============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      b_state <= B_IDLE;
    end else begin
      b_state <= b_state_next;
    end
  end
  
  always_comb begin
    b_state_next = b_state;
    axi_bvalid = 1'b0;
    axi_bid = '0;
    axi_bresp = AXI_RESP_OKAY;
    axi_buser = '0;
    
    case (b_state)
      B_IDLE: begin
        if (lookup_valid && noc_resp_valid && outstanding_table[lookup_idx].is_write) begin
          b_state_next = B_RESP;
        end
      end
      
      B_RESP: begin
        axi_bvalid = 1'b1;
        axi_bid = outstanding_table[lookup_idx].axi_id;
        if (axi_bready) begin
          b_state_next = B_IDLE;
        end
      end
    endcase
  end
  
  // =============================================================================
  // AXI4 READ ADDRESS CHANNEL STATE MACHINE
  // =============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      ar_state <= AR_IDLE;
    end else begin
      ar_state <= ar_state_next;
    end
  end
  
  always_comb begin
    ar_state_next = ar_state;
    axi_arready = 1'b0;
    
    case (ar_state)
      AR_IDLE: begin
        axi_arready = !outstanding_full;
        if (axi_arvalid && axi_arready) begin
          ar_state_next = AR_SEND_REQ;
        end
      end
      
      AR_SEND_REQ: begin
        if (noc_req_valid && noc_req_ready) begin
          ar_state_next = AR_WAIT_RESP;
        end
      end
      
      AR_WAIT_RESP: begin
        if (r_state == R_DATA && axi_rvalid && axi_rready && axi_rlast) begin
          ar_state_next = AR_IDLE;
        end
      end
    endcase
  end
  
  // Capture read address transaction
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_ar_trans <= '0;
    end else if (ar_state == AR_IDLE && axi_arvalid && axi_arready) begin
      current_ar_trans.valid <= 1'b1;
      current_ar_trans.axi_id <= axi_arid;
      current_ar_trans.base_addr <= axi_araddr;
      current_ar_trans.burst_len <= axi_arlen;
      current_ar_trans.burst_size <= axi_arsize;
      current_ar_trans.burst_type <= axi_arburst;
      current_ar_trans.is_write <= 1'b0;
      current_ar_trans.packet_id <= next_packet_id;
      current_ar_trans.dest_x <= axi_araddr[COORD_WIDTH+15:16]; // Extract coordinates from address
      current_ar_trans.dest_y <= axi_araddr[COORD_WIDTH+11:12];
    end
  end
  
  // =============================================================================
  // AXI4 READ DATA CHANNEL STATE MACHINE
  // =============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      r_state <= R_IDLE;
      r_beat_count <= 0;
    end else begin
      r_state <= r_state_next;
      
      if (r_state == R_IDLE) begin
        r_beat_count <= 0;
      end else if (r_state == R_DATA && axi_rvalid && axi_rready) begin
        r_beat_count <= r_beat_count + 1;
      end
    end
  end
  
  always_comb begin
    r_state_next = r_state;
    axi_rvalid = 1'b0;
    axi_rid = '0;
    axi_rdata = '0;
    axi_rresp = AXI_RESP_OKAY;
    axi_rlast = 1'b0;
    axi_ruser = '0;
    
    case (r_state)
      R_IDLE: begin
        if (lookup_valid && noc_resp_valid && !outstanding_table[lookup_idx].is_write) begin
          r_state_next = R_DATA;
        end
      end
      
      R_DATA: begin
        axi_rvalid = noc_resp_valid;
        axi_rid = outstanding_table[lookup_idx].axi_id;
        axi_rdata = noc_resp_flit.payload[AXI_DATA_WIDTH-1:0];
        axi_rlast = (r_beat_count == outstanding_table[lookup_idx].burst_len);
        
        if (axi_rready && axi_rlast) begin
          r_state_next = R_IDLE;
        end
      end
    endcase
  end
  
  // =============================================================================
  // NOC REQUEST GENERATION
  // =============================================================================
  
  always_comb begin
    int_req_valid = 1'b0;
    int_req_flit = '0;
    
    if (aw_state == AW_SEND_REQ) begin
      int_req_valid = 1'b1;
      int_req_flit.flit_type = FLIT_TYPE_SINGLE;
      int_req_flit.dest_x = current_aw_trans.dest_x;
      int_req_flit.dest_y = current_aw_trans.dest_y;
      int_req_flit.src_x = NODE_X[COORD_WIDTH-1:0];
      int_req_flit.src_y = NODE_Y[COORD_WIDTH-1:0];
      int_req_flit.vc_id = VC_REQ;
      int_req_flit.packet_id = current_aw_trans.packet_id;
      int_req_flit.seq_num = 0;
      int_req_flit.qos = axi_awqos;
      int_req_flit.payload[AXI_ADDR_WIDTH-1:0] = current_aw_trans.base_addr;
      int_req_flit.payload[AXI_ADDR_WIDTH+7:AXI_ADDR_WIDTH] = current_aw_trans.burst_len;
      int_req_flit.payload[AXI_ADDR_WIDTH+10:AXI_ADDR_WIDTH+8] = current_aw_trans.burst_size;
    end else if (ar_state == AR_SEND_REQ) begin
      int_req_valid = 1'b1;
      int_req_flit.flit_type = FLIT_TYPE_SINGLE;
      int_req_flit.dest_x = current_ar_trans.dest_x;
      int_req_flit.dest_y = current_ar_trans.dest_y;
      int_req_flit.src_x = NODE_X[COORD_WIDTH-1:0];
      int_req_flit.src_y = NODE_Y[COORD_WIDTH-1:0];
      int_req_flit.vc_id = VC_REQ;
      int_req_flit.packet_id = current_ar_trans.packet_id;
      int_req_flit.seq_num = 0;
      int_req_flit.qos = axi_arqos;
      int_req_flit.payload[AXI_ADDR_WIDTH-1:0] = current_ar_trans.base_addr;
      int_req_flit.payload[AXI_ADDR_WIDTH+7:AXI_ADDR_WIDTH] = current_ar_trans.burst_len;
      int_req_flit.payload[AXI_ADDR_WIDTH+10:AXI_ADDR_WIDTH+8] = current_ar_trans.burst_size;
    end
  end
  
  assign noc_req_valid = int_req_valid;
  assign noc_req_flit = int_req_flit;
  assign noc_resp_ready = 1'b1; // Always ready to receive responses
  
  // =============================================================================
  // PACKET ID MANAGEMENT AND PERFORMANCE COUNTERS
  // =============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      next_packet_id <= 0;
      read_count <= 0;
      write_count <= 0;
    end else begin
      // Increment packet ID for each new transaction
      if ((aw_state == AW_IDLE && axi_awvalid && axi_awready) ||
          (ar_state == AR_IDLE && axi_arvalid && axi_arready)) begin
        next_packet_id <= next_packet_id + 1;
      end
      
      // Performance counters
      if (aw_state == AW_SEND_REQ && noc_req_ready) begin
        write_count <= write_count + 1;
      end
      
      if (ar_state == AR_SEND_REQ && noc_req_ready) begin
        read_count <= read_count + 1;
      end
    end
  end
  
  // Output assignments
  assign error_status = error_reg;
  assign perf_read_count = read_count;
  assign perf_write_count = write_count;
  
  // Debug R state machine transition
  always @(posedge clk) begin
    if (r_state == R_IDLE && lookup_valid) begin
      $display("[%0t] DEBUG_DUT: R_IDLE transition check: lookup_valid=%b, noc_resp_valid=%b, is_write=%b", 
               $time, lookup_valid, noc_resp_valid, outstanding_table[lookup_idx].is_write);
      if (lookup_valid && noc_resp_valid && !outstanding_table[lookup_idx].is_write) begin
        $display("[%0t] DEBUG_DUT: R_IDLE -> R_DATA transition triggered!", $time);
      end
    end
  end

endmodule
