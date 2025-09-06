`timescale 1ns / 1ps
//==============================================================================
// Nebula CHI (Coherent Hub Interface) Protocol Interface
//
// This module implements a CHI-Lite compatible interface for cache coherency
// in the Nebula NoC system. It supports directory-based coherency with 
// snoop filtering and maintains MOESI cache states across multiple nodes.
//
// Features:
// - CHI-Lite protocol compliance  
// - Directory-based coherency protocol
// - Snoop filtering and broadcast optimization
// - Outstanding transaction tracking
// - Cache line state management (MOESI)
// - Integration with NoC packet format
//==============================================================================

import nebula_pkg::*;

module nebula_chi_interface #(
  parameter int NODE_ID = 0,                    // This node's ID
  parameter int NUM_OUTSTANDING = 64,           // Outstanding transaction entries  
  parameter int DIRECTORY_ENTRIES = 1024,      // Directory cache entries
  parameter int SNOOP_FILTER_ENTRIES = 512     // Snoop filter entries
)(
  input  logic clk,
  input  logic rst_n,

  // CHI Request Channel (RN -> HN)
  input  logic                chi_req_valid,
  output logic                chi_req_ready, 
  input  chi_req_t            chi_req,

  // CHI Response Channel (HN -> RN)
  output logic                chi_resp_valid,
  input  logic                chi_resp_ready,
  output chi_resp_t           chi_resp,

  // CHI Data Channel (Bidirectional)
  input  logic                chi_dat_req_valid,
  output logic                chi_dat_req_ready,
  input  chi_data_t           chi_dat_req,
  
  output logic                chi_dat_resp_valid,
  input  logic                chi_dat_resp_ready,
  output chi_data_t           chi_dat_resp,

  // CHI Snoop Channel (HN -> RN)
  output logic                chi_snp_valid,
  input  logic                chi_snp_ready,
  output chi_snoop_t          chi_snp,

  // CHI Snoop Response Channel (RN -> HN)
  input  logic                chi_snp_resp_valid,
  output logic                chi_snp_resp_ready,
  input  chi_resp_t           chi_snp_resp,

  // CHI Snoop Data Channel (RN -> HN)
  input  logic                chi_snp_dat_valid,
  output logic                chi_snp_dat_ready,
  input  chi_data_t           chi_snp_dat,

  // NoC Interface (to local router)
  output logic                noc_flit_out_valid,
  input  logic                noc_flit_out_ready,
  output noc_flit_t           noc_flit_out,

  input  logic                noc_flit_in_valid,
  output logic                noc_flit_in_ready,
  input  noc_flit_t           noc_flit_in,

  // Configuration and Status
  input  logic [CHI_REQ_ADDR_WIDTH-1:0] base_addr,
  input  logic [CHI_REQ_ADDR_WIDTH-1:0] addr_mask,
  output logic [31:0]         status_reg,
  output logic [31:0]         error_reg,
  output logic [31:0]         perf_counter_req,
  output logic [31:0]         perf_counter_resp,
  output logic [31:0]         cache_hit_counter,
  output logic [31:0]         cache_miss_counter
);

  // ============================================================================
  // INTERNAL PARAMETERS AND CONSTANTS
  // ============================================================================
  
  localparam int OUTSTANDING_WIDTH = $clog2(NUM_OUTSTANDING);
  localparam int DIRECTORY_WIDTH = $clog2(DIRECTORY_ENTRIES);
  localparam int SNOOP_FILTER_WIDTH = $clog2(SNOOP_FILTER_ENTRIES);

  // CHI-to-NoC VC mapping
  localparam int CHI_REQ_VC = VC_REQ;    // Request messages use REQ VC
  localparam int CHI_RESP_VC = VC_RSP;   // Response messages use RSP VC
  localparam int CHI_DATA_VC = VC_DAT;   // Data messages use DAT VC
  localparam int CHI_SNOOP_VC = VC_SNP;  // Snoop messages use SNP VC

  // ============================================================================
  // INTERNAL SIGNALS AND STATE
  // ============================================================================

  // Outstanding Transaction Table
  typedef struct packed {
    logic                           valid;
    logic [CHI_TXN_ID_WIDTH-1:0]    txn_id;
    logic [CHI_NODE_ID_WIDTH-1:0]   src_id;
    logic [CHI_NODE_ID_WIDTH-1:0]   tgt_id;
    logic [CHI_REQ_ADDR_WIDTH-1:0]  addr;
    chi_opcode_e                    opcode;
    chi_cache_state_e               req_state;
    logic [2:0]                     size;
    logic                           awaiting_data;
    logic                           awaiting_snoop_resp;
    logic [15:0]                    timestamp;
  } outstanding_entry_t;

  outstanding_entry_t [NUM_OUTSTANDING-1:0] outstanding_table;
  logic [OUTSTANDING_WIDTH-1:0] outstanding_alloc_ptr;
  logic [OUTSTANDING_WIDTH-1:0] outstanding_free_ptr;

  // Directory Cache
  chi_directory_entry_t [DIRECTORY_ENTRIES-1:0] directory_cache;
  logic [DIRECTORY_WIDTH-1:0] directory_alloc_ptr;

  // Snoop Filter  
  typedef struct packed {
    logic                           valid;
    logic [CHI_REQ_ADDR_WIDTH-1:0]  addr;
    logic [63:0]                    sharers;
    logic [CHI_NODE_ID_WIDTH-1:0]   owner;
    chi_cache_state_e               state;
  } snoop_filter_entry_t;

  snoop_filter_entry_t [SNOOP_FILTER_ENTRIES-1:0] snoop_filter;
  logic [SNOOP_FILTER_WIDTH-1:0] snoop_filter_alloc_ptr;

  // FSM States
  typedef enum logic [2:0] {
    CHI_IDLE,
    CHI_DIRECTORY_LOOKUP,
    CHI_SNOOP_BROADCAST, 
    CHI_AWAIT_SNOOP_RESP,
    CHI_DATA_TRANSFER,
    CHI_COMPLETION,
    CHI_ERROR
  } chi_fsm_state_e;

  chi_fsm_state_e chi_req_state, chi_req_state_next;

  // Internal FIFOs
  chi_req_t    req_fifo_data;
  logic        req_fifo_push, req_fifo_pop, req_fifo_empty, req_fifo_full;

  chi_resp_t   resp_fifo_data;
  logic        resp_fifo_push, resp_fifo_pop, resp_fifo_empty, resp_fifo_full;

  chi_data_t   data_fifo_data;
  logic        data_fifo_push, data_fifo_pop, data_fifo_empty, data_fifo_full;

  // NoC Packet Assembly/Disassembly
  noc_flit_t   noc_tx_flit, noc_rx_flit;
  logic        noc_tx_valid, noc_tx_ready, noc_rx_valid, noc_rx_ready;

  // Performance Counters
  logic [31:0] req_counter, resp_counter, hit_counter, miss_counter;
  logic [31:0] error_counter;

  // Address translation
  logic [3:0] dest_x, dest_y;
  logic [CHI_NODE_ID_WIDTH-1:0] dest_node_id;
  logic       addr_match;

  // ============================================================================
  // ADDRESS MAPPING AND COORDINATE EXTRACTION
  // ============================================================================

  always_comb begin
    // Check if address is within our managed range
    addr_match = (chi_req.addr & addr_mask) == (base_addr & addr_mask);
    if (chi_req_valid) begin
      $display("DEBUG RTL: addr_match check: req_addr=%h, base_addr=%h, addr_mask=%h, match=%b", 
               chi_req.addr, base_addr, addr_mask, addr_match);
    end
    
    // Extract destination coordinates from address
    // Use address bits [19:16] for X coordinate, [15:12] for Y coordinate
    dest_x = chi_req.addr[19:16];
    dest_y = chi_req.addr[15:12];
    
    // Convert coordinates to node ID
    dest_node_id = {dest_x, dest_y};
  end

  // ============================================================================
  // CHI REQUEST PROCESSING FSM
  // ============================================================================

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      chi_req_state <= CHI_IDLE;
    end else begin
      chi_req_state <= chi_req_state_next;
    end
  end

  always_comb begin
    chi_req_state_next = chi_req_state;

    case (chi_req_state)
      CHI_IDLE: begin
        if (chi_req_valid && chi_req_ready) begin
          $display("DEBUG RTL: CHI_IDLE processing request, addr_match=%b", addr_match);
          if (addr_match) begin
            $display("DEBUG RTL: Transitioning to CHI_DIRECTORY_LOOKUP");
            chi_req_state_next = CHI_DIRECTORY_LOOKUP;
          end else begin
            $display("DEBUG RTL: Transitioning to CHI_ERROR (addr mismatch)");
            chi_req_state_next = CHI_ERROR;
          end
        end
      end

      CHI_DIRECTORY_LOOKUP: begin
        // Look up cache line in directory
        // Determine if snoops are needed
        $display("DEBUG RTL: CHI_DIRECTORY_LOOKUP - transitioning to CHI_SNOOP_BROADCAST");
        chi_req_state_next = CHI_SNOOP_BROADCAST;
      end

      CHI_SNOOP_BROADCAST: begin
        // Broadcast snoops to relevant nodes
        if (chi_snp_valid && chi_snp_ready) begin
          chi_req_state_next = CHI_AWAIT_SNOOP_RESP;
        end
      end

      CHI_AWAIT_SNOOP_RESP: begin
        // Wait for all snoop responses
        if (chi_snp_resp_valid) begin
          $display("DEBUG RTL: Received snoop response: TXN=%02h, OP=%02h", chi_snp_resp.txn_id, chi_snp_resp.opcode);
          chi_req_state_next = CHI_DATA_TRANSFER;
        end else begin
          $display("DEBUG RTL: Waiting for snoop response, ready=%b", chi_snp_resp_ready);
        end
      end

      CHI_DATA_TRANSFER: begin
        // Handle data movement if required
        chi_req_state_next = CHI_COMPLETION;
      end

      CHI_COMPLETION: begin
        // Send completion response
        if (chi_resp_valid && chi_resp_ready) begin
          chi_req_state_next = CHI_IDLE;
        end
      end

      CHI_ERROR: begin
        // Send error response
        if (chi_resp_valid && chi_resp_ready) begin
          chi_req_state_next = CHI_IDLE;
        end
      end
    endcase
  end

  // ============================================================================
  // DIRECTORY CACHE MANAGEMENT
  // ============================================================================

  logic [DIRECTORY_WIDTH-1:0] directory_lookup_idx;
  logic directory_hit;
  chi_directory_entry_t directory_entry;

  // Simple direct-mapped directory cache
  // In practice, this would be more sophisticated (set-associative, etc.)
  assign directory_lookup_idx = chi_req.addr[DIRECTORY_WIDTH+5:6]; // Cache line aligned

  always_comb begin
    directory_hit = directory_cache[directory_lookup_idx].valid && 
                   (directory_cache[directory_lookup_idx].pending_txn == '0);
    directory_entry = directory_cache[directory_lookup_idx];
  end

  // Directory update logic
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      for (int i = 0; i < DIRECTORY_ENTRIES; i++) begin
        directory_cache[i] <= '0;
      end
      directory_alloc_ptr <= '0;
    end else begin
      // Update directory based on CHI transactions
      if (chi_req_state == CHI_COMPLETION) begin
        case (chi_req.opcode)
          CHI_READSHARED: begin
            directory_cache[directory_lookup_idx].sharers[chi_req.src_id] <= 1'b1;
            directory_cache[directory_lookup_idx].state <= CHI_SHARED_CLEAN;
          end
          CHI_READUNIQUE: begin
            directory_cache[directory_lookup_idx].sharers <= '0;
            directory_cache[directory_lookup_idx].sharers[chi_req.src_id] <= 1'b1;
            directory_cache[directory_lookup_idx].owner <= chi_req.src_id;
            directory_cache[directory_lookup_idx].state <= CHI_UNIQUE_CLEAN;
          end
          // Add more cases for other opcodes
          default: begin
            // Default handling
          end
        endcase
        directory_cache[directory_lookup_idx].valid <= 1'b1;
      end
    end
  end

  // ============================================================================
  // SNOOP FILTER MANAGEMENT  
  // ============================================================================

  logic [SNOOP_FILTER_WIDTH-1:0] snoop_filter_lookup_idx;
  logic snoop_filter_hit;
  snoop_filter_entry_t snoop_filter_entry;

  // Simple hash function for snoop filter lookup
  assign snoop_filter_lookup_idx = chi_req.addr[SNOOP_FILTER_WIDTH+5:6] ^ 
                                   chi_req.addr[SNOOP_FILTER_WIDTH+11:12];

  always_comb begin
    snoop_filter_hit = snoop_filter[snoop_filter_lookup_idx].valid &&
                      (snoop_filter[snoop_filter_lookup_idx].addr[CHI_REQ_ADDR_WIDTH-1:6] == 
                       chi_req.addr[CHI_REQ_ADDR_WIDTH-1:6]);
    snoop_filter_entry = snoop_filter[snoop_filter_lookup_idx];
  end

  // ============================================================================
  // CHI-TO-NOC PROTOCOL TRANSLATION
  // ============================================================================

  // Convert CHI requests to NoC packets
  always_comb begin
    noc_tx_flit = '0;
    noc_tx_valid = 1'b0;

    if (chi_req_state == CHI_SNOOP_BROADCAST) begin
      $display("DEBUG RTL: Broadcasting snoop to (%0d,%0d), flit_valid=%b, noc_ready=%b", 
               dest_x, dest_y, noc_tx_valid, noc_flit_out_ready);
      // Create NoC packet for remote snoop
      noc_tx_flit.dest_x = dest_x;
      noc_tx_flit.dest_y = dest_y;
      noc_tx_flit.src_x = NODE_ID[7:4];   // Extract X from node ID
      noc_tx_flit.src_y = NODE_ID[3:0];   // Extract Y from node ID
      noc_tx_flit.vc_id = CHI_SNOOP_VC;
      noc_tx_flit.flit_type = FLIT_TYPE_SINGLE;
      noc_tx_flit.seq_num = outstanding_table[current_entry_ptr].txn_id;
      
      // Pack CHI snoop into NoC payload
      noc_tx_flit.payload[CHI_TXN_ID_WIDTH-1:0] = chi_snp.txn_id;
      noc_tx_flit.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH] = chi_snp.src_id;
      noc_tx_flit.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH] = chi_snp.tgt_id;
      // Pack address and opcode...
      
      noc_tx_valid = 1'b1;  // Assert valid when broadcasting snoop
    end
  end

  // Convert NoC packets to CHI responses and generate internal completion responses
  always_comb begin
    chi_resp = '0;
    chi_resp_valid = 1'b0;

    if (noc_flit_in_valid && noc_flit_in.vc_id == CHI_RESP_VC) begin
      // Unpack CHI response from NoC payload
      chi_resp.txn_id = noc_flit_in.payload[7:0];
      chi_resp.src_id = noc_flit_in.payload[13:8];
      chi_resp.tgt_id = noc_flit_in.payload[19:14];
      chi_resp.opcode = chi_resp_opcode_e'(noc_flit_in.payload[24:20]);
      chi_resp.resp_err = chi_resp_err_e'(noc_flit_in.payload[26:25]);
      chi_resp.dbid = noc_flit_in.payload[34:27];
      chi_resp.fwd_state = noc_flit_in.payload[37:35];
      chi_resp.rsvdc = noc_flit_in.payload[41:38];
      chi_resp.qos = noc_flit_in.payload[45:42];
      
      chi_resp_valid = 1'b1;
    end else if (chi_req_state == CHI_COMPLETION && outstanding_table[current_entry_ptr].valid) begin
      // Generate internal completion response
      chi_resp.txn_id = outstanding_table[current_entry_ptr].txn_id;
      chi_resp.src_id = NODE_ID[CHI_NODE_ID_WIDTH-1:0];
      chi_resp.tgt_id = outstanding_table[current_entry_ptr].src_id;
      chi_resp.opcode = CHI_COMP;
      chi_resp.resp_err = CHI_OKAY;
      chi_resp.dbid = 8'h00;
      chi_resp.fwd_state = 3'h0;
      chi_resp.rsvdc = 4'h0;
      chi_resp.qos = 4'h0;
      
      chi_resp_valid = 1'b1;
    end
  end

  // ============================================================================
  // OUTSTANDING TRANSACTION MANAGEMENT
  // ============================================================================

  logic outstanding_table_full;
  logic [OUTSTANDING_WIDTH-1:0] outstanding_lookup_idx;

  assign outstanding_table_full = (outstanding_alloc_ptr + 1 == outstanding_free_ptr);

  // Find outstanding transaction by TXN_ID
  always_comb begin
    outstanding_lookup_idx = '0;
    for (int i = 0; i < NUM_OUTSTANDING; i++) begin
      if (outstanding_table[i].valid && 
          outstanding_table[i].txn_id == chi_req.txn_id) begin
        outstanding_lookup_idx = i[OUTSTANDING_WIDTH-1:0];
        break;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      for (int i = 0; i < NUM_OUTSTANDING; i++) begin
        outstanding_table[i] <= '0;
      end
      outstanding_alloc_ptr <= '0;
      outstanding_free_ptr <= '0;
    end else begin
      // Allocate new outstanding entry
      if (chi_req_valid && chi_req_ready && !outstanding_table_full) begin
        outstanding_table[outstanding_alloc_ptr].valid <= 1'b1;
        outstanding_table[outstanding_alloc_ptr].txn_id <= chi_req.txn_id;
        outstanding_table[outstanding_alloc_ptr].src_id <= chi_req.src_id;
        outstanding_table[outstanding_alloc_ptr].tgt_id <= chi_req.tgt_id;
        outstanding_table[outstanding_alloc_ptr].addr <= chi_req.addr;
        outstanding_table[outstanding_alloc_ptr].opcode <= chi_req.opcode;
        outstanding_table[outstanding_alloc_ptr].size <= chi_req.size;
        outstanding_table[outstanding_alloc_ptr].timestamp <= req_counter[15:0];
        
        $display("DEBUG RTL: Allocated outstanding entry [%0d]: TXN=%02h, ADDR=%016h", 
                 outstanding_alloc_ptr, chi_req.txn_id, chi_req.addr);
        
        outstanding_alloc_ptr <= outstanding_alloc_ptr + 1;
      end

      // Free completed transactions
      if (chi_resp_valid && chi_resp_ready) begin
        outstanding_table[outstanding_lookup_idx].valid <= 1'b0;
        outstanding_free_ptr <= outstanding_free_ptr + 1;
      end
    end
  end

  // ============================================================================
  // CONTROL SIGNALS AND READY/VALID LOGIC
  // ============================================================================

  assign chi_req_ready = !outstanding_table_full && (chi_req_state == CHI_IDLE);
  assign noc_flit_out_valid = noc_tx_valid;
  assign noc_flit_out = noc_tx_flit;
  assign noc_flit_in_ready = noc_rx_ready;

  // Snoop channel assignments
  assign chi_snp_valid = (chi_req_state == CHI_SNOOP_BROADCAST);
  assign chi_snp_resp_ready = (chi_req_state == CHI_AWAIT_SNOOP_RESP);
  assign chi_snp_dat_ready = (chi_req_state == CHI_DATA_TRANSFER);
  
  // Generate snoop request based on current outstanding transaction
  logic [OUTSTANDING_WIDTH-1:0] current_entry_ptr;
  assign current_entry_ptr = (outstanding_alloc_ptr == 0) ? NUM_OUTSTANDING - 1 : outstanding_alloc_ptr - 1;
  
  always_comb begin
    chi_snp = '0;
    if (chi_req_state == CHI_SNOOP_BROADCAST && outstanding_table[current_entry_ptr].valid) begin
      chi_snp.txn_id = outstanding_table[current_entry_ptr].txn_id;
      chi_snp.src_id = NODE_ID[CHI_NODE_ID_WIDTH-1:0];
      chi_snp.tgt_id = outstanding_table[current_entry_ptr].tgt_id;
      chi_snp.addr = outstanding_table[current_entry_ptr].addr;
      chi_snp.opcode = CHI_SNPONCE;  // Basic snoop operation
      chi_snp.ns = 1'b0;  // Non-secure
      chi_snp.do_not_goto_sd = 1'b0;  // Allow transition to Shared Dirty
      chi_snp.ret_to_src = 1'b1;  // Return to source
      chi_snp.rsvdc = '0;  // Reserved field
      chi_snp.qos = QOS_NORMAL[QOS_WIDTH-1:0];  // Normal QoS
    end else if (chi_req_state == CHI_SNOOP_BROADCAST) begin
      $display("DEBUG RTL: SNOOP_BROADCAST state but entry [%0d] not valid (alloc_ptr=%0d)", 
               current_entry_ptr, outstanding_alloc_ptr);
    end
  end

  // ============================================================================
  // PERFORMANCE COUNTERS AND STATUS REPORTING
  // ============================================================================

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      req_counter <= '0;
      resp_counter <= '0;
      hit_counter <= '0;
      miss_counter <= '0;
      error_counter <= '0;
    end else begin
      if (chi_req_valid && chi_req_ready) begin
        req_counter <= req_counter + 1;
      end

      if (chi_resp_valid && chi_resp_ready) begin
        resp_counter <= resp_counter + 1;
      end

      if (directory_hit) begin
        hit_counter <= hit_counter + 1;
      end else if (chi_req_valid && chi_req_ready) begin
        miss_counter <= miss_counter + 1;
      end

      if (chi_req_state == CHI_ERROR) begin
        error_counter <= error_counter + 1;
      end
    end
  end

  // Status and error registers
  assign status_reg = {16'h0, chi_req_state, 8'h0, outstanding_table_full, 2'h0};
  assign error_reg = error_counter;
  assign perf_counter_req = req_counter;
  assign perf_counter_resp = resp_counter;  
  assign cache_hit_counter = hit_counter;
  assign cache_miss_counter = miss_counter;

endmodule
