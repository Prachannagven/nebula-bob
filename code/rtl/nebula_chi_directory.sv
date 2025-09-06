`timescale 1ns / 1ps
//==============================================================================
// Nebula CHI Directory Controller
//
// This module implements a directory-based coherency controller that manages
// cache line states across multiple nodes in the Nebula NoC system.
// It tracks cache line ownership, sharing patterns, and coordinates 
// coherency actions through snoop transactions.
//
// Features:
// - Directory-based MOESI protocol implementation
// - Snoop broadcast optimization with filtering
// - Atomic transaction coordination
// - Deadlock prevention with ordered message classes
// - Performance monitoring and statistics
//==============================================================================

import nebula_pkg::*;

module nebula_chi_directory #(
  parameter int HOME_NODE_ID = 0,               // This directory's home node ID
  parameter int NUM_NODES = 16,                 // Total number of nodes in system
  parameter int DIRECTORY_ENTRIES = 2048,      // Number of directory entries
  parameter int SNOOP_TIMEOUT_CYCLES = 1024    // Snoop response timeout
)(
  input  logic clk,
  input  logic rst_n,

  // CHI Request Interface (from requestor nodes)
  input  logic                chi_req_valid,
  output logic                chi_req_ready,
  input  chi_req_t            chi_req,

  // CHI Response Interface (to requestor nodes)  
  output logic                chi_resp_valid,
  input  logic                chi_resp_ready,
  output chi_resp_t           chi_resp,

  // CHI Data Interface (bidirectional)
  input  logic                chi_dat_req_valid,
  output logic                chi_dat_req_ready,
  input  chi_data_t           chi_dat_req,
  
  output logic                chi_dat_resp_valid,
  input  logic                chi_dat_resp_ready,
  output chi_data_t           chi_dat_resp,

  // CHI Snoop Interface (to cached nodes)
  output logic                chi_snp_valid,
  input  logic                chi_snp_ready,
  output chi_snoop_t          chi_snp,

  // CHI Snoop Response Interface (from cached nodes)
  input  logic                chi_snp_resp_valid,
  output logic                chi_snp_resp_ready,
  input  chi_resp_t           chi_snp_resp,

  // CHI Snoop Data Interface (from cached nodes)
  input  logic                chi_snp_dat_valid,
  output logic                chi_snp_dat_ready,
  input  chi_data_t           chi_snp_dat,

  // Memory Interface (to main memory/LLC)
  output logic                mem_req_valid,
  input  logic                mem_req_ready,
  output logic [CHI_REQ_ADDR_WIDTH-1:0] mem_req_addr,
  output logic                mem_req_write,
  output logic [CHI_DATA_WIDTH-1:0] mem_req_data,
  output logic [CHI_BE_WIDTH-1:0] mem_req_be,

  input  logic                mem_resp_valid,
  output logic                mem_resp_ready,
  input  logic [CHI_DATA_WIDTH-1:0] mem_resp_data,
  input  logic                mem_resp_error,

  // Status and Performance Monitoring
  output logic [31:0]         status_reg,
  output logic [31:0]         coherency_violations,
  output logic [31:0]         snoop_timeout_count,
  output logic [31:0]         directory_hit_rate,
  output logic [31:0]         memory_access_count
);

  // ============================================================================
  // INTERNAL PARAMETERS AND TYPES
  // ============================================================================
  
  localparam int DIRECTORY_WIDTH = $clog2(DIRECTORY_ENTRIES);
  localparam int NODE_WIDTH = $clog2(NUM_NODES);
  localparam int TIMEOUT_WIDTH = $clog2(SNOOP_TIMEOUT_CYCLES);

  // Directory FSM States
  typedef enum logic [3:0] {
    DIR_IDLE,
    DIR_LOOKUP,
    DIR_SNOOP_BROADCAST,
    DIR_AWAIT_SNOOP_RESP,
    DIR_MEMORY_ACCESS,
    DIR_DATA_TRANSFER,
    DIR_UPDATE_DIRECTORY,
    DIR_SEND_COMPLETION,
    DIR_ERROR_RECOVERY
  } directory_state_e;

  // Transaction Types
  typedef enum logic [2:0] {
    TXN_READ_SHARED,
    TXN_READ_UNIQUE,
    TXN_WRITE_UNIQUE,
    TXN_WRITEBACK,
    TXN_EVICTION,
    TXN_SNOOP_RESP,
    TXN_ATOMIC
  } transaction_type_e;

  // ============================================================================
  // INTERNAL SIGNALS AND STORAGE
  // ============================================================================

  // Directory Storage
  chi_directory_entry_t [DIRECTORY_ENTRIES-1:0] directory;
  logic [DIRECTORY_WIDTH-1:0] dir_index;
  logic directory_hit;
  chi_directory_entry_t current_entry;

  // Active Transaction Tracking
  typedef struct packed {
    logic                           valid;
    logic [CHI_TXN_ID_WIDTH-1:0]    txn_id;
    logic [CHI_NODE_ID_WIDTH-1:0]   requestor_id;
    logic [CHI_REQ_ADDR_WIDTH-1:0]  addr;
    chi_opcode_e                    opcode;
    transaction_type_e              txn_type;
    chi_cache_state_e               initial_state;
    chi_cache_state_e               final_state;
    logic [NUM_NODES-1:0]           snoop_pending;
    logic [NUM_NODES-1:0]           snoop_responses;
    logic                           data_from_cache;
    logic                           data_from_memory;
    logic                           memory_data_received;
    logic                           write_data_received;
    logic [TIMEOUT_WIDTH-1:0]       timeout_counter;
    logic [CHI_DATA_WIDTH-1:0]      data_buffer;
    logic                           forwarded_data;
  } active_transaction_t;

  active_transaction_t active_txn;
  directory_state_e dir_state, dir_state_next;

  // Snoop Generation Logic
  logic [NUM_NODES-1:0] snoop_targets;
  logic [NODE_WIDTH-1:0] current_snoop_target;
  logic snoop_broadcast_active;

  // Performance Counters
  logic [31:0] total_requests;
  logic [31:0] directory_hits;
  logic [31:0] coherency_violation_count;
  logic [31:0] timeout_count;
  logic [31:0] memory_accesses;

  // Internal Control Signals
  logic start_new_transaction;
  logic complete_transaction;
  // State tracking for breaking circular dependency
  logic transaction_pending;
  logic update_directory_entry;
  logic send_memory_request;
  logic broadcast_snoops;

  // ============================================================================
  // DIRECTORY INDEX CALCULATION AND LOOKUP
  // ============================================================================

  // Use address bits for directory indexing (cache line aligned)
  always_comb begin
    dir_index = chi_req.addr[DIRECTORY_WIDTH+5:6]; // 64-byte aligned
    directory_hit = directory[dir_index].valid;
    current_entry = directory[dir_index];
  end

  // ============================================================================
  // MAIN DIRECTORY CONTROLLER FSM
  // ============================================================================

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      dir_state <= DIR_IDLE;
      transaction_pending <= 1'b0;
    end else begin
      // Add debug output for state transitions
      if (dir_state != dir_state_next) begin
        $display("CHI DIR DEBUG: State transition %s -> %s", 
                 dir_state.name(), dir_state_next.name());
      end
      dir_state <= dir_state_next;
      
      // Track when a transaction request arrives and is ready to process
      // Set when valid request arrives while in IDLE and ready
      // Clear when transaction starts processing
      if (dir_state == DIR_IDLE && chi_req_valid && chi_req_ready) begin
        transaction_pending <= 1'b1;
        $display("[%0t] CHI DIR DEBUG: Transaction pending set", $time);
      end else if (start_new_transaction) begin
        transaction_pending <= 1'b0;
        $display("[%0t] CHI DIR DEBUG: Transaction pending cleared", $time);
      end
    end
  end

  always_comb begin
    dir_state_next = dir_state;
    start_new_transaction = 1'b0;
    complete_transaction = 1'b0;
    update_directory_entry = 1'b0;
    send_memory_request = 1'b0;
    broadcast_snoops = 1'b0;

    case (dir_state)
      DIR_IDLE: begin
        // Transition to DIR_LOOKUP when transaction is pending
        // $display("[%0t] [DEBUG] DIR_IDLE: transaction_pending=%b, chi_req_valid=%b, chi_req_ready=%b", 
        //          $time, transaction_pending, chi_req_valid, chi_req_ready);
        if (transaction_pending) begin
          start_new_transaction = 1'b1;
          dir_state_next = DIR_LOOKUP;
          // $display("[%0t] [DEBUG] Transaction pending in DIR_IDLE: starting transaction", $time);
        end
      end

      DIR_LOOKUP: begin
        // Transaction already started in DIR_IDLE, now process the request
        $display("[%0t] [DEBUG] Processing transaction in DIR_LOOKUP", $time);
        
        // Analyze request against directory state
        case (active_txn.opcode)
          CHI_READSHARED: begin
            if (current_entry.state == CHI_INVALID) begin
              // Clean miss - need data from memory
              dir_state_next = DIR_MEMORY_ACCESS;
            end else if (current_entry.state inside {CHI_SHARED_CLEAN, CHI_SHARED_DIRTY}) begin
              // Shared hit - can provide data immediately
              dir_state_next = DIR_DATA_TRANSFER;
            end else if (current_entry.state inside {CHI_UNIQUE_CLEAN, CHI_UNIQUE_DIRTY, CHI_MODIFIED}) begin
              // Exclusive state - need to snoop owner
              dir_state_next = DIR_SNOOP_BROADCAST;
            end
          end

          CHI_READUNIQUE: begin
            if (current_entry.state == CHI_INVALID) begin
              // Clean miss - need data from memory
              dir_state_next = DIR_MEMORY_ACCESS;
            end else begin
              // Need to invalidate all sharers/owner
              dir_state_next = DIR_SNOOP_BROADCAST;
            end
          end

          CHI_WRITENOSNPFULL, CHI_WRITEUNIQUEFULL: begin
            if (current_entry.sharers != '0 || current_entry.state != CHI_INVALID) begin
              // Need to invalidate existing copies
              dir_state_next = DIR_SNOOP_BROADCAST;
            end else begin
              // No existing copies - but need to wait for write data before memory access
              if (active_txn.write_data_received) begin
                dir_state_next = DIR_MEMORY_ACCESS;
              end else begin
                // Stay in lookup state until write data received
                dir_state_next = DIR_LOOKUP;
              end
            end
          end

          CHI_WRITEBACKFULL, CHI_WRITEVICTIMFULL: begin
            // Writeback from cache - update directory and memory
            dir_state_next = DIR_MEMORY_ACCESS;
          end

          default: begin
            dir_state_next = DIR_ERROR_RECOVERY;
          end
        endcase
      end

      DIR_SNOOP_BROADCAST: begin
        broadcast_snoops = 1'b1;
        if (snoop_broadcast_active) begin
          dir_state_next = DIR_AWAIT_SNOOP_RESP;
        end
      end

      DIR_AWAIT_SNOOP_RESP: begin
        if (active_txn.snoop_responses == active_txn.snoop_pending) begin
          // All snoop responses received
          if (active_txn.data_from_cache) begin
            dir_state_next = DIR_DATA_TRANSFER;
          end else begin
            dir_state_next = DIR_MEMORY_ACCESS;
          end
        end else if (active_txn.timeout_counter == SNOOP_TIMEOUT_CYCLES-1) begin
          // Timeout - proceed with degraded service
          dir_state_next = DIR_ERROR_RECOVERY;
        end
      end

      DIR_MEMORY_ACCESS: begin
        send_memory_request = 1'b1;
        if (mem_req_valid && mem_req_ready) begin
          // For write operations, go directly to directory update since no data response needed
          if (active_txn.txn_type == TXN_WRITE_UNIQUE || active_txn.txn_type == TXN_WRITEBACK) begin
            dir_state_next = DIR_UPDATE_DIRECTORY;
          end else begin
            // For read operations, wait for memory response and then send data
            dir_state_next = DIR_DATA_TRANSFER;
          end
        end
      end

      DIR_DATA_TRANSFER: begin
        // Wait for memory response to be received, then send data response
        if (active_txn.memory_data_received || active_txn.forwarded_data) begin
          if (chi_dat_resp_valid && chi_dat_resp_ready) begin
            dir_state_next = DIR_UPDATE_DIRECTORY;
          end
          // Stay in this state until data response is sent
        end else begin
          // Wait for memory response or forwarded data
          // The memory response will be captured in the always_ff block
          // and memory_data_received will be set
        end
      end

      DIR_UPDATE_DIRECTORY: begin
        update_directory_entry = 1'b1;
        dir_state_next = DIR_SEND_COMPLETION;
      end

      DIR_SEND_COMPLETION: begin
        if (chi_resp_valid && chi_resp_ready) begin
          complete_transaction = 1'b1;
          dir_state_next = DIR_IDLE;
        end
      end

      DIR_ERROR_RECOVERY: begin
        // Send error response and clean up
        if (chi_resp_valid && chi_resp_ready) begin
          complete_transaction = 1'b1;
          dir_state_next = DIR_IDLE;
        end
      end
    endcase
  end

  // ============================================================================
  // ACTIVE TRANSACTION MANAGEMENT
  // ============================================================================

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      active_txn <= '0;
    end else begin
      if (start_new_transaction) begin
        active_txn.valid <= 1'b1;
        active_txn.txn_id <= chi_req.txn_id;
        active_txn.requestor_id <= chi_req.src_id;
        active_txn.addr <= chi_req.addr;
        active_txn.opcode <= chi_req.opcode;
        active_txn.initial_state <= current_entry.state;
        active_txn.snoop_pending <= '0;
        active_txn.snoop_responses <= '0;
        active_txn.data_from_cache <= 1'b0;
        active_txn.data_from_memory <= 1'b0;
        active_txn.memory_data_received <= 1'b0;
        active_txn.timeout_counter <= '0;
        active_txn.forwarded_data <= 1'b0;
        active_txn.write_data_received <= 1'b0;

        // Determine transaction type
        case (chi_req.opcode)
          CHI_READSHARED: active_txn.txn_type <= TXN_READ_SHARED;
          CHI_READUNIQUE: active_txn.txn_type <= TXN_READ_UNIQUE;
          CHI_WRITENOSNPFULL, CHI_WRITEUNIQUEFULL: active_txn.txn_type <= TXN_WRITE_UNIQUE;
          CHI_WRITEBACKFULL, CHI_WRITEVICTIMFULL: active_txn.txn_type <= TXN_WRITEBACK;
          default: active_txn.txn_type <= TXN_READ_SHARED;
        endcase
      end

      if (complete_transaction) begin
        $display("CHI DIR DEBUG: Completing transaction TXN=%02h", active_txn.txn_id);
        active_txn.valid <= 1'b0;
      end

      // Update timeout counter
      if (dir_state == DIR_AWAIT_SNOOP_RESP) begin
        active_txn.timeout_counter <= active_txn.timeout_counter + 1;
      end

      // Handle snoop responses
      if (chi_snp_resp_valid && chi_snp_resp_ready) begin
        active_txn.snoop_responses[chi_snp_resp.src_id] <= 1'b1;
        
        // Check if snoop response includes data
        if (chi_snp_resp.opcode == CHI_SNPRESPDATA) begin
          active_txn.data_from_cache <= 1'b1;
        end
      end

      // Handle write data from requester
      if (chi_dat_req_valid && chi_dat_req_ready) begin
        active_txn.data_buffer <= chi_dat_req.data;
        active_txn.write_data_received <= 1'b1;
      end

      // Handle snoop data
      if (chi_snp_dat_valid && chi_snp_dat_ready) begin
        active_txn.data_buffer <= chi_snp_dat.data;
        active_txn.forwarded_data <= 1'b1;
      end

      // Handle memory responses
      if (mem_resp_valid && mem_resp_ready) begin
        active_txn.data_buffer <= mem_resp_data;
        active_txn.data_from_memory <= 1'b1;
        active_txn.memory_data_received <= 1'b1;
      end
    end
  end

  // ============================================================================
  // SNOOP BROADCAST LOGIC
  // ============================================================================

  always_comb begin
    snoop_targets = '0;
    
    // Determine which nodes need to be snooped based on directory state
    case (active_txn.txn_type)
      TXN_READ_SHARED: begin
        if (current_entry.state inside {CHI_UNIQUE_CLEAN, CHI_UNIQUE_DIRTY, CHI_MODIFIED}) begin
          // Snoop the current owner
          snoop_targets[current_entry.owner] = 1'b1;
        end
      end

      TXN_READ_UNIQUE, TXN_WRITE_UNIQUE: begin
        // Snoop all current sharers
        snoop_targets = current_entry.sharers;
      end

      default: begin
        snoop_targets = '0;
      end
    endcase

    // Don't snoop the requestor
    snoop_targets[active_txn.requestor_id] = 1'b0;
  end

  // Snoop broadcast sequencer
  logic [NODE_WIDTH-1:0] snoop_node_counter;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      snoop_node_counter <= '0;
      snoop_broadcast_active <= 1'b0;
    end else begin
      if (broadcast_snoops && !snoop_broadcast_active) begin
        snoop_broadcast_active <= 1'b1;
        snoop_node_counter <= '0;
        active_txn.snoop_pending <= snoop_targets;
      end

      if (snoop_broadcast_active) begin
        if (snoop_node_counter < NUM_NODES) begin
          if (snoop_targets[snoop_node_counter] && chi_snp_valid && chi_snp_ready) begin
            snoop_node_counter <= snoop_node_counter + 1;
          end else if (!snoop_targets[snoop_node_counter]) begin
            snoop_node_counter <= snoop_node_counter + 1;
          end
        end else begin
          snoop_broadcast_active <= 1'b0;
        end
      end
    end
  end

  assign current_snoop_target = snoop_node_counter[NODE_WIDTH-1:0];

  // ============================================================================
  // DIRECTORY UPDATE LOGIC
  // ============================================================================

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      for (int i = 0; i < DIRECTORY_ENTRIES; i++) begin
        directory[i] <= '0;
      end
    end else begin
      if (update_directory_entry) begin
        case (active_txn.txn_type)
          TXN_READ_SHARED: begin
            directory[dir_index].sharers[active_txn.requestor_id] <= 1'b1;
            directory[dir_index].state <= CHI_SHARED_CLEAN;
            directory[dir_index].valid <= 1'b1;
          end

          TXN_READ_UNIQUE: begin
            directory[dir_index].sharers <= '0;
            directory[dir_index].sharers[active_txn.requestor_id] <= 1'b1;
            directory[dir_index].owner <= active_txn.requestor_id;
            directory[dir_index].state <= CHI_UNIQUE_CLEAN;
            directory[dir_index].valid <= 1'b1;
          end

          TXN_WRITE_UNIQUE: begin
            directory[dir_index].sharers <= '0;
            directory[dir_index].sharers[active_txn.requestor_id] <= 1'b1;
            directory[dir_index].owner <= active_txn.requestor_id;
            directory[dir_index].state <= CHI_UNIQUE_DIRTY;
            directory[dir_index].dirty <= 1'b1;
            directory[dir_index].valid <= 1'b1;
          end

          TXN_WRITEBACK: begin
            directory[dir_index].sharers[active_txn.requestor_id] <= 1'b0;
            if (directory[dir_index].sharers == (1 << active_txn.requestor_id)) begin
              // Last sharer - line becomes invalid
              directory[dir_index].state <= CHI_INVALID;
              directory[dir_index].valid <= 1'b0;
            end
            directory[dir_index].dirty <= 1'b0;
          end
        endcase
      end
    end
  end

  // ============================================================================
  // CHI INTERFACE SIGNAL ASSIGNMENTS
  // ============================================================================

  // Request channel - Keep simple to avoid circular dependency
  assign chi_req_ready = (dir_state == DIR_IDLE) && !transaction_pending;
  assign chi_dat_req_ready = ((active_txn.valid && 
                               (active_txn.txn_type == TXN_WRITE_UNIQUE) && 
                               !active_txn.write_data_received) ||
                              (start_new_transaction && 
                               (chi_req.opcode == CHI_WRITEUNIQUEFULL)) ||
                              ((dir_state == DIR_LOOKUP) && 
                               (active_txn.txn_type == TXN_WRITE_UNIQUE) && 
                               !active_txn.write_data_received));

  // Response channel
  always_comb begin
    chi_resp = '0;
    chi_resp_valid = 1'b0;

    if (dir_state == DIR_SEND_COMPLETION) begin
      chi_resp.txn_id = active_txn.txn_id;
      chi_resp.src_id = HOME_NODE_ID[CHI_NODE_ID_WIDTH-1:0];
      chi_resp.tgt_id = active_txn.requestor_id;
      chi_resp.opcode = CHI_COMP;
      chi_resp.resp_err = CHI_OKAY;
      chi_resp_valid = 1'b1;
      $display("CHI DIR DEBUG: Sending completion response TXN=%02h, valid=%b, ready=%b", 
               active_txn.txn_id, chi_resp_valid, chi_resp_ready);
    end else if (dir_state == DIR_ERROR_RECOVERY) begin
      chi_resp.txn_id = active_txn.txn_id;
      chi_resp.src_id = HOME_NODE_ID[CHI_NODE_ID_WIDTH-1:0];
      chi_resp.tgt_id = active_txn.requestor_id;
      chi_resp.opcode = CHI_COMP;
      chi_resp.resp_err = CHI_SLVERR;
      chi_resp_valid = 1'b1;
    end
  end

  // Data response channel
  always_comb begin
    chi_dat_resp = '0;
    chi_dat_resp_valid = 1'b0;

    if (dir_state == DIR_DATA_TRANSFER && (active_txn.forwarded_data || active_txn.memory_data_received)) begin
      chi_dat_resp.txn_id = active_txn.txn_id;
      chi_dat_resp.src_id = HOME_NODE_ID[CHI_NODE_ID_WIDTH-1:0];
      chi_dat_resp.tgt_id = active_txn.requestor_id;
      chi_dat_resp.data = active_txn.data_buffer;
      chi_dat_resp.be = {CHI_BE_WIDTH{1'b1}};
      chi_dat_resp_valid = 1'b1;
      $display("CHI DIR DEBUG: Sending data response TXN=%02h, valid=%b, ready=%b", 
               active_txn.txn_id, chi_dat_resp_valid, chi_dat_resp_ready);
    end
  end

  // Snoop channel
  always_comb begin
    chi_snp = '0;
    chi_snp_valid = 1'b0;

    if (snoop_broadcast_active && snoop_targets[current_snoop_target]) begin
      chi_snp.txn_id = active_txn.txn_id;
      chi_snp.src_id = HOME_NODE_ID[CHI_NODE_ID_WIDTH-1:0];
      chi_snp.tgt_id = current_snoop_target[CHI_NODE_ID_WIDTH-1:0];
      chi_snp.addr = active_txn.addr;
      
      case (active_txn.txn_type)
        TXN_READ_SHARED: chi_snp.opcode = CHI_SNPSHARED;
        TXN_READ_UNIQUE, TXN_WRITE_UNIQUE: chi_snp.opcode = CHI_SNPUNIQUE;
        default: chi_snp.opcode = CHI_SNPSHARED;
      endcase
      
      chi_snp_valid = 1'b1;
    end
  end

  // Memory interface
  assign mem_req_valid = (dir_state == DIR_MEMORY_ACCESS) && send_memory_request;
  assign mem_req_addr = active_txn.addr;
  assign mem_req_write = (active_txn.txn_type == TXN_WRITEBACK) || (active_txn.txn_type == TXN_WRITE_UNIQUE);
  assign mem_req_data = active_txn.data_buffer;
  assign mem_req_be = {CHI_BE_WIDTH{1'b1}};
  assign mem_resp_ready = (dir_state == DIR_DATA_TRANSFER);

  // Snoop response interfaces
  assign chi_snp_resp_ready = (dir_state == DIR_AWAIT_SNOOP_RESP);
  assign chi_snp_dat_ready = (dir_state == DIR_AWAIT_SNOOP_RESP);

  // ============================================================================
  // PERFORMANCE MONITORING
  // ============================================================================

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      total_requests <= '0;
      directory_hits <= '0;
      coherency_violation_count <= '0;
      timeout_count <= '0;
      memory_accesses <= '0;
    end else begin
      if (chi_req_valid && chi_req_ready) begin
        total_requests <= total_requests + 1;
        if (directory_hit) begin
          directory_hits <= directory_hits + 1;
        end
      end

      if (active_txn.timeout_counter == SNOOP_TIMEOUT_CYCLES-1) begin
        timeout_count <= timeout_count + 1;
      end

      if (mem_req_valid && mem_req_ready) begin
        memory_accesses <= memory_accesses + 1;
      end

      // Coherency violation detection (simplified)
      if (dir_state == DIR_ERROR_RECOVERY) begin
        coherency_violation_count <= coherency_violation_count + 1;
      end
    end
  end

  // Status register assignments
  assign status_reg = {24'h0, dir_state};
  assign coherency_violations = coherency_violation_count;
  assign snoop_timeout_count = timeout_count;
  assign directory_hit_rate = (total_requests > 0) ? 
                             ((directory_hits * 100) / total_requests) : 32'h0;
  assign memory_access_count = memory_accesses;

endmodule
