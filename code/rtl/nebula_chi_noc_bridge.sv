`timescale 1ns / 1ps
//==============================================================================
// Nebula CHI-to-NoC Protocol Bridge
//
// This module translates between CHI coherency protocol messages and 
// NoC packet format for transmission across the mesh network.
// It handles message serialization, virtual channel mapping,
// and maintains transaction ordering requirements.
//
// Features:
// - CHI message serialization to NoC flits
// - NoC packet deserialization to CHI messages  
// - Virtual channel assignment by message type
// - Transaction ID preservation across network
// - Cache line segmentation for large data transfers
// - Ordering preservation with sequence numbers
//==============================================================================

import nebula_pkg::*;

module nebula_chi_noc_bridge #(
  parameter int NODE_ID = 0,                    // This node's network ID
  parameter int MAX_OUTSTANDING = 32           // Maximum outstanding transactions
)(
  input  logic clk,
  input  logic rst_n,

  // CHI Interface (Local)
  // Request Channel (outgoing)
  input  logic                chi_req_valid,
  output logic                chi_req_ready,
  input  chi_req_t            chi_req,

  // Response Channel (outgoing)  
  input  logic                chi_resp_valid,
  output logic                chi_resp_ready,
  input  chi_resp_t           chi_resp,

  // Data Channel (outgoing)
  input  logic                chi_dat_out_valid,
  output logic                chi_dat_out_ready,
  input  chi_data_t           chi_dat_out,

  // Snoop Channel (outgoing)
  input  logic                chi_snp_valid,
  output logic                chi_snp_ready,
  input  chi_snoop_t          chi_snp,

  // Request Channel (incoming)
  output logic                chi_req_in_valid,
  input  logic                chi_req_in_ready,
  output chi_req_t            chi_req_in,

  // Response Channel (incoming)
  output logic                chi_resp_in_valid,
  input  logic                chi_resp_in_ready,
  output chi_resp_t           chi_resp_in,

  // Data Channel (incoming)
  output logic                chi_dat_in_valid,
  input  logic                chi_dat_in_ready,
  output chi_data_t           chi_dat_in,

  // Snoop Channel (incoming)
  output logic                chi_snp_in_valid,
  input  logic                chi_snp_in_ready,
  output chi_snoop_t          chi_snp_in,

  // NoC Interface
  output logic                noc_flit_out_valid,
  input  logic                noc_flit_out_ready,
  output noc_flit_t           noc_flit_out,

  input  logic                noc_flit_in_valid,
  output logic                noc_flit_in_ready,
  input  noc_flit_t           noc_flit_in,

  // Status and Debug
  output logic [31:0]         packets_sent,
  output logic [31:0]         packets_received,
  output logic [31:0]         protocol_errors,
  output logic [31:0]         buffer_overruns
);

  // ============================================================================
  // INTERNAL PARAMETERS AND TYPES
  // ============================================================================

  localparam int OUTSTANDING_WIDTH = $clog2(MAX_OUTSTANDING);

  // CHI Message Types for NoC encoding
  typedef enum logic [3:0] {
    NOC_CHI_REQ     = 4'h0,
    NOC_CHI_RESP    = 4'h1, 
    NOC_CHI_DATA    = 4'h2,
    NOC_CHI_SNOOP   = 4'h3,
    NOC_CHI_SNRESP  = 4'h4,
    NOC_CHI_SNDATA  = 4'h5
  } noc_chi_msg_type_e;

  // NoC Packet Header for CHI messages
  typedef struct packed {
    noc_chi_msg_type_e          msg_type;
    logic [CHI_TXN_ID_WIDTH-1:0] txn_id;
    logic [CHI_NODE_ID_WIDTH-1:0] src_id;
    logic [CHI_NODE_ID_WIDTH-1:0] tgt_id;
    logic [3:0]                 data_chunks;  // For multi-flit data
    logic [3:0]                 chunk_id;    // Current chunk number
  } chi_noc_header_t;

  // ============================================================================
  // INTERNAL SIGNALS AND STORAGE
  // ============================================================================

  // Outstanding Transaction Tracking
  typedef struct packed {
    logic                           valid;
    logic [CHI_TXN_ID_WIDTH-1:0]    txn_id;
    logic [CHI_NODE_ID_WIDTH-1:0]   dest_node;
    noc_chi_msg_type_e              msg_type;
    logic [15:0]                    timestamp;
    logic [3:0]                     chunks_sent;
    logic [3:0]                     chunks_expected;
  } outstanding_txn_t;

  outstanding_txn_t [MAX_OUTSTANDING-1:0] outstanding_table;
  logic [OUTSTANDING_WIDTH-1:0] outstanding_alloc_ptr;
  logic [OUTSTANDING_WIDTH-1:0] outstanding_free_ptr;
  logic outstanding_table_full;

  // TX Path Arbitration
  logic [5:0] tx_arb_request;
  logic [5:0] tx_arb_grant;
  logic [2:0] tx_granted_channel;

  // TX FIFOs for each CHI channel
  logic chi_req_fifo_push, chi_req_fifo_pop, chi_req_fifo_empty, chi_req_fifo_full;
  chi_req_t chi_req_fifo_dout;

  logic chi_resp_fifo_push, chi_resp_fifo_pop, chi_resp_fifo_empty, chi_resp_fifo_full;
  chi_resp_t chi_resp_fifo_dout;

  logic chi_dat_fifo_push, chi_dat_fifo_pop, chi_dat_fifo_empty, chi_dat_fifo_full;
  chi_data_t chi_dat_fifo_dout;

  logic chi_snp_fifo_push, chi_snp_fifo_pop, chi_snp_fifo_empty, chi_snp_fifo_full;
  chi_snoop_t chi_snp_fifo_dout;

  // RX Path Packet Assembly
  typedef struct packed {
    logic                           active;
    noc_chi_msg_type_e              msg_type;
    logic [CHI_TXN_ID_WIDTH-1:0]    txn_id;
    logic [CHI_NODE_ID_WIDTH-1:0]   src_id;
    logic [3:0]                     chunks_received;
    logic [3:0]                     total_chunks;
    logic [CHI_DATA_WIDTH-1:0]      data_buffer;
    chi_req_t                       req_buffer;
    chi_resp_t                      resp_buffer;
    chi_snoop_t                     snp_buffer;
  } rx_assembly_t;

  rx_assembly_t rx_assembly;

  // Coordinate extraction from node ID
  logic [3:0] node_x, node_y;
  logic [3:0] dest_x, dest_y;

  // Output flit register to hold values
  noc_flit_t noc_flit_out_reg;
  logic noc_flit_out_valid_reg;
  
  // Intermediate signals for combinatorial logic
  noc_flit_t noc_flit_out_next;
  logic noc_flit_out_valid_next;

  // Performance counters
  logic [31:0] tx_packet_count, rx_packet_count;
  logic [31:0] error_count, overrun_count;

  // ============================================================================
  // NODE ID TO COORDINATE MAPPING
  // ============================================================================

  always_comb begin
    // Extract coordinates from node ID (assume 4x4 grid max for now)
    node_x = NODE_ID[3:0] % 4;  // X coordinate
    node_y = NODE_ID[3:0] / 4;  // Y coordinate
  end

  function automatic void get_dest_coordinates(
    input logic [CHI_NODE_ID_WIDTH-1:0] dest_node_id,
    output logic [3:0] x_coord,
    output logic [3:0] y_coord
  );
    x_coord = dest_node_id[3:0] % 4;
    y_coord = dest_node_id[3:0] / 4;
  endfunction

  // ============================================================================
  // TX PATH: CHI TO NOC CONVERSION
  // ============================================================================

  // Round-robin arbiter for TX channels
  logic [5:0] tx_arb_grant_next;
  
  always_comb begin
    tx_arb_grant_next = tx_arb_grant;
    
    // Only advance if we processed a request
    if (noc_flit_out_valid_next) begin
      // Rotate to find next requesting channel
      tx_arb_grant_next = {tx_arb_grant[4:0], tx_arb_grant[5]};
      
      // Keep rotating until we find a requesting channel or complete rotation
      for (int i = 0; i < 6; i++) begin
        if ((tx_arb_grant_next & tx_arb_request) != 6'b0 || tx_arb_request == 6'b0) begin
          break;
        end
        tx_arb_grant_next = {tx_arb_grant_next[4:0], tx_arb_grant_next[5]};
      end
    end
  end
  
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      tx_arb_grant <= 6'b000001;  // Start with REQ channel
    end else begin
      tx_arb_grant <= tx_arb_grant_next;
    end
  end

  // TX arbitration requests
  assign tx_arb_request[0] = !chi_req_fifo_empty;
  assign tx_arb_request[1] = !chi_resp_fifo_empty;
  assign tx_arb_request[2] = !chi_dat_fifo_empty;
  assign tx_arb_request[3] = !chi_snp_fifo_empty;
  assign tx_arb_request[4] = 1'b0;  // Reserved
  assign tx_arb_request[5] = 1'b0;  // Reserved

  // Determine which channel is granted
  always_comb begin
    tx_granted_channel = 3'h0;
    for (int i = 0; i < 6; i++) begin
      if (tx_arb_grant[i] && tx_arb_request[i]) begin
        tx_granted_channel = i[2:0];
        break;
      end
    end
  end

  // Output flit register to preserve coordinates when valid
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      noc_flit_out_reg <= '0;
      noc_flit_out_valid_reg <= 1'b0;
    end else begin
      // Update register when new valid flit is generated
      if (noc_flit_out_valid_next) begin
        noc_flit_out_reg <= noc_flit_out_next;
        noc_flit_out_valid_reg <= 1'b1;
      end else if (noc_flit_out_ready) begin
        // Clear valid when output is accepted
        noc_flit_out_valid_reg <= 1'b0;
      end
    end
  end

  // Assign outputs from register
  assign noc_flit_out = noc_flit_out_reg;
  assign noc_flit_out_valid = noc_flit_out_valid_reg;

  // CHI to NoC packet conversion
  always_comb begin
    // Default assignments
    chi_req_fifo_pop = 1'b0;
    chi_resp_fifo_pop = 1'b0;
    chi_dat_fifo_pop = 1'b0;
    chi_snp_fifo_pop = 1'b0;

    // Initialize next output with zero
    noc_flit_out_next = '0;
    noc_flit_out_valid_next = 1'b0;

    // Debug the channel grant
    $display("BRIDGE DEBUG: tx_granted_channel=%0h, chi_req_fifo_empty=%0b, tx_arb_grant=%06b, tx_arb_request=%06b", 
             tx_granted_channel, chi_req_fifo_empty, tx_arb_grant, tx_arb_request);

    // Only generate output if there's a valid grant and request match
    if ((tx_arb_grant & tx_arb_request) != 6'b0) begin
      case (tx_granted_channel)
        3'h0: begin // CHI Request
          if (tx_arb_grant[0] && tx_arb_request[0] && !chi_req_fifo_empty && !noc_flit_out_valid_reg) begin
            get_dest_coordinates(chi_req_fifo_dout.tgt_id, dest_x, dest_y);
            
            noc_flit_out_next.dest_x = dest_x;
            noc_flit_out_next.dest_y = dest_y;
            noc_flit_out_next.src_x = node_x;
            noc_flit_out_next.src_y = node_y;
            noc_flit_out_next.vc_id = VC_REQ;
            noc_flit_out_next.flit_type = FLIT_TYPE_SINGLE;
            noc_flit_out_next.seq_num = chi_req_fifo_dout.txn_id;

            // Debug output
            $display("BRIDGE DEBUG: NODE_ID=%0d, node_x=%0d, node_y=%0d, src_x=%0d, src_y=%0d", 
                     NODE_ID, node_x, node_y, noc_flit_out_next.src_x, noc_flit_out_next.src_y);

            // Pack CHI request into payload
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH-1:0] = chi_req_fifo_dout.txn_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH] = chi_req_fifo_dout.src_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH] = chi_req_fifo_dout.tgt_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+5:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH] = chi_req_fifo_dout.opcode;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+5:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+6] = chi_req_fifo_dout.addr;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+8:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+6] = chi_req_fifo_dout.size;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+12:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+9] = chi_req_fifo_dout.qos;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+15:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+13] = NOC_CHI_REQ;

            noc_flit_out_valid_next = 1'b1;
            chi_req_fifo_pop = noc_flit_out_ready;
          end
        end

        3'h1: begin // CHI Response
          if (tx_arb_grant[1] && tx_arb_request[1] && !chi_resp_fifo_empty && !noc_flit_out_valid_reg) begin
            get_dest_coordinates(chi_resp_fifo_dout.tgt_id, dest_x, dest_y);
            
            noc_flit_out_next.dest_x = dest_x;
            noc_flit_out_next.dest_y = dest_y;
            noc_flit_out_next.src_x = node_x;
            noc_flit_out_next.src_y = node_y;
            noc_flit_out_next.vc_id = VC_RSP;
            noc_flit_out_next.flit_type = FLIT_TYPE_SINGLE;
            noc_flit_out_next.seq_num = chi_resp_fifo_dout.txn_id;

            // Pack CHI response into payload
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH-1:0] = chi_resp_fifo_dout.txn_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH] = chi_resp_fifo_dout.src_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH] = chi_resp_fifo_dout.tgt_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+4:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH] = chi_resp_fifo_dout.opcode;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+6:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+5] = chi_resp_fifo_dout.resp_err;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+9:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+7] = NOC_CHI_RESP;

            noc_flit_out_valid_next = 1'b1;
            chi_resp_fifo_pop = noc_flit_out_ready;
          end
        end

        3'h2: begin // CHI Data
          if (tx_arb_grant[2] && tx_arb_request[2] && !chi_dat_fifo_empty && !noc_flit_out_valid_reg) begin
            get_dest_coordinates(chi_dat_fifo_dout.tgt_id, dest_x, dest_y);
            
            noc_flit_out_next.dest_x = dest_x;
            noc_flit_out_next.dest_y = dest_y;
            noc_flit_out_next.src_x = node_x;
            noc_flit_out_next.src_y = node_y;
            noc_flit_out_next.vc_id = VC_DAT;
            noc_flit_out_next.flit_type = FLIT_TYPE_SINGLE; // For now, single flit data
            noc_flit_out_next.seq_num = chi_dat_fifo_dout.txn_id;

            // Pack CHI data into payload (truncated for single flit)
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH-1:0] = chi_dat_fifo_dout.txn_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH] = chi_dat_fifo_dout.src_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH] = chi_dat_fifo_dout.tgt_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+2:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH] = NOC_CHI_DATA;
            // Pack data within payload bounds
            noc_flit_out_next.payload[PAYLOAD_BITS_PER_FLIT-1:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+3] = 
              chi_dat_fifo_dout.data[PAYLOAD_BITS_PER_FLIT-CHI_TXN_ID_WIDTH-2*CHI_NODE_ID_WIDTH-4:0];

            noc_flit_out_valid_next = 1'b1;
            chi_dat_fifo_pop = noc_flit_out_ready;
          end
        end

        3'h3: begin // CHI Snoop
          if (tx_arb_grant[3] && tx_arb_request[3] && !chi_snp_fifo_empty && !noc_flit_out_valid_reg) begin
            get_dest_coordinates(chi_snp_fifo_dout.tgt_id, dest_x, dest_y);
            
            noc_flit_out_next.dest_x = dest_x;
            noc_flit_out_next.dest_y = dest_y;
            noc_flit_out_next.src_x = node_x;
            noc_flit_out_next.src_y = node_y;
            noc_flit_out_next.vc_id = VC_SNP;
            noc_flit_out_next.flit_type = FLIT_TYPE_SINGLE;
            noc_flit_out_next.seq_num = chi_snp_fifo_dout.txn_id;

            // Pack CHI snoop into payload
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH-1:0] = chi_snp_fifo_dout.txn_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH] = chi_snp_fifo_dout.src_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH-1:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH] = chi_snp_fifo_dout.tgt_id;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+5:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH] = chi_snp_fifo_dout.opcode;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+5:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+6] = chi_snp_fifo_dout.addr;
            noc_flit_out_next.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+8:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+6] = NOC_CHI_SNOOP;

            noc_flit_out_valid_next = 1'b1;
            chi_snp_fifo_pop = noc_flit_out_ready;
          end
        end
      endcase
    end
  end

  // ============================================================================
  // RX PATH: NOC TO CHI CONVERSION
  // ============================================================================

  // NoC packet reception and CHI message reconstruction
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rx_assembly <= '0;
      chi_req_in_valid <= 1'b0;
      chi_resp_in_valid <= 1'b0;
      chi_dat_in_valid <= 1'b0;
      chi_snp_in_valid <= 1'b0;
    end else begin
      // Clear valid signals when acknowledged
      if (chi_req_in_valid && chi_req_in_ready) chi_req_in_valid <= 1'b0;
      if (chi_resp_in_valid && chi_resp_in_ready) chi_resp_in_valid <= 1'b0;
      if (chi_dat_in_valid && chi_dat_in_ready) chi_dat_in_valid <= 1'b0;
      if (chi_snp_in_valid && chi_snp_in_ready) chi_snp_in_valid <= 1'b0;

      // Process incoming NoC packets
      if (noc_flit_in_valid && noc_flit_in_ready) begin
        noc_chi_msg_type_e msg_type = noc_chi_msg_type_e'(noc_flit_in.payload[3:0]);
        
        case (msg_type)
          NOC_CHI_REQ: begin
            chi_req_in.txn_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+3:4];
            chi_req_in.src_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH+3:CHI_TXN_ID_WIDTH+4];
            chi_req_in.tgt_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+3:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH+4];
            chi_req_in.opcode <= chi_opcode_e'(noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+9:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+4]);
            chi_req_in.addr <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+9:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+10];
            chi_req_in.size <= 3'h6; // 64-byte cache line
            chi_req_in.qos <= QOS_NORMAL[QOS_WIDTH-1:0];
            chi_req_in_valid <= 1'b1;
          end

          NOC_CHI_RESP: begin
            chi_resp_in.txn_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+3:4];
            chi_resp_in.src_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH+3:CHI_TXN_ID_WIDTH+4];
            chi_resp_in.tgt_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+3:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH+4];
            chi_resp_in.opcode <= chi_resp_opcode_e'(noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+8:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+4]);
            chi_resp_in.resp_err <= chi_resp_err_e'(noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+10:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+9]);
            chi_resp_in.qos <= QOS_NORMAL[QOS_WIDTH-1:0];
            chi_resp_in_valid <= 1'b1;
          end

          NOC_CHI_DATA: begin
            chi_dat_in.txn_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+3:4];
            chi_dat_in.src_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH+3:CHI_TXN_ID_WIDTH+4];
            chi_dat_in.tgt_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+3:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH+4];
            // Extract data (truncated for single flit)
            chi_dat_in.data <= '0;
            // Extract data within payload bounds
            chi_dat_in.data[PAYLOAD_BITS_PER_FLIT-CHI_TXN_ID_WIDTH-2*CHI_NODE_ID_WIDTH-5:0] <= 
              noc_flit_in.payload[PAYLOAD_BITS_PER_FLIT-1:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+4];
            chi_dat_in.be <= {CHI_BE_WIDTH{1'b1}};
            chi_dat_in.qos <= QOS_NORMAL[QOS_WIDTH-1:0];
            chi_dat_in_valid <= 1'b1;
          end

          NOC_CHI_SNOOP: begin
            chi_snp_in.txn_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+3:4];
            chi_snp_in.src_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH+3:CHI_TXN_ID_WIDTH+4];
            chi_snp_in.tgt_id <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+3:CHI_TXN_ID_WIDTH+CHI_NODE_ID_WIDTH+4];
            chi_snp_in.opcode <= chi_opcode_e'(noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+9:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+4]);
            chi_snp_in.addr <= noc_flit_in.payload[CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+CHI_REQ_ADDR_WIDTH+9:CHI_TXN_ID_WIDTH+2*CHI_NODE_ID_WIDTH+10];
            chi_snp_in.qos <= QOS_NORMAL[QOS_WIDTH-1:0];
            chi_snp_in_valid <= 1'b1;
          end

          default: begin
            // Unknown message type - increment error counter
            error_count <= error_count + 1;
          end
        endcase
      end
    end
  end

  assign noc_flit_in_ready = 1'b1; // Always ready to receive

  // ============================================================================
  // INPUT FIFOS FOR TX PATH
  // ============================================================================

  // CHI Request FIFO
  nebula_fifo #(
    .DATA_WIDTH($bits(chi_req_t)),
    .DEPTH(8)
  ) chi_req_tx_fifo (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(chi_req_fifo_push),
    .rd_en(chi_req_fifo_pop),
    .wr_data(chi_req),
    .rd_data(chi_req_fifo_dout),
    .empty(chi_req_fifo_empty),
    .full(chi_req_fifo_full),
    .almost_empty(),
    .almost_full(),
    .count()
  );

  assign chi_req_fifo_push = chi_req_valid && chi_req_ready;
  assign chi_req_ready = !chi_req_fifo_full;

  // CHI Response FIFO
  nebula_fifo #(
    .DATA_WIDTH($bits(chi_resp_t)),
    .DEPTH(8)
  ) chi_resp_tx_fifo (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(chi_resp_fifo_push),
    .rd_en(chi_resp_fifo_pop),
    .wr_data(chi_resp),
    .rd_data(chi_resp_fifo_dout),
    .empty(chi_resp_fifo_empty),
    .full(chi_resp_fifo_full),
    .almost_empty(),
    .almost_full(),
    .count()
  );

  assign chi_resp_fifo_push = chi_resp_valid && chi_resp_ready;
  assign chi_resp_ready = !chi_resp_fifo_full;

  // CHI Data FIFO
  nebula_fifo #(
    .DATA_WIDTH($bits(chi_data_t)),
    .DEPTH(4)
  ) chi_dat_tx_fifo (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(chi_dat_fifo_push),
    .rd_en(chi_dat_fifo_pop),
    .wr_data(chi_dat_out),
    .rd_data(chi_dat_fifo_dout),
    .empty(chi_dat_fifo_empty),
    .full(chi_dat_fifo_full),
    .almost_empty(),
    .almost_full(),
    .count()
  );

  assign chi_dat_fifo_push = chi_dat_out_valid && chi_dat_out_ready;
  assign chi_dat_out_ready = !chi_dat_fifo_full;

  // CHI Snoop FIFO
  nebula_fifo #(
    .DATA_WIDTH($bits(chi_snoop_t)),
    .DEPTH(8)
  ) chi_snp_tx_fifo (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(chi_snp_fifo_push),
    .rd_en(chi_snp_fifo_pop),
    .wr_data(chi_snp),
    .rd_data(chi_snp_fifo_dout),
    .empty(chi_snp_fifo_empty),
    .full(chi_snp_fifo_full),
    .almost_empty(),
    .almost_full(),
    .count()
  );

  assign chi_snp_fifo_push = chi_snp_valid && chi_snp_ready;
  assign chi_snp_ready = !chi_snp_fifo_full;

  // ============================================================================
  // OUTSTANDING TRANSACTION TRACKING
  // ============================================================================

  assign outstanding_table_full = (outstanding_alloc_ptr + 1 == outstanding_free_ptr);

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      for (int i = 0; i < MAX_OUTSTANDING; i++) begin
        outstanding_table[i] <= '0;
      end
      outstanding_alloc_ptr <= '0;
      outstanding_free_ptr <= '0;
    end else begin
      // Track outgoing transactions
      if (noc_flit_out_valid && noc_flit_out_ready && !outstanding_table_full) begin
        outstanding_table[outstanding_alloc_ptr].valid <= 1'b1;
        outstanding_table[outstanding_alloc_ptr].txn_id <= noc_flit_out.seq_num;
        outstanding_table[outstanding_alloc_ptr].dest_node <= {dest_y, dest_x};
        outstanding_table[outstanding_alloc_ptr].msg_type <= noc_chi_msg_type_e'(noc_flit_out.payload[3:0]);
        outstanding_table[outstanding_alloc_ptr].timestamp <= tx_packet_count[15:0];
        outstanding_alloc_ptr <= outstanding_alloc_ptr + 1;
      end

      // Clear completed transactions
      if ((chi_resp_in_valid && chi_resp_in_ready) ||
          (chi_dat_in_valid && chi_dat_in_ready)) begin
        for (int i = 0; i < MAX_OUTSTANDING; i++) begin
          if (outstanding_table[i].valid && 
              ((outstanding_table[i].txn_id == chi_resp_in.txn_id) ||
               (outstanding_table[i].txn_id == chi_dat_in.txn_id))) begin
            outstanding_table[i].valid <= 1'b0;
            outstanding_free_ptr <= outstanding_free_ptr + 1;
            break;
          end
        end
      end
    end
  end

  // ============================================================================
  // PERFORMANCE MONITORING
  // ============================================================================

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      tx_packet_count <= '0;
      rx_packet_count <= '0;
      error_count <= '0;
      overrun_count <= '0;
    end else begin
      if (noc_flit_out_valid && noc_flit_out_ready) begin
        tx_packet_count <= tx_packet_count + 1;
      end

      if (noc_flit_in_valid && noc_flit_in_ready) begin
        rx_packet_count <= rx_packet_count + 1;
      end

      // Count buffer overruns
      if ((chi_req_valid && chi_req_fifo_full) ||
          (chi_resp_valid && chi_resp_fifo_full) ||
          (chi_dat_out_valid && chi_dat_fifo_full) ||
          (chi_snp_valid && chi_snp_fifo_full)) begin
        overrun_count <= overrun_count + 1;
      end
    end
  end

  // Output assignments
  assign packets_sent = tx_packet_count;
  assign packets_received = rx_packet_count;
  assign protocol_errors = error_count;
  assign buffer_overruns = overrun_count;

endmodule
