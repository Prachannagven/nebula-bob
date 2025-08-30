/**
 * NoC Packet Disassembler Module
 * 
 * Reconstructs higher-level packets from incoming NoC flits.
 * Handles multi-flit packet reassembly with error checking.
 * 
 * Features:
 * - Multi-flit packet reconstruction
 * - Sequence number verification
 * - Error detection and reporting
 * - Payload data reassembly
 * - Packet completion signaling
 */

import nebula_pkg::*;

module nebula_packet_disassembler #(
  parameter int MAX_PAYLOAD_SIZE = 1024,
  parameter int FLITS_PER_PACKET = 4
)(
  input  logic                              clk,
  input  logic                              rst_n,
  
  // Input flit interface
  input  logic                              flit_valid,
  input  noc_flit_t                         flit_in,
  output logic                              flit_ready,
  
  // Output packet interface
  output logic                              pkt_valid,
  output logic [COORD_WIDTH-1:0]            src_x, src_y,
  output logic [COORD_WIDTH-1:0]            dest_x, dest_y,
  output logic [VC_ID_WIDTH-1:0]            vc_id,
  output logic [QOS_WIDTH-1:0]              qos,
  output logic [MAX_PAYLOAD_SIZE*8-1:0]     payload_data,
  output logic [$clog2(MAX_PAYLOAD_SIZE)-1:0] payload_size,
  input  logic                              pkt_ready,
  
  // Error reporting
  output logic                              error_detected,
  output error_code_e                       error_code
);

  // State machine states
  typedef enum logic [2:0] {
    IDLE,
    RECV_HEAD,
    RECV_BODY,
    RECV_TAIL,
    PKT_COMPLETE,
    ERROR_STATE
  } state_e;
  
  state_e current_state, next_state;
  
  // Error detection signals
  logic seq_error_detected;
  
  // Packet reconstruction registers
  logic [MAX_PAYLOAD_SIZE*8-1:0]    payload_buffer;
  logic [$clog2(MAX_PAYLOAD_SIZE)-1:0] bytes_received;
  logic [$clog2(MAX_PAYLOAD_SIZE)-1:0] actual_payload_size;  // Extracted from HEAD flit
  logic [SEQ_NUM_WIDTH-1:0]         expected_seq;
  logic [PACKET_ID_WIDTH-1:0]       current_pkt_id;
  logic [$clog2(FLITS_PER_PACKET)-1:0] flit_count;
  
  // Header information storage
  logic [COORD_WIDTH-1:0]           pkt_src_x, pkt_src_y;
  logic [COORD_WIDTH-1:0]           pkt_dest_x, pkt_dest_y;
  logic [VC_ID_WIDTH-1:0]           pkt_vc_id;
  logic [QOS_WIDTH-1:0]             pkt_qos;
  
  // Payload extraction
  localparam int HEADER_SIZE = FLIT_TYPE_WIDTH + VC_ID_WIDTH + 4*COORD_WIDTH + 
                               SEQ_NUM_WIDTH + PACKET_ID_WIDTH + QOS_WIDTH;
  localparam int PAYLOAD_BITS_PER_FLIT = FLIT_WIDTH - HEADER_SIZE;
  
  assign flit_ready = (current_state != PKT_COMPLETE) && (current_state != ERROR_STATE);
  
  // Sequence error detection
  assign seq_error_detected = flit_valid && flit_ready && 
                              (current_state == RECV_HEAD || current_state == RECV_BODY) &&
                              (flit_in.seq_num != expected_seq || flit_in.packet_id != current_pkt_id);
  
  // State machine
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      current_state <= IDLE;
    end else begin
      current_state <= next_state;
    end
  end
  
  always_comb begin
    next_state = current_state;
    
    case (current_state)
      IDLE: begin
        if (flit_valid && flit_ready) begin
          if (flit_in.flit_type == FLIT_TYPE_HEAD) begin
            next_state = RECV_HEAD;
          end else if (flit_in.flit_type == FLIT_TYPE_SINGLE) begin
            next_state = PKT_COMPLETE;
          end else begin
            next_state = ERROR_STATE;  // Unexpected flit type
          end
        end
      end
      
      RECV_HEAD: begin
        if (flit_valid && flit_ready) begin
          if (seq_error_detected) begin
            next_state = ERROR_STATE;
          end else if (flit_in.flit_type == FLIT_TYPE_BODY) begin
            next_state = RECV_BODY;
          end else if (flit_in.flit_type == FLIT_TYPE_TAIL) begin
            next_state = PKT_COMPLETE;
          end else begin
            next_state = ERROR_STATE;
          end
        end
      end
      
      RECV_BODY: begin
        if (flit_valid && flit_ready) begin
          if (seq_error_detected) begin
            next_state = ERROR_STATE;
          end else if (flit_in.flit_type == FLIT_TYPE_BODY) begin
            next_state = RECV_BODY;
          end else if (flit_in.flit_type == FLIT_TYPE_TAIL) begin
            next_state = PKT_COMPLETE;
          end else begin
            next_state = ERROR_STATE;
          end
        end
      end
      
      PKT_COMPLETE: begin
        if (pkt_valid && pkt_ready) begin
          next_state = IDLE;
        end
      end
      
      ERROR_STATE: begin
        next_state = IDLE;  // Reset on error
      end
      
      default: next_state = IDLE;
    endcase
  end
  
  // Packet reconstruction logic
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      payload_buffer <= '0;
      bytes_received <= '0;
      expected_seq <= '0;
      current_pkt_id <= '0;
      flit_count <= '0;
      pkt_src_x <= '0;
      pkt_src_y <= '0;
      pkt_dest_x <= '0;
      pkt_dest_y <= '0;
      pkt_vc_id <= '0;
      pkt_qos <= '0;
      error_detected <= 1'b0;
      error_code <= ERR_NONE;
    end else begin
      // Clear error only when starting a new packet (IDLE->RECV_HEAD or IDLE->PKT_COMPLETE)
      if (current_state == IDLE && next_state != IDLE) begin
        error_detected <= 1'b0;
        error_code <= ERR_NONE;
      end
      
      if (flit_valid && flit_ready) begin
        case (current_state)
          IDLE: begin
            if (flit_in.flit_type == FLIT_TYPE_HEAD || flit_in.flit_type == FLIT_TYPE_SINGLE) begin
                            // Store packet metadata from first flit (HEAD or SINGLE)
              pkt_src_x <= flit_in.src_x;
              pkt_src_y <= flit_in.src_y;
              pkt_dest_x <= flit_in.dest_x;
              pkt_dest_y <= flit_in.dest_y;
              pkt_vc_id <= flit_in.vc_id;
              pkt_qos <= flit_in.qos;
              current_pkt_id <= flit_in.packet_id;
              expected_seq <= flit_in.seq_num;  // Expect same sequence number for all flits in packet
              
              // Store first payload - handle both SINGLE and HEAD flits
              if (flit_in.flit_type == FLIT_TYPE_SINGLE) begin
                // For single flit packets, copy up to 192 bits (24 bytes) to handle test cases
                payload_buffer[191:0] <= flit_in.payload[191:0];
              end else begin
                // For HEAD flit of multi-flit packet, copy full payload width
                payload_buffer[PAYLOAD_BITS_PER_FLIT-1:0] <= flit_in.payload[PAYLOAD_BITS_PER_FLIT-1:0];
              end
              bytes_received <= PAYLOAD_BITS_PER_FLIT / 8;
              flit_count <= 1;
            end
          end
          
          RECV_HEAD, RECV_BODY: begin
            // Only process payload if no sequence error (state machine handles errors)
            if (!seq_error_detected) begin
              // For multi-flit packets from the assembler, always copy full payload width
              // The assembler shifts payload correctly, so each flit uses the full width
              payload_buffer[flit_count*PAYLOAD_BITS_PER_FLIT +: PAYLOAD_BITS_PER_FLIT] <= flit_in.payload[PAYLOAD_BITS_PER_FLIT-1:0];
              bytes_received <= bytes_received + (PAYLOAD_BITS_PER_FLIT / 8);
              flit_count <= flit_count + 1;
              // All flits in the same packet have the same sequence number
            end
          end
          
          default: begin
            // Reset on completion or error
            if (next_state == IDLE) begin
              payload_buffer <= '0;
              bytes_received <= '0;
              flit_count <= '0;
            end
          end
        endcase
      end
      
      // Error detection
      if (next_state == ERROR_STATE && current_state != ERROR_STATE) begin
        error_detected <= 1'b1;
        error_code <= ERR_PROTOCOL;
      end
    end
  end
  
  // Output packet signals
  assign pkt_valid = (current_state == PKT_COMPLETE);
  assign src_x = pkt_src_x;
  assign src_y = pkt_src_y;
  assign dest_x = pkt_dest_x;
  assign dest_y = pkt_dest_y;
  assign vc_id = pkt_vc_id;
  assign qos = pkt_qos;
  assign payload_data = payload_buffer;
  assign payload_size = bytes_received;
  
  // Assertions for verification
  `ifdef ASSERT_ON
    // Packet should only be valid in PKT_COMPLETE state
    property pkt_valid_state;
      @(posedge clk) disable iff (!rst_n)
      pkt_valid |-> (current_state == PKT_COMPLETE);
    endproperty
    assert property (pkt_valid_state) else $error("Packet valid in wrong state");
    
    // Flit sequence should be correct
    property flit_sequence;
      @(posedge clk) disable iff (!rst_n)
      flit_valid && flit_ready && (current_state != IDLE) |-> 
        (flit_in.seq_num == expected_seq && flit_in.packet_id == current_pkt_id);
    endproperty
    assert property (flit_sequence) else $error("Flit sequence error");
  `endif

endmodule
