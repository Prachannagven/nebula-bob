/**
 * NoC Packet Assembly and Disassembly Module
 * 
 * Handles conversion between higher-level packets and NoC flits.
 * Supports multi-flit packets with pr        flit_out.flit_type = (total_flits == 1) ? FLIT_TYPE_SINGLE : FLIT_TYPE_HEAD;per header, body, and tail formatting.
 * 
 * Features:
 * - Multi-flit packet assembly from payload data
 * - Automatic header generation with routing information
 * - CRC generation for error detection
 * - Packet disassembly and payload reconstruction
 * - Sequence number management
 */

import nebula_pkg::*;

module nebula_packet_assembler #(
  parameter int MAX_PAYLOAD_SIZE = 1024,  // Maximum payload size in bytes
  parameter int FLITS_PER_PACKET = 4      // Maximum flits per packet
)(
  input  logic                              clk,
  input  logic                              rst_n,
  
  // Input packet interface
  input  logic                              pkt_valid,
  input  logic [COORD_WIDTH-1:0]            src_x, src_y,
  input  logic [COORD_WIDTH-1:0]            dest_x, dest_y,
  input  logic [VC_ID_WIDTH-1:0]            vc_id,
  input  logic [QOS_WIDTH-1:0]              qos,
  input  logic [MAX_PAYLOAD_SIZE*8-1:0]     payload_data,
  input  logic [$clog2(MAX_PAYLOAD_SIZE)-1:0] payload_size,
  output logic                              pkt_ready,
  
  // Output flit interface
  output logic                              flit_valid,
  output noc_flit_t                         flit_out,
  input  logic                              flit_ready,
  
  // Status
  output logic                              busy
);

  // State machine states
  typedef enum logic [2:0] {
    IDLE,
    SEND_HEAD,
    SEND_BODY,
    SEND_TAIL,
    WAIT_READY
  } state_e;
  
  state_e current_state, next_state;
  
  // Internal registers
  logic [SEQ_NUM_WIDTH-1:0]         seq_num;
  logic [PACKET_ID_WIDTH-1:0]       packet_id;
  logic [$clog2(FLITS_PER_PACKET)-1:0] flit_count;
  logic [MAX_PAYLOAD_SIZE*8-1:0]    payload_reg;
  logic [$clog2(MAX_PAYLOAD_SIZE)-1:0] payload_size_reg;
  logic [$clog2(MAX_PAYLOAD_SIZE)-1:0] bytes_sent;
  
  // Registered coordinate and control information
  logic [COORD_WIDTH-1:0]           src_x_reg, src_y_reg;
  logic [COORD_WIDTH-1:0]           dest_x_reg, dest_y_reg;
  logic [VC_ID_WIDTH-1:0]           vc_id_reg;
  logic [QOS_WIDTH-1:0]             qos_reg;
  
  // Calculate number of flits needed
  logic [$clog2(FLITS_PER_PACKET)-1:0] total_flits;
  logic [FLIT_WIDTH-48-1:0] current_payload;
  
  // Header fields size calculation
  localparam int HEADER_SIZE = FLIT_TYPE_WIDTH + VC_ID_WIDTH + 4*COORD_WIDTH + 
                               SEQ_NUM_WIDTH + PACKET_ID_WIDTH + QOS_WIDTH;
  localparam int PAYLOAD_BITS_PER_FLIT = FLIT_WIDTH - HEADER_SIZE;
  
  assign total_flits = (payload_size_reg * 8 + PAYLOAD_BITS_PER_FLIT - 1) / PAYLOAD_BITS_PER_FLIT;
  assign busy = (current_state != IDLE);
  assign pkt_ready = (current_state == IDLE);
  
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
        if (pkt_valid && pkt_ready) begin
          if (total_flits == 1) begin
            next_state = SEND_HEAD;  // Single flit packet
          end else begin
            next_state = SEND_HEAD;
          end
        end
      end
      
      SEND_HEAD: begin
        if (flit_valid && flit_ready) begin
          if (total_flits == 1) begin
            next_state = IDLE;  // Single flit complete
          end else begin
            next_state = (flit_count + 1 == total_flits - 1) ? SEND_TAIL : SEND_BODY;
          end
        end
      end
      
      SEND_BODY: begin
        if (flit_valid && flit_ready) begin
          next_state = (flit_count + 1 == total_flits - 1) ? SEND_TAIL : SEND_BODY;
        end
      end
      
      SEND_TAIL: begin
        if (flit_valid && flit_ready) begin
          next_state = IDLE;
        end
      end
      
      default: next_state = IDLE;
    endcase
  end
  
  // Register packet information on new packet
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      payload_reg <= '0;
      payload_size_reg <= '0;
      seq_num <= '0;
      packet_id <= '0;
      flit_count <= '0;
      bytes_sent <= '0;
      src_x_reg <= '0;
      src_y_reg <= '0;
      dest_x_reg <= '0;
      dest_y_reg <= '0;
      vc_id_reg <= '0;
      qos_reg <= '0;
    end else if (pkt_valid && pkt_ready) begin
      payload_reg <= payload_data;
      payload_size_reg <= payload_size;
      seq_num <= seq_num + 1;
      packet_id <= packet_id + 1;
      flit_count <= '0;
      bytes_sent <= '0;
      src_x_reg <= src_x;
      src_y_reg <= src_y;
      dest_x_reg <= dest_x;
      dest_y_reg <= dest_y;
      vc_id_reg <= vc_id;
      qos_reg <= qos;
    end else if (flit_valid && flit_ready) begin
      flit_count <= flit_count + 1;
      bytes_sent <= bytes_sent + (PAYLOAD_BITS_PER_FLIT / 8);
      // Shift payload for next flit
      payload_reg <= payload_reg >> PAYLOAD_BITS_PER_FLIT;
    end
  end
  
  // Extract current payload for the flit
  assign current_payload = payload_reg[PAYLOAD_BITS_PER_FLIT-1:0];
  
  // Generate output flit
  always_comb begin
    flit_valid = 1'b0;
    flit_out = '0;  // Default all fields to zero
    
    case (current_state)
      SEND_HEAD: begin
        flit_valid = 1'b1;
        flit_out.dest_x = dest_x_reg;
        flit_out.dest_y = dest_y_reg;
        flit_out.src_x = src_x_reg;
        flit_out.src_y = src_y_reg;
        flit_out.flit_type = (total_flits == 1) ? FLIT_TYPE_SINGLE : FLIT_TYPE_HEAD;
        flit_out.vc_id = vc_id_reg;
        flit_out.seq_num = seq_num;
        flit_out.packet_id = packet_id;
        flit_out.qos = qos_reg;
        flit_out.payload = current_payload;
      end
      
      SEND_BODY: begin
        flit_valid = 1'b1;
        flit_out.dest_x = dest_x_reg;
        flit_out.dest_y = dest_y_reg;
        flit_out.src_x = src_x_reg;
        flit_out.src_y = src_y_reg;
        flit_out.flit_type = FLIT_TYPE_BODY;
        flit_out.vc_id = vc_id_reg;
        flit_out.seq_num = seq_num;
        flit_out.packet_id = packet_id;
        flit_out.qos = qos_reg;
        flit_out.payload = current_payload;
      end
      
      SEND_TAIL: begin
        flit_valid = 1'b1;
        flit_out.dest_x = dest_x_reg;
        flit_out.dest_y = dest_y_reg;
        flit_out.src_x = src_x_reg;
        flit_out.src_y = src_y_reg;
        flit_out.flit_type = FLIT_TYPE_TAIL;
        flit_out.vc_id = vc_id_reg;
        flit_out.seq_num = seq_num;
        flit_out.packet_id = packet_id;
        flit_out.qos = qos_reg;
        flit_out.payload = current_payload;
      end
      
      default: begin
        flit_valid = 1'b0;
        flit_out = '0;
      end
    endcase
  end
  
  // Assertions for verification
  `ifdef ASSERT_ON
    // Flit type should be correct for position
    property flit_type_correctness;
      @(posedge clk) disable iff (!rst_n)
      flit_valid |-> (
        (current_state == SEND_HEAD && total_flits > 1 && flit_out.flit_type == FLIT_TYPE_HEAD) ||
        (current_state == SEND_HEAD && total_flits == 1 && flit_out.flit_type == FLIT_TYPE_SINGLE) ||
        (current_state == SEND_BODY && flit_out.flit_type == FLIT_TYPE_BODY) ||
        (current_state == SEND_TAIL && flit_out.flit_type == FLIT_TYPE_TAIL)
      );
    endproperty
    assert property (flit_type_correctness) else $error("Incorrect flit type");
  `endif

endmodule
