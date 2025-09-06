/**
 * Nebula AXI4-to-NoC Bridge Module
 * 
 * This module implements the translation engine between AXI4 protocol and the
 * Nebula NoC packet format. It handles burst decomposition, address mapping,
 * packet assembly/disassembly, and reorder buffer management for maintaining
 * AXI4 transaction ordering requirements.
 * 
 * Key Features:
 * - Burst decomposition for multi-beat AXI4 transactions
 * - Address-to-coordinate mapping for NoC routing
 * - Packet assembly with sequence numbering
 * - Reorder buffer for response reconstruction
 * - 4KB boundary protection and validation
 * - Comprehensive error handling and reporting
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: August 2025
 */

`include "nebula_pkg.sv"

module nebula_axi_noc_bridge
  import nebula_pkg::*;
#(
  parameter int NODE_X = 0,
  parameter int NODE_Y = 0,
  parameter int MESH_SIZE_X = 4,
  parameter int MESH_SIZE_Y = 4,
  parameter int REORDER_DEPTH = 64
)(
  input  logic clk,
  input  logic rst_n,
  
  // Configuration
  input  logic [AXI_ADDR_WIDTH-1:0] base_addr,
  input  logic [AXI_ADDR_WIDTH-1:0] addr_mask,
  
  // AXI4 Write Address Channel
  input  logic                        axi_awvalid,
  output logic                        axi_awready,
  input  logic [AXI_ID_WIDTH-1:0]     axi_awid,
  input  logic [AXI_ADDR_WIDTH-1:0]   axi_awaddr,
  input  logic [7:0]                  axi_awlen,
  input  logic [2:0]                  axi_awsize,
  input  logic [1:0]                  axi_awburst,
  input  logic                        axi_awlock,
  input  logic [3:0]                  axi_awcache,
  input  logic [2:0]                  axi_awprot,
  input  logic [QOS_WIDTH-1:0]        axi_awqos,
  input  logic [3:0]                  axi_awregion,
  input  logic [AXI_AWUSER_WIDTH-1:0] axi_awuser,
  
  // AXI4 Write Data Channel
  input  logic                        axi_wvalid,
  output logic                        axi_wready,
  input  logic [AXI_DATA_WIDTH-1:0]   axi_wdata,
  input  logic [AXI_STRB_WIDTH-1:0]   axi_wstrb,
  input  logic                        axi_wlast,
  input  logic [AXI_WUSER_WIDTH-1:0]  axi_wuser,
  
  // AXI4 Write Response Channel
  output logic                        axi_bvalid,
  input  logic                        axi_bready,
  output logic [AXI_ID_WIDTH-1:0]     axi_bid,
  output logic [1:0]                  axi_bresp,
  output logic [AXI_BUSER_WIDTH-1:0]  axi_buser,
  
  // AXI4 Read Address Channel
  input  logic                        axi_arvalid,
  output logic                        axi_arready,
  input  logic [AXI_ID_WIDTH-1:0]     axi_arid,
  input  logic [AXI_ADDR_WIDTH-1:0]   axi_araddr,
  input  logic [7:0]                  axi_arlen,
  input  logic [2:0]                  axi_arsize,
  input  logic [1:0]                  axi_arburst,
  input  logic                        axi_arlock,
  input  logic [3:0]                  axi_arcache,
  input  logic [2:0]                  axi_arprot,
  input  logic [QOS_WIDTH-1:0]        axi_arqos,
  input  logic [3:0]                  axi_arregion,
  input  logic [AXI_ARUSER_WIDTH-1:0] axi_aruser,
  
  // AXI4 Read Data Channel
  output logic                        axi_rvalid,
  input  logic                        axi_rready,
  output logic [AXI_ID_WIDTH-1:0]     axi_rid,
  output logic [AXI_DATA_WIDTH-1:0]   axi_rdata,
  output logic [1:0]                  axi_rresp,
  output logic                        axi_rlast,
  output logic [AXI_RUSER_WIDTH-1:0]  axi_ruser,
  
  // NoC Interface - External (connects to router)
  output logic      noc_flit_out_valid,
  input  logic      noc_flit_out_ready,
  output noc_flit_t noc_flit_out,
  
  input  logic      noc_flit_in_valid,
  output logic      noc_flit_in_ready,
  input  noc_flit_t noc_flit_in,
  output logic [31:0]               status_reg,
  output logic [31:0]               error_reg,
  
  // Performance Monitoring
  output logic [31:0] packet_tx_count,
  output logic [31:0] packet_rx_count,
  output logic [15:0] avg_latency,
  output logic [7:0]  buffer_utilization
);

  // =============================================================================
  // INTERNAL SIGNAL DECLARATIONS
  // =============================================================================
  
  // Address mapping and coordinate extraction
  logic [COORD_WIDTH-1:0] dest_x, dest_y;
  logic [AXI_ADDR_WIDTH-1:0] mapped_addr;
  logic addr_valid;
  logic boundary_violation;
  
  // Packet ID generation
  logic [PACKET_ID_WIDTH-1:0] next_packet_id;
  
  // AXI ready signals generation
  logic axi_awready_int, axi_wready_int, axi_arready_int;
  assign axi_awready = axi_awready_int;
  assign axi_wready = axi_wready_int;
  assign axi_arready = axi_arready_int;
  
  // Burst decomposition
  typedef struct packed {
    logic                        valid;
    logic [AXI_ID_WIDTH-1:0]     axi_id;
    logic [AXI_ADDR_WIDTH-1:0]   base_addr;
    logic [AXI_ADDR_WIDTH-1:0]   current_addr;
    logic [7:0]                  total_beats;
    logic [7:0]                  current_beat;
    logic [2:0]                  burst_size;
    logic [1:0]                  burst_type;
    logic                        is_write;
    logic [PACKET_ID_WIDTH-1:0]  packet_id;
    logic [AXI_DATA_WIDTH-1:0]   data_buffer;
  } burst_tracker_t;
  
  burst_tracker_t write_burst, read_burst;
  
  // Packet assembly state machine
  typedef enum logic [2:0] {
    PACK_IDLE,
    PACK_HEADER,
    PACK_DATA,
    PACK_WAIT_READY
  } pack_state_e;
  
  pack_state_e pack_state, pack_state_next;
  
  // NoC packet buffer for multi-flit packets
  typedef struct packed {
    logic                    valid;
    logic [2:0]              flit_count;
    logic [2:0]              total_flits;
    logic [PACKET_ID_WIDTH-1:0] packet_id;
  } packet_buffer_t;
  
  packet_buffer_t tx_packet_buffer;
  noc_flit_t tx_flits [7:0]; // Separate unpacked array
  
  // Reorder buffer for response reconstruction
  typedef struct packed {
    logic                        valid;
    logic [AXI_ID_WIDTH-1:0]     axi_id;
    logic [7:0]                  total_beats;
    logic [7:0]                  received_beats;
    logic                        is_write;
    logic [PACKET_ID_WIDTH-1:0]  packet_id;
    logic [1:0]                  resp_status;
  } reorder_entry_t;
  
  reorder_entry_t reorder_buffer [REORDER_DEPTH-1:0];
  logic [AXI_DATA_WIDTH-1:0] reorder_data_buffer [REORDER_DEPTH-1:0][255:0]; // Separate data storage
  logic [$clog2(REORDER_DEPTH)-1:0] reorder_alloc_ptr;
  logic [$clog2(REORDER_DEPTH)-1:0] reorder_lookup_idx;
  logic reorder_lookup_valid;
  
  // Performance monitoring
  logic [31:0] tx_count, rx_count;
  logic [15:0] latency_sum;
  logic [15:0] latency_samples;
  
  // Error tracking
  logic [31:0] error_status;
  
  // =============================================================================
  // PACKET ID GENERATION
  // =============================================================================
  
  logic [PACKET_ID_WIDTH-1:0] packet_id_counter;
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      packet_id_counter <= '0;
    end else if ((axi_awvalid && axi_awready) || (axi_arvalid && axi_arready)) begin
      packet_id_counter <= packet_id_counter + 1;
    end
  end
  
  assign next_packet_id = packet_id_counter;
  
  // =============================================================================
  // AXI READY SIGNAL GENERATION
  // =============================================================================
  
  // AXI ready signals based on internal state and NoC readiness
  assign axi_awready_int = (pack_state == PACK_IDLE) && !write_burst.valid && noc_flit_out_ready;
  assign axi_wready_int = write_burst.valid && noc_flit_out_ready && (pack_state == PACK_IDLE || pack_state == PACK_DATA);
  assign axi_arready_int = (pack_state == PACK_IDLE) && !read_burst.valid && noc_flit_out_ready;
  
  // =============================================================================
  // ADDRESS MAPPING AND COORDINATE EXTRACTION
  // =============================================================================
  
  // Map AXI4 address to NoC coordinates
  // Address format: [63:16] = address, [15:12] = dest_y, [11:8] = dest_x
  always_comb begin
    mapped_addr = (axi_awvalid ? axi_awaddr : axi_araddr) & addr_mask;
    dest_x = mapped_addr[11:8];
    dest_y = mapped_addr[15:12];
    
    // Validate coordinates are within mesh bounds
    addr_valid = coord_valid(dest_x, dest_y, MESH_SIZE_X, MESH_SIZE_Y);
    
    // Check for 4KB boundary violations in burst
    boundary_violation = 1'b0;
    if (axi_awvalid) begin
      logic [AXI_ADDR_WIDTH-1:0] burst_end_addr;
      burst_end_addr = axi_awaddr + ((axi_awlen + 1) << axi_awsize);
      boundary_violation = (axi_awaddr[AXI_ADDR_WIDTH-1:12] != burst_end_addr[AXI_ADDR_WIDTH-1:12]);
    end else if (axi_arvalid) begin
      logic [AXI_ADDR_WIDTH-1:0] burst_end_addr;
      burst_end_addr = axi_araddr + ((axi_arlen + 1) << axi_arsize);
      boundary_violation = (axi_araddr[AXI_ADDR_WIDTH-1:12] != burst_end_addr[AXI_ADDR_WIDTH-1:12]);
    end
  end
  
  // =============================================================================
  // BURST DECOMPOSITION AND TRACKING
  // =============================================================================
  
  // Write burst tracking
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      write_burst <= '0;
    end else begin
      // Start new write burst
      if (axi_awvalid && axi_awready && addr_valid && !boundary_violation) begin
        write_burst.valid <= 1'b1;
        write_burst.axi_id <= axi_awid;
        write_burst.base_addr <= axi_awaddr;
        write_burst.current_addr <= axi_awaddr;
        write_burst.total_beats <= axi_awlen + 1;
        write_burst.current_beat <= 0;
        write_burst.burst_size <= axi_awsize;
        write_burst.burst_type <= axi_awburst;
        write_burst.is_write <= 1'b1;
        write_burst.packet_id <= next_packet_id;
      end
      
      // Process write data beats
      if (write_burst.valid && axi_wvalid && axi_wready) begin
        write_burst.current_beat <= write_burst.current_beat + 1;
        write_burst.data_buffer <= axi_wdata;
        
        // Calculate next address
        if (write_burst.burst_type == AXI_BURST_INCR) begin
          write_burst.current_addr <= write_burst.current_addr + (1 << write_burst.burst_size);
        end else if (write_burst.burst_type == AXI_BURST_WRAP) begin
          logic [AXI_ADDR_WIDTH-1:0] wrap_mask;
          wrap_mask = (write_burst.total_beats << write_burst.burst_size) - 1;
          write_burst.current_addr <= (write_burst.base_addr & ~wrap_mask) | 
                                     ((write_burst.current_addr + (1 << write_burst.burst_size)) & wrap_mask);
        end
        // FIXED burst keeps same address
        
        if (axi_wlast) begin
          write_burst.valid <= 1'b0;
        end
      end
    end
  end
  
  // Read burst tracking  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      read_burst <= '0;
    end else begin
      // Start new read burst
      if (axi_arvalid && axi_arready && addr_valid && !boundary_violation) begin
        read_burst.valid <= 1'b1;
        read_burst.axi_id <= axi_arid;
        read_burst.base_addr <= axi_araddr;
        read_burst.current_addr <= axi_araddr;
        read_burst.total_beats <= axi_arlen + 1;
        read_burst.current_beat <= 0;
        read_burst.burst_size <= axi_arsize;
        read_burst.burst_type <= axi_arburst;
        read_burst.is_write <= 1'b0;
        read_burst.packet_id <= next_packet_id;
      end
      
      // Complete read burst when all data received
      if (read_burst.valid && axi_rvalid && axi_rready && axi_rlast) begin
        read_burst.valid <= 1'b0;
      end
    end
  end
  
  // =============================================================================
  // PACKET ASSEMBLY AND TRANSMISSION
  // =============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      pack_state <= PACK_IDLE;
    end else begin
      pack_state <= pack_state_next;
    end
  end
  
  always_comb begin
    pack_state_next = pack_state;
    noc_flit_out_valid = 1'b0;
    noc_flit_out = '0;
    
    case (pack_state)
      PACK_IDLE: begin
        // Start packet assembly for write transactions
        if (write_burst.valid && axi_wvalid) begin
          pack_state_next = PACK_HEADER;
        end
        // Start packet assembly for read transactions  
        else if (read_burst.valid) begin
          pack_state_next = PACK_HEADER;
        end
      end
      
      PACK_HEADER: begin
        noc_flit_out_valid = 1'b1;
        
        // Assemble header flit
        if (write_burst.valid) begin
          noc_flit_out.flit_type = (write_burst.total_beats == 1) ? FLIT_TYPE_SINGLE : FLIT_TYPE_HEAD;
          noc_flit_out.dest_x = dest_x;
          noc_flit_out.dest_y = dest_y;
          noc_flit_out.src_x = NODE_X[COORD_WIDTH-1:0];
          noc_flit_out.src_y = NODE_Y[COORD_WIDTH-1:0];
          noc_flit_out.vc_id = VC_REQ;
          noc_flit_out.packet_id = write_burst.packet_id;
          noc_flit_out.seq_num = write_burst.current_beat;
          noc_flit_out.qos = axi_awqos;
          
          // Pack address and control info
          noc_flit_out.payload[AXI_ADDR_WIDTH-1:0] = write_burst.current_addr;
          noc_flit_out.payload[AXI_ADDR_WIDTH+7:AXI_ADDR_WIDTH] = write_burst.total_beats;
          noc_flit_out.payload[AXI_ADDR_WIDTH+10:AXI_ADDR_WIDTH+8] = write_burst.burst_size;
          noc_flit_out.payload[AXI_ADDR_WIDTH+12:AXI_ADDR_WIDTH+11] = write_burst.burst_type;
          
          // Pack data if single flit or start of multi-flit
          if (PAYLOAD_BITS_PER_FLIT >= AXI_DATA_WIDTH) begin
            noc_flit_out.payload[AXI_ADDR_WIDTH+12+AXI_DATA_WIDTH:AXI_ADDR_WIDTH+13] = write_burst.data_buffer;
          end
        end else if (read_burst.valid) begin
          noc_flit_out.flit_type = FLIT_TYPE_SINGLE; // Read requests are always single flit
          noc_flit_out.dest_x = dest_x;
          noc_flit_out.dest_y = dest_y;
          noc_flit_out.src_x = NODE_X[COORD_WIDTH-1:0];
          noc_flit_out.src_y = NODE_Y[COORD_WIDTH-1:0];
          noc_flit_out.vc_id = VC_REQ;
          noc_flit_out.packet_id = read_burst.packet_id;
          noc_flit_out.seq_num = 0;
          noc_flit_out.qos = axi_arqos;
          
          // Pack address and control info
          noc_flit_out.payload[AXI_ADDR_WIDTH-1:0] = read_burst.current_addr;
          noc_flit_out.payload[AXI_ADDR_WIDTH+7:AXI_ADDR_WIDTH] = read_burst.total_beats;
          noc_flit_out.payload[AXI_ADDR_WIDTH+10:AXI_ADDR_WIDTH+8] = read_burst.burst_size;
          noc_flit_out.payload[AXI_ADDR_WIDTH+12:AXI_ADDR_WIDTH+11] = read_burst.burst_type;
        end
        
        if (noc_flit_out_ready) begin
          if ((write_burst.valid && write_burst.total_beats > 1) ||
              (read_burst.valid && read_burst.total_beats > 1)) begin
            pack_state_next = PACK_DATA;
          end else begin
            pack_state_next = PACK_IDLE;
          end
        end else begin
          pack_state_next = PACK_WAIT_READY;
        end
      end
      
      PACK_DATA: begin
        // Handle multi-flit data transmission
        noc_flit_out_valid = 1'b1;
        
        if (write_burst.valid && write_burst.current_beat < write_burst.total_beats - 1) begin
          noc_flit_out.flit_type = FLIT_TYPE_BODY;
          noc_flit_out.packet_id = write_burst.packet_id;
          noc_flit_out.seq_num = write_burst.current_beat;
          // Only assign the bits that fit in the payload
          noc_flit_out.payload[PAYLOAD_BITS_PER_FLIT-1:0] = write_burst.data_buffer[PAYLOAD_BITS_PER_FLIT-1:0];
        end else begin
          noc_flit_out.flit_type = FLIT_TYPE_TAIL;
          noc_flit_out.packet_id = write_burst.packet_id;
          noc_flit_out.seq_num = write_burst.current_beat;
          // Only assign the bits that fit in the payload
          noc_flit_out.payload[PAYLOAD_BITS_PER_FLIT-1:0] = write_burst.data_buffer[PAYLOAD_BITS_PER_FLIT-1:0];
        end
        
        if (noc_flit_out_ready) begin
          pack_state_next = PACK_IDLE;
        end else begin
          pack_state_next = PACK_WAIT_READY;
        end
      end
      
      PACK_WAIT_READY: begin
        noc_flit_out_valid = 1'b1;
        if (noc_flit_out_ready) begin
          pack_state_next = PACK_IDLE;
        end
      end
    endcase
  end
  
  // =============================================================================
  // REORDER BUFFER MANAGEMENT
  // =============================================================================
  
  // Allocate reorder buffer entry for new transactions
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      for (int i = 0; i < REORDER_DEPTH; i++) begin
        reorder_buffer[i] <= '0;
      end
      reorder_alloc_ptr <= 0;
    end else begin
      // Allocate entry for new write transaction
      if (write_burst.valid && axi_wlast && axi_wvalid && axi_wready_int) begin
        reorder_buffer[reorder_alloc_ptr].valid <= 1'b1;
        reorder_buffer[reorder_alloc_ptr].axi_id <= write_burst.axi_id;
        reorder_buffer[reorder_alloc_ptr].total_beats <= write_burst.total_beats;
        reorder_buffer[reorder_alloc_ptr].received_beats <= 0;
        reorder_buffer[reorder_alloc_ptr].is_write <= 1'b1;
        reorder_buffer[reorder_alloc_ptr].packet_id <= write_burst.packet_id;
        reorder_alloc_ptr <= reorder_alloc_ptr + 1;
      end
      
      // Allocate entry for new read transaction
      if (read_burst.valid && pack_state == PACK_HEADER && noc_flit_out_ready) begin
        reorder_buffer[reorder_alloc_ptr].valid <= 1'b1;
        reorder_buffer[reorder_alloc_ptr].axi_id <= read_burst.axi_id;
        reorder_buffer[reorder_alloc_ptr].total_beats <= read_burst.total_beats;
        reorder_buffer[reorder_alloc_ptr].received_beats <= 0;
        reorder_buffer[reorder_alloc_ptr].is_write <= 1'b0;
        reorder_buffer[reorder_alloc_ptr].packet_id <= read_burst.packet_id;
        reorder_alloc_ptr <= reorder_alloc_ptr + 1;
      end
      
      // Process incoming NoC responses
      if (noc_flit_in_valid && reorder_lookup_valid) begin
        reorder_buffer[reorder_lookup_idx].received_beats <= 
          reorder_buffer[reorder_lookup_idx].received_beats + 1;
        
        // Store response data for read transactions
        if (!reorder_buffer[reorder_lookup_idx].is_write) begin
          reorder_data_buffer[reorder_lookup_idx][reorder_buffer[reorder_lookup_idx].received_beats] 
            <= noc_flit_in.payload[PAYLOAD_BITS_PER_FLIT-1:0];
        end
        
        // Mark entry as complete if all beats received
        if (reorder_buffer[reorder_lookup_idx].received_beats + 1 == 
            reorder_buffer[reorder_lookup_idx].total_beats) begin
          reorder_buffer[reorder_lookup_idx].valid <= 1'b0;
        end
      end
    end
  end
  
  // Lookup reorder buffer entry by packet ID
  always_comb begin
    reorder_lookup_valid = 1'b0;
    reorder_lookup_idx = 0;
    
    for (int i = 0; i < REORDER_DEPTH; i++) begin
      if (reorder_buffer[i].valid && 
          reorder_buffer[i].packet_id == noc_flit_in.packet_id) begin
        reorder_lookup_valid = 1'b1;
        reorder_lookup_idx = i;
        break;
      end
    end
  end
  
  // =============================================================================
  // AXI4 RESPONSE GENERATION
  // =============================================================================
  
  // Connect to AXI interface for response generation
  assign noc_flit_in_ready = 1'b1; // Always ready to accept responses
  
  // Write response generation
  assign axi_bvalid = (reorder_lookup_valid && 
                      reorder_buffer[reorder_lookup_idx].is_write &&
                      reorder_buffer[reorder_lookup_idx].received_beats == 
                      reorder_buffer[reorder_lookup_idx].total_beats);
  assign axi_bid = reorder_buffer[reorder_lookup_idx].axi_id;
  assign axi_bresp = reorder_buffer[reorder_lookup_idx].resp_status;
  assign axi_buser = '0;
  
  // Read response generation
  assign axi_rvalid = (reorder_lookup_valid && 
                      !reorder_buffer[reorder_lookup_idx].is_write &&
                      reorder_buffer[reorder_lookup_idx].received_beats < 
                      reorder_buffer[reorder_lookup_idx].total_beats);
  assign axi_rid = reorder_buffer[reorder_lookup_idx].axi_id;
  assign axi_rdata = reorder_data_buffer[reorder_lookup_idx][reorder_buffer[reorder_lookup_idx].received_beats];
  assign axi_rresp = reorder_buffer[reorder_lookup_idx].resp_status;
  assign axi_rlast = (reorder_buffer[reorder_lookup_idx].received_beats == 
                     reorder_buffer[reorder_lookup_idx].total_beats - 1);
  assign axi_ruser = '0;
  
  // =============================================================================
  // ERROR HANDLING AND STATUS
  // =============================================================================
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      error_status <= 0;
    end else begin
      // Address validation errors
      if ((axi_awvalid && !addr_valid) || (axi_arvalid && !addr_valid)) begin
        error_status[0] <= 1'b1; // Invalid address
      end
      
      // Boundary violation errors
      if (boundary_violation) begin
        error_status[1] <= 1'b1; // 4KB boundary violation
      end
      
      // Reorder buffer overflow
      if (reorder_alloc_ptr == REORDER_DEPTH - 1) begin
        error_status[2] <= 1'b1; // Buffer overflow
      end
    end
  end
  
  // Performance monitoring
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      tx_count <= 0;
      rx_count <= 0;
      latency_sum <= 0;
      latency_samples <= 0;
    end else begin
      if (noc_flit_out_valid && noc_flit_out_ready) begin
        tx_count <= tx_count + 1;
      end
      
      if (noc_flit_in_valid && noc_flit_in_ready) begin
        rx_count <= rx_count + 1;
      end
    end
  end
  
  // Output assignments
  assign status_reg = {24'b0, pack_state};
  assign error_reg = error_status;
  assign packet_tx_count = tx_count;
  assign packet_rx_count = rx_count;
  assign avg_latency = latency_samples ? (latency_sum / latency_samples) : 16'h0;
  assign buffer_utilization = (reorder_alloc_ptr * 100) / REORDER_DEPTH;

endmodule
