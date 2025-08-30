/**
 * Nebula GPU Interconnect Package
 * 
 * This package contains all the constants, structures, and type definitions
 * for the Nebula scalable GPU interconnect system.
 * 
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: August 2025
 */

package nebula_pkg;

  // =============================================================================
  // NETWORK TOPOLOGY PARAMETERS
  // =============================================================================
  
  // Mesh dimensions (parameterizable for scaling)
  parameter int MESH_SIZE_X_DEFAULT = 4;
  parameter int MESH_SIZE_Y_DEFAULT = 4;
  parameter int MAX_MESH_SIZE = 8;
  
  // Router port configuration
  parameter int NUM_PORTS = 5;  // N, S, E, W, Local
  parameter int PORT_NORTH = 0;
  parameter int PORT_SOUTH = 1;
  parameter int PORT_EAST  = 2;
  parameter int PORT_WEST  = 3;
  parameter int PORT_LOCAL = 4;

  // =============================================================================
  // FLIT AND PACKET PARAMETERS
  // =============================================================================
  
  // Flit structure (256-bit for GPU workloads)
  parameter int FLIT_WIDTH = 256;
  parameter int FLIT_TYPE_WIDTH = 2;
  parameter int FLIT_VC_WIDTH = 2;
  
  // Address and coordinate widths
  parameter int COORD_WIDTH = 4;    // Supports up to 16x16 mesh
  parameter int ADDR_WIDTH = 64;    // 64-bit addressing
  parameter int NODE_ID_WIDTH = 6;  // Up to 64 nodes
  
  // Packet structure  
  parameter int SEQ_NUM_WIDTH = 16;
  parameter int PACKET_ID_WIDTH = 8;
  parameter int CRC_WIDTH = 32;     // Strong error detection
  parameter int FLITS_PER_PACKET = 8;  // Maximum flits per packet (128 bytes)
  parameter int PAYLOAD_BITS_PER_FLIT = FLIT_WIDTH - 48;  // 208 bits payload per flit
  parameter int HEADER_SIZE = 48;   // Header size in bits

  // =============================================================================
  // VIRTUAL CHANNEL PARAMETERS  
  // =============================================================================
  
  // VC configuration (based on CHI message classes)
  parameter int NUM_VCS = 4;
  parameter int VC_ID_WIDTH = 2;
  parameter int VC_DEPTH = 16;      // 16 flits per VC (industry standard)
  parameter int VC_PTR_WIDTH = $clog2(VC_DEPTH);
  
  // VC assignment for CHI protocol
  parameter int VC_REQ = 0;    // Requests
  parameter int VC_RSP = 1;    // Responses  
  parameter int VC_SNP = 2;    // Snoops
  parameter int VC_DAT = 3;    // Data

  // =============================================================================
  // BUFFER AND FLOW CONTROL
  // =============================================================================
  
  // Credit-based flow control
  parameter int CREDIT_WIDTH = $clog2(VC_DEPTH + 1);
  parameter int TOTAL_BUFFER_DEPTH = NUM_VCS * VC_DEPTH;
  
  // Pipeline parameters
  parameter int ROUTER_PIPELINE_DEPTH = 5;  // BW-RC-VA-SA-ST
  
  // Timeout and retry parameters
  parameter int TIMEOUT_WIDTH = 16;
  parameter int MAX_RETRIES = 4;

  // =============================================================================
  // PROTOCOL INTERFACE PARAMETERS
  // =============================================================================
  
  // AXI4 parameters (GPU-optimized)
  parameter int AXI_ID_WIDTH = 8;      // 256 outstanding transactions
  parameter int AXI_ADDR_WIDTH = 64;   // 64-bit addressing
  parameter int AXI_DATA_WIDTH = 512;  // 512-bit for GPU bandwidth
  parameter int AXI_STRB_WIDTH = AXI_DATA_WIDTH/8;
  parameter int AXI_MAX_BURST_LEN = 256;
  
  // CHI parameters
  parameter int CHI_NODE_ID_WIDTH = 6;    // 64 nodes max
  parameter int CHI_REQ_ADDR_WIDTH = 64;
  parameter int CHI_DATA_WIDTH = 512;     // Cache line width
  parameter int CHI_BE_WIDTH = CHI_DATA_WIDTH/8;
  parameter int CHI_CACHE_LINE_SIZE = 64; // 64-byte cache lines

  // =============================================================================
  // PERFORMANCE AND QOS PARAMETERS
  // =============================================================================
  
  // QoS traffic classes
  parameter int QOS_WIDTH = 4;
  parameter int QOS_URGENT = 4'hF;
  parameter int QOS_HIGH = 4'hC;
  parameter int QOS_NORMAL = 4'h8;
  parameter int QOS_LOW = 4'h4;
  
  // Performance monitoring
  parameter int PERF_COUNTER_WIDTH = 32;
  parameter int LATENCY_COUNTER_WIDTH = 16;

  // =============================================================================
  // FLIT TYPE DEFINITIONS
  // =============================================================================
  
  typedef enum logic [FLIT_TYPE_WIDTH-1:0] {
    FLIT_TYPE_HEAD   = 2'b00,
    FLIT_TYPE_BODY   = 2'b01, 
    FLIT_TYPE_TAIL   = 2'b10,
    FLIT_TYPE_SINGLE = 2'b11
  } flit_type_e;

  // Alternative names for compatibility
  parameter logic [FLIT_TYPE_WIDTH-1:0] FLIT_HEAD = FLIT_TYPE_HEAD;
  parameter logic [FLIT_TYPE_WIDTH-1:0] FLIT_BODY = FLIT_TYPE_BODY;  
  parameter logic [FLIT_TYPE_WIDTH-1:0] FLIT_TAIL = FLIT_TYPE_TAIL;
  parameter logic [FLIT_TYPE_WIDTH-1:0] FLIT_HEAD_TAIL = FLIT_TYPE_SINGLE;
  parameter logic [FLIT_TYPE_WIDTH-1:0] FLIT_SINGLE = FLIT_TYPE_SINGLE;

  // =============================================================================
  // NOC PACKET HEADER STRUCTURE
  // =============================================================================
  
  typedef struct packed {
    logic [FLIT_TYPE_WIDTH-1:0]    flit_type;
    logic [VC_ID_WIDTH-1:0]        vc_id;
    logic [COORD_WIDTH-1:0]        dest_x;
    logic [COORD_WIDTH-1:0]        dest_y;
    logic [COORD_WIDTH-1:0]        src_x;
    logic [COORD_WIDTH-1:0]        src_y;
    logic [SEQ_NUM_WIDTH-1:0]      seq_num;
    logic [PACKET_ID_WIDTH-1:0]    packet_id;
    logic [QOS_WIDTH-1:0]          qos;
    logic [FLIT_WIDTH-48-1:0]      payload;  // Remaining bits for payload (208 bits)
  } noc_flit_t;

  // Simplified flit type for testbenches
  typedef noc_flit_t flit_t;

  // =============================================================================
  // PACKET TYPE DEFINITIONS
  // =============================================================================
  
  typedef enum logic [3:0] {
    PKT_READ_REQ    = 4'h0,
    PKT_WRITE_REQ   = 4'h1, 
    PKT_READ_RESP   = 4'h2,
    PKT_WRITE_RESP  = 4'h3,
    PKT_READ_DATA   = 4'h4,
    PKT_WRITE_DATA  = 4'h5,
    PKT_SNOOP       = 4'h6,
    PKT_ACK         = 4'h7
  } packet_type_e;
  
  typedef struct packed {
    packet_type_e                   packet_type;
    logic [COORD_WIDTH-1:0]         dest_x;
    logic [COORD_WIDTH-1:0]         dest_y;
    logic [COORD_WIDTH-1:0]         src_x;
    logic [COORD_WIDTH-1:0]         src_y;
    logic [VC_ID_WIDTH-1:0]         vc_id;
    logic [ADDR_WIDTH-1:0]          address;
    logic [PACKET_ID_WIDTH-1:0]     packet_id;
    logic [QOS_WIDTH-1:0]           qos;
    logic [FLIT_WIDTH*8-1:0]        data;  // Up to 8 flits worth of data
    logic [$clog2(8):0]             data_length;  // Number of flits
  } packet_t;

  // =============================================================================
  // AXI4 TRANSACTION STRUCTURES
  // =============================================================================
  
  typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]     id;
    logic [AXI_ADDR_WIDTH-1:0]   addr;
    logic [7:0]                  len;      // Burst length
    logic [2:0]                  size;     // Burst size
    logic [1:0]                  burst;    // Burst type
    logic [QOS_WIDTH-1:0]        qos;
    logic                        valid;
  } axi_aw_t;
  
  typedef struct packed {
    logic [AXI_DATA_WIDTH-1:0]   data;
    logic [AXI_STRB_WIDTH-1:0]   strb;
    logic                        last;
    logic                        valid;
  } axi_w_t;
  
  typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]     id;
    logic [AXI_ADDR_WIDTH-1:0]   addr;
    logic [7:0]                  len;
    logic [2:0]                  size;
    logic [1:0]                  burst;
    logic [QOS_WIDTH-1:0]        qos;
    logic                        valid;
  } axi_ar_t;
  
  typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]     id;
    logic [AXI_DATA_WIDTH-1:0]   data;
    logic [1:0]                  resp;
    logic                        last;
    logic                        valid;
  } axi_r_t;
  
  typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]     id;
    logic [1:0]                  resp;
    logic                        valid;
  } axi_b_t;

  // =============================================================================
  // CHI TRANSACTION STRUCTURES  
  // =============================================================================
  
  typedef enum logic [5:0] {
    // Request opcodes
    CHI_ReadShared     = 6'h01,
    CHI_ReadClean      = 6'h02, 
    CHI_ReadOnce       = 6'h03,
    CHI_ReadUnique     = 6'h07,
    CHI_WriteBackFull  = 6'h08,
    CHI_WriteEvictFull = 6'h0A,
    CHI_WriteUniquePtl = 6'h18,
    CHI_WriteUniqueFull = 6'h19
  } chi_opcode_e;
  
  typedef struct packed {
    logic [CHI_NODE_ID_WIDTH-1:0] src_id;
    logic [CHI_NODE_ID_WIDTH-1:0] tgt_id;
    logic [7:0]                   txn_id;
    chi_opcode_e                  opcode;
    logic [CHI_REQ_ADDR_WIDTH-1:0] addr;
    logic [2:0]                   size;
    logic [QOS_WIDTH-1:0]         qos;
  } chi_req_t;
  
  // CHI coherency states
  typedef enum logic [2:0] {
    CHI_INVALID      = 3'b000,  // I
    CHI_UNIQUE_CLEAN = 3'b001,  // UC
    CHI_UNIQUE_DIRTY = 3'b010,  // UD
    CHI_SHARED_CLEAN = 3'b011,  // SC
    CHI_SHARED_DIRTY = 3'b100   // SD
  } chi_state_e;

  // =============================================================================
  // ERROR CODES AND DEBUG
  // =============================================================================
  
  typedef enum logic [7:0] {
    ERR_NONE           = 8'h00,
    ERR_CRC_MISMATCH   = 8'h01,
    ERR_TIMEOUT        = 8'h02,
    ERR_BUFFER_OVERFLOW = 8'h03,
    ERR_INVALID_DEST   = 8'h04,
    ERR_VC_DEADLOCK    = 8'h05,
    ERR_PROTOCOL       = 8'h06
  } error_code_e;
  
  // Debug register addresses
  parameter logic [15:0] DBG_STATUS_REG = 16'h0000;
  parameter logic [15:0] DBG_ERROR_REG  = 16'h0004;
  parameter logic [15:0] DBG_PERF_REG   = 16'h0008;

  // =============================================================================
  // UTILITY FUNCTIONS
  // =============================================================================
  
  // Calculate Manhattan distance between two coordinates
  function automatic int manhattan_distance(
    input logic [COORD_WIDTH-1:0] x1, y1, x2, y2
  );
    return (x1 > x2 ? x1 - x2 : x2 - x1) + (y1 > y2 ? y1 - y2 : y2 - y1);
  endfunction
  
  // Check if coordinates are valid for given mesh size
  function automatic bit coord_valid(
    input logic [COORD_WIDTH-1:0] x, y,
    input int mesh_x, mesh_y
  );
    return (x < mesh_x) && (y < mesh_y);
  endfunction

endpackage
