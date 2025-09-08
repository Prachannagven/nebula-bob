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
  parameter int MESH_SIZE_X_DEFAULT = 8;
  parameter int MESH_SIZE_Y_DEFAULT = 8;
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
  parameter int AXI_AWUSER_WIDTH = 8;
  parameter int AXI_WUSER_WIDTH = 8;
  parameter int AXI_BUSER_WIDTH = 8;
  parameter int AXI_ARUSER_WIDTH = 8;
  parameter int AXI_RUSER_WIDTH = 8;
  
  // CHI parameters
  parameter int CHI_NODE_ID_WIDTH = 6;    // 64 nodes max
  parameter int CHI_REQ_ADDR_WIDTH = 64;
  parameter int CHI_DATA_WIDTH = 512;     // Cache line width
  parameter int CHI_BE_WIDTH = CHI_DATA_WIDTH/8;
  parameter int CHI_CACHE_LINE_SIZE = 64; // 64-byte cache lines
  parameter int CHI_TXN_ID_WIDTH = 8;     // Transaction ID width
  parameter int CHI_DBID_WIDTH = 8;       // Data buffer ID width
  parameter int CHI_RSVDC_WIDTH = 4;      // Reserved field width

  // =============================================================================
  // CHI PROTOCOL DEFINITIONS
  // =============================================================================
  
  // CHI Cache States (MOESI + others)
  typedef enum logic [2:0] {
    CHI_INVALID     = 3'b000,  // I - Invalid
    CHI_UNIQUE_CLEAN = 3'b001, // UC - Unique Clean  
    CHI_UNIQUE_DIRTY = 3'b010, // UD - Unique Dirty
    CHI_SHARED_CLEAN = 3'b011, // SC - Shared Clean
    CHI_SHARED_DIRTY = 3'b100, // SD - Shared Dirty  
    CHI_EXCLUSIVE   = 3'b101,  // E - Exclusive
    CHI_MODIFIED    = 3'b110,  // M - Modified
    CHI_OWNED       = 3'b111   // O - Owned
  } chi_cache_state_e;

  // CHI Request Opcodes
  typedef enum logic [5:0] {
    // Read transactions
    CHI_READSHARED     = 6'h01,
    CHI_READCLEAN      = 6'h02, 
    CHI_READONCE       = 6'h03,
    CHI_READNOSNP      = 6'h04,
    CHI_READUNIQUE     = 6'h07,
    
    // Write transactions
    CHI_WRITENOSNPPTL  = 6'h18,
    CHI_WRITENOSNPFULL = 6'h19,
    CHI_WRITEUNIQUEPTL = 6'h1A,
    CHI_WRITEUNIQUEFULL= 6'h1B,
    CHI_WRITECLEANFULL = 6'h1C,
    CHI_WRITEBACKFULL  = 6'h1D,
    CHI_WRITEBACKPTL   = 6'h1E,
    CHI_WRITEVICTIMFULL= 6'h1F,
    
    // Coherent transactions
    CHI_CLEANSHARED    = 6'h20,
    CHI_CLEANINVALID   = 6'h21,
    CHI_MAKEINVALID    = 6'h22,
    CHI_CLEANUNIQUE    = 6'h23,
    
    // Snoop transactions  
    CHI_SNPSHARED      = 6'h30,
    CHI_SNPCLEAN       = 6'h31,
    CHI_SNPONCE        = 6'h32,
    CHI_SNPUNIQUE      = 6'h33
  } chi_opcode_e;

  // CHI Response Opcodes
  typedef enum logic [4:0] {
    CHI_COMP           = 5'h00,  // Completion
    CHI_COMPDBIDRESP   = 5'h01,  // Completion with DBID
    CHI_DBIDRESP       = 5'h02,  // DBID Response
    CHI_READRECEIPT    = 5'h03,  // Read Receipt
    CHI_SNPRESP        = 5'h04,  // Snoop Response
    CHI_COMPDATA       = 5'h05,  // Completion with Data
    CHI_SNPRESPDATA    = 5'h06,  // Snoop Response with Data
    CHI_DATALESS       = 5'h07   // Dataless Response
  } chi_resp_opcode_e;

  // CHI Response Error Codes
  typedef enum logic [1:0] {
    CHI_OKAY           = 2'b00,  // Normal completion
    CHI_EXOKAY         = 2'b01,  // Exclusive completion  
    CHI_SLVERR         = 2'b10,  // Slave error
    CHI_DECERR         = 2'b11   // Decode error
  } chi_resp_err_e;

  // =============================================================================
  // CHI MESSAGE STRUCTURES
  // =============================================================================

  // CHI Request Channel Structure
  typedef struct packed {
    logic [CHI_TXN_ID_WIDTH-1:0]    txn_id;      // Transaction ID
    logic [CHI_NODE_ID_WIDTH-1:0]   src_id;      // Source node ID  
    logic [CHI_NODE_ID_WIDTH-1:0]   tgt_id;      // Target node ID
    logic [CHI_REQ_ADDR_WIDTH-1:0]  addr;        // Address
    chi_opcode_e                    opcode;      // Request opcode
    logic [2:0]                     size;        // Transfer size (2^size bytes)
    logic [CHI_RSVDC_WIDTH-1:0]     rsvdc;       // Reserved field
    logic                           likely_shared; // Cache line likely shared
    logic                           allow_retry; // Allow retry responses
    logic [QOS_WIDTH-1:0]           qos;         // Quality of Service
  } chi_req_t;

  // CHI Response Channel Structure  
  typedef struct packed {
    logic [CHI_TXN_ID_WIDTH-1:0]    txn_id;      // Transaction ID
    logic [CHI_NODE_ID_WIDTH-1:0]   src_id;      // Source node ID
    logic [CHI_NODE_ID_WIDTH-1:0]   tgt_id;      // Target node ID
    chi_resp_opcode_e               opcode;      // Response opcode
    chi_resp_err_e                  resp_err;    // Response error
    logic [CHI_DBID_WIDTH-1:0]      dbid;        // Data buffer ID
    logic [2:0]                     fwd_state;   // Forwarded cache state
    logic [CHI_RSVDC_WIDTH-1:0]     rsvdc;       // Reserved field
    logic [QOS_WIDTH-1:0]           qos;         // Quality of Service
  } chi_resp_t;

  // CHI Data Channel Structure
  typedef struct packed {
    logic [CHI_TXN_ID_WIDTH-1:0]    txn_id;      // Transaction ID  
    logic [CHI_NODE_ID_WIDTH-1:0]   src_id;      // Source node ID
    logic [CHI_NODE_ID_WIDTH-1:0]   tgt_id;      // Target node ID
    logic [CHI_DATA_WIDTH-1:0]      data;        // Data payload
    logic [CHI_BE_WIDTH-1:0]        be;          // Byte enables
    logic [1:0]                     data_id;     // Data identifier
    logic                           ccid;        // Critical chunk ID
    logic                           data_pull;   // Data pull indication
    logic [CHI_RSVDC_WIDTH-1:0]     rsvdc;       // Reserved field
    logic [QOS_WIDTH-1:0]           qos;         // Quality of Service
  } chi_data_t;

  // CHI Snoop Channel Structure
  typedef struct packed {
    logic [CHI_TXN_ID_WIDTH-1:0]    txn_id;      // Transaction ID
    logic [CHI_NODE_ID_WIDTH-1:0]   src_id;      // Source node ID
    logic [CHI_NODE_ID_WIDTH-1:0]   tgt_id;      // Target node ID  
    logic [CHI_REQ_ADDR_WIDTH-1:0]  addr;        // Address
    chi_opcode_e                    opcode;      // Snoop opcode
    logic                           ns;          // Non-secure access
    logic                           do_not_goto_sd; // Do not go to Shared Dirty
    logic                           ret_to_src;  // Return data to source
    logic [CHI_RSVDC_WIDTH-1:0]     rsvdc;       // Reserved field
    logic [QOS_WIDTH-1:0]           qos;         // Quality of Service
  } chi_snoop_t;

  // Directory Entry Structure
  typedef struct packed {
    chi_cache_state_e               state;       // Cache line state
    logic [CHI_NODE_ID_WIDTH-1:0]   owner;       // Owner node ID (if exclusive)
    logic [63:0]                    sharers;     // Sharer bit vector (64 nodes max)
    logic                           dirty;       // Dirty bit
    logic                           valid;       // Valid entry
    logic [CHI_TXN_ID_WIDTH-1:0]    pending_txn; // Pending transaction ID
  } chi_directory_entry_t;

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
  
  // AXI4 burst types
  typedef enum logic [1:0] {
    AXI_BURST_FIXED = 2'b00,
    AXI_BURST_INCR  = 2'b01,
    AXI_BURST_WRAP  = 2'b10,
    AXI_BURST_RSVD  = 2'b11
  } axi_burst_e;
  
  // AXI4 response types
  typedef enum logic [1:0] {
    AXI_RESP_OKAY   = 2'b00,
    AXI_RESP_EXOKAY = 2'b01,
    AXI_RESP_SLVERR = 2'b10,
    AXI_RESP_DECERR = 2'b11
  } axi_resp_e;
  
  // AXI4 Write Address Channel
  typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]     awid;
    logic [AXI_ADDR_WIDTH-1:0]   awaddr;
    logic [7:0]                  awlen;      // Burst length
    logic [2:0]                  awsize;     // Burst size
    logic [1:0]                  awburst;    // Burst type
    logic                        awlock;     // Lock type
    logic [3:0]                  awcache;    // Cache type
    logic [2:0]                  awprot;     // Protection type
    logic [QOS_WIDTH-1:0]        awqos;      // QoS identifier
    logic [3:0]                  awregion;   // Region identifier
    logic [AXI_AWUSER_WIDTH-1:0] awuser;     // User signal
  } axi_aw_t;
  
  // AXI4 Write Data Channel
  typedef struct packed {
    logic [AXI_DATA_WIDTH-1:0]   wdata;
    logic [AXI_STRB_WIDTH-1:0]   wstrb;      // Write strobe
    logic                        wlast;      // Write last
    logic [AXI_WUSER_WIDTH-1:0]  wuser;      // User signal
  } axi_w_t;
  
  // AXI4 Write Response Channel
  typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]     bid;
    logic [1:0]                  bresp;      // Write response
    logic [AXI_BUSER_WIDTH-1:0]  buser;      // User signal
  } axi_b_t;
  
  // AXI4 Read Address Channel
  typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]     arid;
    logic [AXI_ADDR_WIDTH-1:0]   araddr;
    logic [7:0]                  arlen;      // Burst length
    logic [2:0]                  arsize;     // Burst size
    logic [1:0]                  arburst;    // Burst type
    logic                        arlock;     // Lock type
    logic [3:0]                  arcache;    // Cache type
    logic [2:0]                  arprot;     // Protection type
    logic [QOS_WIDTH-1:0]        arqos;      // QoS identifier
    logic [3:0]                  arregion;   // Region identifier
    logic [AXI_ARUSER_WIDTH-1:0] aruser;     // User signal
  } axi_ar_t;
  
  // AXI4 Read Data Channel
  typedef struct packed {
    logic [AXI_ID_WIDTH-1:0]     rid;
    logic [AXI_DATA_WIDTH-1:0]   rdata;
    logic [1:0]                  rresp;      // Read response
    logic                        rlast;      // Read last
    logic [AXI_RUSER_WIDTH-1:0]  ruser;      // User signal
  } axi_r_t;
  
  // Outstanding Transaction Entry
  typedef struct packed {
    logic                        valid;
    logic [AXI_ID_WIDTH-1:0]     axi_id;
    logic [AXI_ADDR_WIDTH-1:0]   base_addr;
    logic [7:0]                  burst_len;
    logic [2:0]                  burst_size;
    logic [1:0]                  burst_type;
    logic [7:0]                  beat_count;
    logic                        is_write;
    logic [PACKET_ID_WIDTH-1:0]  packet_id;
    logic [COORD_WIDTH-1:0]      dest_x;
    logic [COORD_WIDTH-1:0]      dest_y;
  } transaction_entry_t;
  

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
