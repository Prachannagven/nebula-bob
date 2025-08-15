package nebula_pkg;
  typedef struct packed { logic [7:0] x; logic [7:0] y; } coord_t; // up to 256x256

  typedef enum logic [2:0] {
    VC_CTRL=3'd0, VC_REQ=3'd1, VC_RESP=3'd2, VC_DATA0=3'd3,
    VC_DATA1=3'd4, VC_SNOOP=3'd5, VC_SYS=3'd6
  } vc_class_e;

  typedef enum logic [2:0] {
    NOC_MSG_REQ=3'd0, NOC_MSG_RESP=3'd1, NOC_MSG_DATA=3'd2,
    NOC_MSG_SNOOP=3'd3, NOC_MSG_CTRL=3'd4
  } noc_msg_e;

  typedef struct packed {
    coord_t      dst;      coord_t    src;
    vc_class_e   vclass;   noc_msg_e  msg;
    logic [15:0] tid;      logic [15:0] seq;
    logic [7:0]  length;   logic [7:0]  qos;
    logic [7:0]  cluster;  logic        head;
    logic        tail;
  } flit_hdr_t;

  parameter int FLIT_PAYLOAD_W = 256;
  parameter int FLIT_HDR_W     = $bits(flit_hdr_t);
  parameter int FLIT_W         = FLIT_HDR_W + FLIT_PAYLOAD_W;

  typedef struct packed { logic valid; logic [7:0] vc; } credit_t;

  typedef struct packed { logic [31:0] addr; logic valid; logic ready; } axil_ar_t;
  typedef struct packed { logic [31:0] data; logic [3:0] strb; logic [31:0] addr; logic valid; logic ready; } axil_aw_w_t;
  typedef struct packed { logic valid; logic ready; logic [1:0] resp; logic [31:0] data; } axil_b_r_t;
endpackage
import nebula_pkg::*;
