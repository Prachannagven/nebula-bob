interface axi4_small_if #(parameter int A=32, D=64, ID=8) (input logic clk, rst_n);
  logic ar_valid, ar_ready; logic [A-1:0] ar_addr; logic [7:0] ar_len; logic [ID-1:0] ar_id;
  logic r_valid,  r_ready;  logic [D-1:0] r_data; logic [1:0] r_resp; logic r_last; logic [ID-1:0] r_id;
  logic aw_valid, aw_ready; logic [A-1:0] aw_addr; logic [7:0] aw_len; logic [ID-1:0] aw_id;
  logic w_valid,  w_ready;  logic [D-1:0] w_data; logic [7:0] w_strb; logic w_last;
  logic b_valid,  b_ready;  logic [1:0] b_resp; logic [ID-1:0] b_id;
endinterface
