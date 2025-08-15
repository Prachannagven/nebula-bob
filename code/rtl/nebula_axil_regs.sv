module nebula_axil_regs (
  input  logic clk, rst_n,
  input  axil_ar_t  s_ar,   output axil_b_r_t s_r,
  input  axil_aw_w_t s_aw_w,output axil_b_r_t s_b,
  output logic [31:0] cfg_qos_thresh, output logic [31:0] cfg_cluster_id);
  logic [31:0] regs [0:3];
  assign s_r.ready=1'b1; assign s_r.resp=2'b00; assign s_r.valid=s_ar.valid; assign s_r.data=regs[s_ar.addr[3:2]];
  assign s_b.ready=1'b1; assign s_b.resp=2'b00; assign s_b.valid=s_aw_w.valid;
  always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin regs[0]<=32'd8; regs[1]<=32'd0; end
    else if(s_aw_w.valid) regs[s_aw_w.addr[3:2]] <= (s_aw_w.data & {8{s_aw_w.strb[0]}});
  end
  assign cfg_qos_thresh=regs[0]; assign cfg_cluster_id=regs[1];
endmodule
