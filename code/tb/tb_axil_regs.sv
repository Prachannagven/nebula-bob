`ifdef TB_AXIL_REGS
module tb_axil_regs; logic clk=0,rst_n=0; always #5 clk=~clk; axil_ar_t ar; axil_b_r_t r; axil_aw_w_t aw;
  axil_b_r_t b; logic [31:0] qos, cluster;
  nebula_axil_regs dut(.clk,.rst_n,.s_ar(ar),.s_r(r),.s_aw_w(aw),.s_b(b),.cfg_qos_thresh(qos),.cfg_cluster_id(cluster));
  initial begin repeat(3) @(posedge clk); rst_n=1; ar='0; aw='0;
    // Write reg0
    aw.valid=1; aw.addr=32'h0; aw.strb=4'hF; aw.data=32'd12; @(posedge clk); aw.valid=0;
    // Read reg0
    ar.valid=1; ar.addr=32'h0; @(posedge clk); ar.valid=0; @(posedge clk);
    // Write reg1 and read back
    aw.valid=1; aw.addr=32'h4; aw.strb=4'hF; aw.data=32'hABCD; @(posedge clk); aw.valid=0;
    ar.valid=1; ar.addr=32'h4; @(posedge clk); ar.valid=0; @(posedge clk);
    repeat(5) @(posedge clk); $finish; end
endmodule
`endif
