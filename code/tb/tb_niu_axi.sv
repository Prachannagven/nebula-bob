`ifdef TB_NIU
module tb_niu_axi; logic clk=0,rst_n=0; always #5 clk=~clk; axi4_small_if #(.D(64)) axi(.*);
  nebula_link_if link(.*); coord_t me='{8'd0,8'd0};
  nebula_niu_axi dut(.clk,.rst_n,.s_axi(axi),.noc_tx(link),.noc_rx(link),.my_coord(me));
  initial begin repeat(5) @(posedge clk); rst_n=1;
    // Simple write burst of 2 beats
    axi.aw_valid<=1; axi.aw_addr<=32'h0001_0001; axi.aw_len<=8'd1; axi.aw_id<=8'h1; @(posedge clk); axi.aw_valid<=0;
    axi.w_valid<=1; axi.w_data<=64'h1122_3344_5566_7788; axi.w_strb<=8'hFF; axi.w_last<=0; @(posedge clk);
    axi.w_data<=64'h99AA_BBCC_DDEE_FF00; axi.w_last<=1; @(posedge clk); axi.w_valid<=0;
    // Read request
    axi.ar_valid<=1; axi.ar_addr<=32'h0001_0001; axi.ar_len<=8'd0; axi.ar_id<=8'h2; @(posedge clk); axi.ar_valid<=0;
    repeat(50) @(posedge clk); $finish; end
endmodule
`endif
