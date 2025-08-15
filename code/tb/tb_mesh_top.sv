`ifdef TB_TOP
module tb_mesh_top; localparam int NX=2, NY=2; logic clk=0,rst_n=0; always #5 clk=~clk;
  nebula_mesh_top #(.NX(NX),.NY(NY)) dut(.clk,.rst_n);
  initial begin repeat(5) @(posedge clk); rst_n=1; repeat(200) @(posedge clk); $finish; end
endmodule
`endif
