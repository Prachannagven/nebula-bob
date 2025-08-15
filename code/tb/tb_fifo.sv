`ifdef TB_FIFO
module tb_fifo; logic clk=0,rst_n=0; always #5 clk=~clk; localparam W=16,DEP=8;
  logic push,pop; logic [W-1:0] din,dout; logic full,empty; logic [$clog2(DEP):0] level;
  nebula_fifo #(.WIDTH(W),.DEPTH(DEP)) dut(.clk,.rst_n,.push,.din,.pop,.dout,.full,.empty,.level);
  initial begin repeat(3) @(posedge clk); rst_n=1; push=0; pop=0; din='0;
    // Fill
    for(int i=0;i<DEP;i++) begin @(posedge clk); push=1; din=i; end @(posedge clk); push=0;
    // Drain
    for(int i=0;i<DEP;i++) begin @(posedge clk); pop=1; end @(posedge clk); pop=0;
    // Interleave
    repeat(3) begin @(posedge clk); push=1; din=$urandom_range(0,255); @(posedge clk); push=0; pop=1; @(posedge clk); pop=0; end
    repeat(10) @(posedge clk); $finish; end
endmodule
`endif
