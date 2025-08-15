`ifdef TB_ROUTER
module tb_router; localparam int VCS=2; localparam int PORTS=5; logic clk=0,rst_n=0; always #5 clk=~clk;
  nebula_link_if links_tx[PORTS](.*); nebula_link_if links_rx[PORTS](.*);
  logic [PORTS-1:0] congest;
  nebula_router #(.VCS(VCS),.FIFO_DEPTH(4)) dut(.clk,.rst_n,.link_out(links_tx),.link_in(links_rx),.congest);
  // simple loopback local port to itself, stimulate one flit into local RX
  typedef struct packed { flit_hdr_t hdr; logic [FLIT_PAYLOAD_W-1:0] payload; } flit_t;
  initial begin repeat(5) @(posedge clk); rst_n=1; // send one local flit
    flit_t f; f='0; f.hdr.head=1; f.hdr.tail=1; f.hdr.vclass=VC_REQ; f.hdr.dst='{8'd0,8'd0};
    links_rx[4].rx_valid<=1; links_rx[4].rx_flit<=f; @(posedge clk); links_rx[4].rx_valid<=0;
    repeat(20) @(posedge clk); $finish; end
  // Always ready downstream
  genvar o; generate for(o=0;o<PORTS;o++) begin : G
    assign links_tx[o].rx_ready = 1'b1; end endgenerate
endmodule
`endif
