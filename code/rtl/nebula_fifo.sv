module nebula_fifo #(parameter int WIDTH=64, DEPTH=16, ADDR_W=$clog2(DEPTH)) (
  input  logic clk, rst_n,
  input  logic push, input logic [WIDTH-1:0] din,
  input  logic pop,  output logic [WIDTH-1:0] dout,
  output logic full, output logic empty, output logic [ADDR_W:0] level);
  logic [WIDTH-1:0] mem [0:DEPTH-1];
  logic [ADDR_W-1:0] rd_ptr, wr_ptr; logic [ADDR_W:0] cnt;
  assign full=(cnt==DEPTH); assign empty=(cnt==0); assign level=cnt; assign dout=mem[rd_ptr];
  always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin rd_ptr<='0; wr_ptr<='0; cnt<='0; end
    else begin
      if(push && !full) begin mem[wr_ptr]<=din; wr_ptr<=wr_ptr+1'b1; end
      if(pop  && !empty) begin rd_ptr<=rd_ptr+1'b1; end
      case({push && !full, pop && !empty})
        2'b10: cnt<=cnt+1'b1; 2'b01: cnt<=cnt-1'b1; default: cnt<=cnt;
      endcase
    end
  end
endmodule
