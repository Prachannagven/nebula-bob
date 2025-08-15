module chi_lite_directory #(parameter int LINES=1024)(
  input logic clk, rst_n, input logic rd_en, input logic wr_en,
  input logic [31:0] index, input logic [7:0] state_in, input logic [63:0] sharers_in,
  output logic [7:0] state_out, output logic [63:0] sharers_out);
  logic [7:0]  state_ram   [0:LINES-1];
  logic [63:0] sharers_ram [0:LINES-1];
  always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin for(int i=0;i<LINES;i++) begin state_ram[i]<=8'd0; sharers_ram[i]<='0; end end
    else if(wr_en) begin state_ram[index]<=state_in; sharers_ram[index]<=sharers_in; end
  end
  assign state_out=state_ram[index]; assign sharers_out=sharers_ram[index];
endmodule
