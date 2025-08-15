module nebula_top #(parameter int NX=2, NY=2)(input logic clk, rst_n);
  nebula_mesh_top #(.NX(NX),.NY(NY)) u_mesh (.clk,.rst_n);
endmodule
