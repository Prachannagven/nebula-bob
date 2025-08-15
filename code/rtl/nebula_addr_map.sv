module nebula_addr_map #(parameter int NX=4, NY=4, parameter int A=48) (
  input  logic [A-1:0] addr, output coord_t dst);
  assign dst.x = addr[15:8]; assign dst.y = addr[7:0];
endmodule
