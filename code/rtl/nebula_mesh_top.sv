module nebula_mesh_top #(parameter int NX=4, NY=4, parameter int VCS=4, parameter int FIFO_DEPTH=8)(input logic clk, rst_n);
  localparam int PORTS=5;
  nebula_link_if links_n [NX][NY] (.*); nebula_link_if links_s [NX][NY] (.*);
  nebula_link_if links_e [NX][NY] (.*); nebula_link_if links_w [NX][NY] (.*);
  nebula_link_if link_local [NX][NY] (.*);
  for(genvar x=0;x<NX;x++) begin: GX for(genvar y=0;y<NY;y++) begin: GY
    nebula_router #(.NX(NX),.NY(NY),.X_ID(x),.Y_ID(y),.PORTS(PORTS),.VCS(VCS),.FIFO_DEPTH(FIFO_DEPTH)) u_r (
      .clk,.rst_n,
      .link_out('{
        (y>0)    ? links_n[x][y] : link_local[x][y],
        (y<NY-1) ? links_s[x][y] : link_local[x][y],
        (x<NX-1) ? links_e[x][y] : link_local[x][y],
        (x>0)    ? links_w[x][y] : link_local[x][y],
        link_local[x][y]}),
      .link_in('{
        (y>0)    ? links_s[x][y-1] : link_local[x][y],
        (y<NY-1) ? links_n[x][y+1] : link_local[x][y],
        (x<NX-1) ? links_w[x+1][y] : link_local[x][y],
        (x>0)    ? links_e[x-1][y] : link_local[x][y],
        link_local[x][y]}),
      .congest());
    axi4_small_if #(.A(32),.D(64),.ID(8)) s_axi (.*);
    nebula_niu_axi #(.D(64),.A(32),.ID(8),.NX(NX),.NY(NY)) u_niu (
      .clk,.rst_n,.s_axi,.noc_tx(link_local[x][y]),.noc_rx(link_local[x][y]),.my_coord('{x[7:0],y[7:0]}));
  end end
endmodule
