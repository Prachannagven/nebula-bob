module nebula_router #(
  parameter int NX=4, NY=4, parameter int X_ID=0, Y_ID=0,
  parameter int PORTS=5, parameter int VCS=4, parameter int FIFO_DEPTH=8,
  parameter int FLITW=FLIT_W)(
  input  logic clk, rst_n,
  nebula_link_if.TX link_out[PORTS], nebula_link_if.RX link_in[PORTS],
  output logic [PORTS-1:0] congest);
  typedef struct packed { flit_hdr_t hdr; logic [FLIT_PAYLOAD_W-1:0] payload; } flit_t;
  localparam int FLITW_INT=$bits(flit_t);
  flit_t fifo_din[PORTS][VCS], fifo_dout[PORTS][VCS];
  logic  fifo_push[PORTS][VCS], fifo_pop[PORTS][VCS], fifo_full[PORTS][VCS], fifo_empty[PORTS][VCS];

  for(genvar p=0;p<PORTS;p++) begin: G_RX
    logic [2:0] rx_vc_sel; flit_t rx_flit_unpack; assign rx_flit_unpack=link_in[p].rx_flit; assign rx_vc_sel=rx_flit_unpack.hdr.vclass[2:0]%VCS;
    assign link_in[p].rx_ready = !fifo_full[p][rx_vc_sel];
    always_ff @(posedge clk or negedge rst_n) begin
      if(!rst_n) begin link_in[p].credit_rx_valid<=1'b0; link_in[p].credit_rx_vc<='0; end
      else begin
        link_in[p].credit_rx_valid<=1'b0; link_in[p].credit_rx_vc<='0;
        for(int v=0; v<VCS; v++) if(fifo_pop[p][v]) begin link_in[p].credit_rx_valid<=1'b1; link_in[p].credit_rx_vc<=v[7:0]; end
      end
    end
    for(genvar v=0; v<VCS; v++) begin: G_VC
      assign fifo_push[p][v] = link_in[p].rx_valid && link_in[p].rx_ready && (rx_vc_sel==v);
      assign fifo_din [p][v] = rx_flit_unpack;
      nebula_fifo #(.WIDTH(FLITW_INT), .DEPTH(FIFO_DEPTH)) u_fifo (.*,
        .push(fifo_push[p][v]), .din(fifo_din[p][v]), .pop(fifo_pop[p][v]), .dout(fifo_dout[p][v]),
        .full(fifo_full[p][v]), .empty(fifo_empty[p][v]), .level());
    end
  end

  function automatic int xy_route (input coord_t me, input coord_t dst);
    if(dst.x>me.x) return 2; else if(dst.x<me.x) return 3; else if(dst.y>me.y) return 1; else if(dst.y<me.y) return 0; else return 4;
  endfunction
  coord_t ME; assign ME.x=X_ID[7:0]; assign ME.y=Y_ID[7:0];

  typedef struct packed {logic valid; logic [$clog2(PORTS)-1:0] outp; flit_t flit; int src_p; int src_v;} req_t;
  req_t req[PORTS][VCS];
  always_comb begin
    for(int p=0;p<PORTS;p++) for(int v=0;v<VCS;v++) begin
      req[p][v].valid=!fifo_empty[p][v]; req[p][v].outp=xy_route(ME,fifo_dout[p][v].hdr.dst);
      req[p][v].flit=fifo_dout[p][v]; req[p][v].src_p=p; req[p][v].src_v=v; end
  end

  logic [PORTS-1:0] out_has_grant; flit_t out_flit[PORTS]; int out_src_p[PORTS]; int out_src_v[PORTS];
  int rr_ptr[PORTS];
  always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) for(int o=0;o<PORTS;o++) rr_ptr[o]<=0; else for(int o=0;o<PORTS;o++)
      if(out_has_grant[o] && link_out[o].rx_ready && link_out[o].tx_valid) rr_ptr[o]<=rr_ptr[o]+1;
  end
  always_comb begin
    for(int o=0;o<PORTS;o++) begin
      out_has_grant[o]=1'b0; out_flit[o]='0; out_src_p[o]=0; out_src_v[o]=0;
      for(int k=0;k<PORTS*VCS;k++) begin int idx=(rr_ptr[o]+k)%(PORTS*VCS); int p=idx/VCS; int v=idx%VCS;
        if(req[p][v].valid && req[p][v].outp==o) begin out_has_grant[o]=1'b1; out_flit[o]=req[p][v].flit; out_src_p[o]=p; out_src_v[o]=v; break; end
      end
    end
  end

  for(genvar o=0;o<PORTS;o++) begin: G_TX
    assign link_out[o].tx_valid=out_has_grant[o]; assign link_out[o].tx_flit=out_flit[o];
    always_comb begin for(int p=0;p<PORTS;p++) for(int v=0;v<VCS;v++) fifo_pop[p][v]=1'b0;
      if(out_has_grant[o] && link_out[o].rx_ready) fifo_pop[out_src_p[o]][out_src_v[o]]=1'b1; end
    assign link_out[o].credit_tx_valid=1'b0; assign link_out[o].credit_tx_vc='0;
  end

  for(genvar p=0;p<PORTS;p++) begin: G_CONG
    logic [$clog2(FIFO_DEPTH+1)-1:0] occ_sum;
    always_comb begin occ_sum='0; for(int v=0; v<VCS; v++) occ_sum += (!fifo_empty[p][v]); congest[p]=(occ_sum>(VCS/2)); end
  end
endmodule
