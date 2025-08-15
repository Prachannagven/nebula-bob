module nebula_niu_axi #(
  parameter int D=64, A=32, ID=8, parameter int NX=4, NY=4)(
  input logic clk, rst_n, axi4_small_if s_axi,
  nebula_link_if.TX noc_tx, nebula_link_if.RX noc_rx, input coord_t my_coord);
  typedef struct packed {logic used; logic [A-1:0] addr; logic [7:0] len; logic [15:0] seq; logic [ID-1:0] id;} ot_t;
  ot_t rd_ot, wr_ot; coord_t dst_tmp;
  nebula_addr_map #(.NX(NX),.NY(NY),.A(A)) u_map (.addr(s_axi.ar_valid ? s_axi.ar_addr : s_axi.aw_addr), .dst(dst_tmp));
  typedef struct packed { flit_hdr_t hdr; logic [FLIT_PAYLOAD_W-1:0] payload; } flit_t; flit_t tx_flit;

  typedef enum logic [1:0] {RD_IDLE,RD_HDR,RD_WAIT} rd_fsm_e; rd_fsm_e rd_state;
  typedef enum logic [2:0] {WR_IDLE,WR_HDR,WR_DATA,WR_WAIT_B} wr_fsm_e; wr_fsm_e wr_state;

  assign s_axi.ar_ready = (rd_state==RD_IDLE);
  assign s_axi.aw_ready = (wr_state==WR_IDLE);
  assign s_axi.w_ready  = (wr_state==WR_DATA) && noc_tx.rx_ready;
  assign noc_tx.tx_valid = ((rd_state==RD_HDR) || (wr_state==WR_HDR) || (wr_state==WR_DATA));
  assign noc_tx.tx_flit  = tx_flit; assign noc_tx.credit_tx_valid=1'b0; assign noc_tx.credit_tx_vc='0;

  always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin rd_state<=RD_IDLE; rd_ot<='0; end
    else case(rd_state)
      RD_IDLE: if(s_axi.ar_valid) begin rd_ot.used<=1'b1; rd_ot.addr<=s_axi.ar_addr; rd_ot.len<=s_axi.ar_len; rd_ot.seq<=0; rd_ot.id<=s_axi.ar_id; rd_state<=RD_HDR; end
      RD_HDR:  if(noc_tx.rx_ready) rd_state<=RD_WAIT;
      RD_WAIT: if(!rd_ot.used) rd_state<=RD_IDLE;
    endcase
  end
  always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin wr_state<=WR_IDLE; wr_ot<='0; end
    else case(wr_state)
      WR_IDLE: if(s_axi.aw_valid) begin wr_ot.used<=1'b1; wr_ot.addr<=s_axi.aw_addr; wr_ot.len<=s_axi.aw_len; wr_ot.seq<=0; wr_ot.id<=s_axi.aw_id; wr_state<=WR_HDR; end
      WR_HDR:  if(noc_tx.rx_ready) wr_state<=WR_DATA;
      WR_DATA: if(s_axi.w_valid && s_axi.w_ready) begin wr_ot.seq<=wr_ot.seq+1; if(s_axi.w_last) wr_state<=WR_WAIT_B; end
      WR_WAIT_B: if(!wr_ot.used) wr_state<=WR_IDLE;
    endcase
  end

  always_comb begin
    tx_flit='0; tx_flit.hdr.src=my_coord; tx_flit.hdr.dst=dst_tmp; tx_flit.hdr.length=8'd1;
    if(rd_state==RD_HDR) begin
      tx_flit.hdr.head=1'b1; tx_flit.hdr.tail=1'b1; tx_flit.hdr.msg=NOC_MSG_REQ; tx_flit.hdr.vclass=VC_REQ;
      tx_flit.hdr.tid={8'h00, rd_ot.id}; tx_flit.payload={192'b0, s_axi.ar_addr, s_axi.ar_len, 32'hDEAD_RD};
    end else if(wr_state==WR_HDR) begin
      tx_flit.hdr.head=1'b1; tx_flit.hdr.tail=(s_axi.aw_len==0); tx_flit.hdr.msg=NOC_MSG_REQ; tx_flit.hdr.vclass=VC_REQ;
      tx_flit.hdr.tid={8'h00, wr_ot.id}; tx_flit.payload={192'b0, s_axi.aw_addr, s_axi.aw_len, 32'hBEEF_WR};
    end else if(wr_state==WR_DATA && s_axi.w_valid) begin
      tx_flit.hdr.head=1'b0; tx_flit.hdr.tail=s_axi.w_last; tx_flit.hdr.msg=NOC_MSG_DATA; tx_flit.hdr.vclass=VC_DATA0;
      tx_flit.hdr.tid={8'h00, wr_ot.id}; tx_flit.payload={{(FLIT_PAYLOAD_W-D){1'b0}}, s_axi.w_data};
    end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if(!rst_n) begin
      s_axi.r_valid<=1'b0; s_axi.r_data<='0; s_axi.r_resp<=2'b00; s_axi.r_last<=1'b0; s_axi.r_id<='0;
      s_axi.b_valid<=1'b0; s_axi.b_resp<=2'b00; s_axi.b_id<='0;
      noc_rx.credit_rx_valid<=1'b0; noc_rx.credit_rx_vc<='0; noc_rx.tx_ready<=1'b1;
    end else begin
      s_axi.r_valid<=1'b0; s_axi.b_valid<=1'b0; noc_rx.credit_rx_valid<=1'b0;
      if(noc_rx.rx_valid && noc_rx.tx_ready) begin
        typedef struct packed { flit_hdr_t hdr; logic [FLIT_PAYLOAD_W-1:0] payload; } flit_t2; flit_t2 f = noc_rx.rx_flit;
        noc_rx.credit_rx_valid<=1'b1; noc_rx.credit_rx_vc<={5'b0, f.hdr.vclass};
        if(f.hdr.msg==NOC_MSG_DATA) begin
          s_axi.r_valid<=1'b1; s_axi.r_data<=f.payload[D-1:0]; s_axi.r_last<=f.hdr.tail; s_axi.r_resp<=2'b00; s_axi.r_id<=f.hdr.tid[ID-1:0];
          if(f.hdr.tail) rd_ot.used<=1'b0;
        end else if(f.hdr.msg==NOC_MSG_RESP) begin
          s_axi.b_valid<=1'b1; s_axi.b_resp<=2'b00; s_axi.b_id<=f.hdr.tid[ID-1:0];
          wr_ot.used<=1'b0;
        end
      end
    end
  end
