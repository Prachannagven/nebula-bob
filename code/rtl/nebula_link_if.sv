interface nebula_link_if #(parameter int FLIT_WI=FLIT_W, VC_W=3) (input logic clk, rst_n);
  logic              tx_valid;  logic [FLIT_WI-1:0] tx_flit;  logic rx_ready; // our TX
  logic              rx_valid;  logic [FLIT_WI-1:0] rx_flit;  logic tx_ready; // our RX backpressure
  logic        credit_tx_valid; logic [7:0] credit_tx_vc;
  logic        credit_rx_valid; logic [7:0] credit_rx_vc;
  modport TX (input clk,rst_n, input rx_ready, output tx_valid, output tx_flit,
              output credit_tx_valid, output credit_tx_vc,
              input credit_rx_valid, input credit_rx_vc);
  modport RX (input clk,rst_n, output rx_ready, input rx_valid, input rx_flit,
              input credit_tx_valid, input credit_tx_vc,
              output credit_rx_valid, output credit_rx_vc);
endinterface
