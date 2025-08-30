/**
 * Credit-Based Flow Control Module
 * 
 * Implements credit-based flow control for NoC links.
 * Each credit represents one buffer slot at the downstream node.
 * 
 * Features:
 * - Configurable initial credit count
 * - Credit increment on credit return
 * - Credit decrement on data send
 * - Flow control ready signal generation
 */

import nebula_pkg::*;

module nebula_credit_flow_ctrl #(
  parameter int MAX_CREDITS = VC_DEPTH,
  parameter int CREDIT_WIDTH = $clog2(MAX_CREDITS + 1)
)(
  input  logic                      clk,
  input  logic                      rst_n,
  
  // Data send interface
  input  logic                      send_flit,
  output logic                      credits_available,
  
  // Credit return interface
  input  logic                      credit_return,
  
  // Status
  output logic [CREDIT_WIDTH-1:0]  credit_count
);

  // Internal credit counter
  logic [CREDIT_WIDTH-1:0] credits;
  
  assign credit_count = credits;
  assign credits_available = (credits > 0);
  
  // Credit management
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      credits <= MAX_CREDITS;  // Start with full credits
    end else begin
      case ({send_flit && credits_available, credit_return})
        2'b01: begin // Credit return only
          if (credits < MAX_CREDITS) begin
            credits <= credits + 1;
          end
        end
        2'b10: credits <= credits - 1;                    // Send flit only
        2'b11: credits <= credits;                        // Both (no change)
        default: credits <= credits;                      // No operation
      endcase
    end
  end
  
  // Assertions for verification
  `ifdef ASSERT_ON
    // Credits should never exceed maximum
    property credit_max_check;
      @(posedge clk) disable iff (!rst_n)
      credits <= MAX_CREDITS;
    endproperty
    assert property (credit_max_check) else $error("Credits exceeded maximum");
    
    // Should not send when no credits available
    property no_send_without_credits;
      @(posedge clk) disable iff (!rst_n)
      send_flit |-> credits_available;
    endproperty
    assert property (no_send_without_credits) else $error("Sent flit without credits");
    
    // Credits should not underflow
    property credit_underflow_check;
      @(posedge clk) disable iff (!rst_n)
      credits >= 0;
    endproperty
    assert property (credit_underflow_check) else $error("Credit underflow");
  `endif

endmodule
