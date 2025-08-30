/**
 * Round-Robin Arbiter
 * 
 * N-way round-robin arbiter with configurable number of requestors.
 * Ensures fair access by rotating priority among requestors.
 * 
 * Features:
 * - Parameterizable number of requestors
 * - True round-robin with rotating priority
 * - One-hot grant output
 * - Grant valid signal
 */

import nebula_pkg::*;

module nebula_rr_arbiter #(
  parameter int NUM_REQS = NUM_PORTS,
  parameter int REQ_WIDTH = $clog2(NUM_REQS)
)(
  input  logic                     clk,
  input  logic                     rst_n,
  
  // Request interface
  input  logic [NUM_REQS-1:0]      req,
  
  // Grant interface  
  output logic [NUM_REQS-1:0]      grant,
  output logic                     grant_valid,
  output logic [REQ_WIDTH-1:0]     grant_id
);

  // Priority mask for round-robin
  logic [NUM_REQS-1:0] priority_mask;
  logic [NUM_REQS-1:0] masked_req;
  logic [NUM_REQS-1:0] unmasked_grant;
  logic [NUM_REQS-1:0] masked_grant;
  
  // Apply priority mask to requests
  assign masked_req = req & priority_mask;
  
  // Priority encoders for masked and unmasked requests
  nebula_priority_encoder #(.NUM_REQS(NUM_REQS)) pe_unmasked (
    .req(req),
    .grant(unmasked_grant),
    .grant_valid()
  );
  
  nebula_priority_encoder #(.NUM_REQS(NUM_REQS)) pe_masked (
    .req(masked_req),
    .grant(masked_grant),
    .grant_valid()
  );
  
  // Select between masked and unmasked grants
  assign grant = |masked_req ? masked_grant : unmasked_grant;
  assign grant_valid = |req;
  
  // Convert one-hot grant to binary ID
  always_comb begin
    grant_id = '0;
    for (int i = 0; i < NUM_REQS; i++) begin
      if (grant[i]) grant_id = i;
    end
  end
  
  // Update priority mask on each grant
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      priority_mask <= '1;  // All high initially
    end else if (grant_valid) begin
      // Update mask to exclude granted and lower priority requestors
      for (int i = 0; i < NUM_REQS; i++) begin
        if (grant[i]) begin
          // Set mask to exclude this and lower indexed requestors
          priority_mask <= ~((1 << (i + 1)) - 1);
          break;
        end
      end
      
      // If we granted the highest priority, reset mask
      if (grant[NUM_REQS-1]) begin
        priority_mask <= '1;
      end
    end
  end
  
  // Assertions for verification
  `ifdef ASSERT_ON
    // Only one grant should be active
    property one_hot_grant;
      @(posedge clk) disable iff (!rst_n)
      $onehot0(grant);
    endproperty
    assert property (one_hot_grant) else $error("Multiple grants active");
    
    // Grant should only be active when request is active
    property grant_implies_req;
      @(posedge clk) disable iff (!rst_n)
      |grant |-> |(req & grant);
    endproperty
    assert property (grant_implies_req) else $error("Grant without corresponding request");
  `endif

endmodule

/**
 * Priority Encoder Helper Module
 * Converts multiple requests to one-hot grant (lowest index has priority)
 */
module nebula_priority_encoder #(
  parameter int NUM_REQS = NUM_PORTS
)(
  input  logic [NUM_REQS-1:0]      req,
  output logic [NUM_REQS-1:0]      grant,
  output logic                     grant_valid
);

  assign grant_valid = |req;
  
  always_comb begin
    grant = '0;
    for (int i = 0; i < NUM_REQS; i++) begin
      if (req[i]) begin
        grant[i] = 1'b1;
        break;
      end
    end
  end

endmodule
