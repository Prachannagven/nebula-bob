/**
 * Testbench for nebula_rr_arbiter module
 * 
 * Tests:
 * - Round-robin fairness
 * - One-hot grant generation
 * - Grant ID encoding
 * - Priority rotation
 * - Starvation prevention
 * - Multiple simultaneous requests
 */

`timescale 1ns/1ps

import nebula_pkg::*;

module tb_nebula_rr_arbiter;

  // Parameters
  parameter int NUM_REQS = 5;
  parameter int REQ_WIDTH = $clog2(NUM_REQS);
  
  // Clock and reset
  logic clk;
  logic rst_n;
  
  // DUT interface
  logic [NUM_REQS-1:0]      req;
  logic [NUM_REQS-1:0]      grant;
  logic                     grant_valid;
  logic [REQ_WIDTH-1:0]     grant_id;
  
  // Test variables
  int error_count = 0;
  int test_count = 0;
  int grant_history[NUM_REQS];
  
  // DUT instantiation
  nebula_rr_arbiter #(
    .NUM_REQS(NUM_REQS),
    .REQ_WIDTH(REQ_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .req(req),
    .grant(grant),
    .grant_valid(grant_valid),
    .grant_id(grant_id)
  );
  
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // Test stimulus
  initial begin
    $display("=== NEBULA ROUND-ROBIN ARBITER TESTBENCH START ===");
    
    // Initialize
    rst_n = 0;
    req = 0;
    
    // Reset
    repeat(3) @(posedge clk);
    rst_n = 1;
    @(posedge clk);
    
    // Test 1: No requests
    test_no_requests();
    
    // Test 2: Single request
    test_single_request();
    
    // Test 3: Round-robin fairness
    test_round_robin_fairness();
    
    // Test 4: Grant ID encoding
    test_grant_id_encoding();
    
    // Test 5: Priority rotation
    test_priority_rotation();
    
    // Test 6: Starvation prevention
    test_starvation_prevention();
    
    // Test 7: All requests active
    test_all_requests();
    
    // Test 8: Random request patterns
    test_random_patterns();
    
    // Summary
    $display("\n=== TEST SUMMARY ===");
    $display("Total tests: %0d", test_count);
    $display("Errors: %0d", error_count);
    if (error_count == 0) begin
      $display("*** ALL TESTS PASSED ***");
    end else begin
      $display("*** %0d TESTS FAILED ***", error_count);
    end
    
    $finish;
  end
  
  // Test 1: No requests
  task test_no_requests();
    $display("\n--- Test 1: No Requests ---");
    test_count++;
    
    req = 0;
    @(posedge clk);
    
    if (grant_valid !== 1'b0) begin
      $error("Expected grant_valid=0 with no requests, got %b", grant_valid);
      error_count++;
    end
    
    if (grant !== 0) begin
      $error("Expected grant=0 with no requests, got %b", grant);
      error_count++;
    end
    
    $display("No requests test completed");
  endtask
  
  // Test 2: Single request
  task test_single_request();
    $display("\n--- Test 2: Single Request ---");
    test_count++;
    
    // Test each request line individually
    for (int i = 0; i < NUM_REQS; i++) begin
      req = (1 << i);
      @(posedge clk);
      
      if (!grant_valid) begin
        $error("Expected grant_valid=1 for req[%0d], got %b", i, grant_valid);
        error_count++;
      end
      
      if (grant !== (1 << i)) begin
        $error("Expected grant[%0d]=1, got grant=%b", i, grant);
        error_count++;
      end
      
      if (grant_id !== i) begin
        $error("Expected grant_id=%0d, got %0d", i, grant_id);
        error_count++;
      end
      
      req = 0;
      @(posedge clk);
    end
    
    $display("Single request test completed");
  endtask
  
  // Test 3: Round-robin fairness
  task test_round_robin_fairness();
    $display("\n--- Test 3: Round-Robin Fairness ---");
    test_count++;
    
    // Clear grant history
    for (int i = 0; i < NUM_REQS; i++) begin
      grant_history[i] = 0;
    end
    
    // All requestors active for multiple rounds
    req = '1; // All requests active
    
    for (int round = 0; round < NUM_REQS * 3; round++) begin
      @(posedge clk);
      
      if (!grant_valid) begin
        $error("Expected grant_valid=1 with all requests active at round %0d", round);
        error_count++;
      end
      
      // Check one-hot property
      if ($countones(grant) != 1) begin
        $error("Grant should be one-hot, got %b at round %0d", grant, round);
        error_count++;
      end
      
      // Update grant history
      for (int i = 0; i < NUM_REQS; i++) begin
        if (grant[i]) grant_history[i]++;
      end
    end
    
    // Check fairness - each requestor should have been granted roughly equally
    begin
      automatic int min_grants, max_grants;
      min_grants = grant_history[0];
      max_grants = grant_history[0];
    for (int i = 1; i < NUM_REQS; i++) begin
      if (grant_history[i] < min_grants) min_grants = grant_history[i];
      if (grant_history[i] > max_grants) max_grants = grant_history[i];
    end
    
    if (max_grants - min_grants > 1) begin
      $error("Unfair distribution detected: min=%0d, max=%0d", min_grants, max_grants);
      error_count++;
    end
    
    $display("Grant distribution:");
    for (int i = 0; i < NUM_REQS; i++) begin
      $display("  Requestor %0d: %0d grants", i, grant_history[i]);
    end
    end  // end automatic begin block
    
    req = 0;
    @(posedge clk);
    
    $display("Round-robin fairness test completed");
  endtask
  
  // Test 4: Grant ID encoding
  task test_grant_id_encoding();
    $display("\n--- Test 4: Grant ID Encoding ---");
    test_count++;
    
    for (int i = 0; i < NUM_REQS; i++) begin
      req = (1 << i);
      @(posedge clk);
      
      if (grant_id !== i) begin
        $error("Grant ID mismatch for req[%0d]: expected %0d, got %0d", i, i, grant_id);
        error_count++;
      end
      
      // Verify grant vector matches grant_id
      if (!grant[grant_id]) begin
        $error("Grant vector inconsistent with grant_id: grant=%b, grant_id=%0d", grant, grant_id);
        error_count++;
      end
    end
    
    req = 0;
    @(posedge clk);
    
    $display("Grant ID encoding test completed");
  endtask
  
  // Test 5: Priority rotation
  task test_priority_rotation();
    $display("\n--- Test 5: Priority Rotation ---");
    test_count++;
    
    // Start with all requests and observe rotation
    req = '1;
    
    begin
      automatic logic [REQ_WIDTH-1:0] last_grant_id, expected_next;
      last_grant_id = 0;
    
    // First grant establishes starting point
    @(posedge clk);
    last_grant_id = grant_id;
    $display("Initial grant to requestor %0d", last_grant_id);
    
    // Check next several grants follow round-robin order
    for (int i = 0; i < NUM_REQS - 1; i++) begin
      @(posedge clk);
      
      expected_next = (last_grant_id + 1) % NUM_REQS;
      
      if (grant_id !== expected_next) begin
        $error("Priority rotation violation: after %0d, expected %0d, got %0d", 
               last_grant_id, expected_next, grant_id);
        error_count++;
      end
      
      $display("Grant rotated to requestor %0d (expected %0d)", grant_id, expected_next);
      last_grant_id = grant_id;
    end
    
    req = 0;
    @(posedge clk);
    end  // end automatic begin block
    
    $display("Priority rotation test completed");
  endtask
  
  // Test 6: Starvation prevention
  task test_starvation_prevention();
    $display("\n--- Test 6: Starvation Prevention ---");
    test_count++;
    
    // Test scenario where high-priority requestor continuously requests
    // but others should still get service
    
    for (int starved_req = 0; starved_req < NUM_REQS; starved_req++) begin
      // Clear grant history
      for (int i = 0; i < NUM_REQS; i++) begin
        grant_history[i] = 0;
      end
      
      // Run with all requestors active
      req = '1;
      
      for (int cycle = 0; cycle < NUM_REQS * 2; cycle++) begin
        @(posedge clk);
        
        for (int i = 0; i < NUM_REQS; i++) begin
          if (grant[i]) grant_history[i]++;
        end
      end
      
      // Check that the potentially starved requestor got at least one grant
      if (grant_history[starved_req] == 0) begin
        $error("Requestor %0d was starved", starved_req);
        error_count++;
      end
    end
    
    req = 0;
    @(posedge clk);
    
    $display("Starvation prevention test completed");
  endtask
  
  // Test 7: All requests active
  task test_all_requests();
    $display("\n--- Test 7: All Requests Active ---");
    test_count++;
    
    req = '1; // All requests active
    
    // Clear grant history
    for (int i = 0; i < NUM_REQS; i++) begin
      grant_history[i] = 0;
    end
    
    // Run for exactly NUM_REQS cycles to see one complete round
    for (int cycle = 0; cycle < NUM_REQS; cycle++) begin
      @(posedge clk);
      
      if (!grant_valid) begin
        $error("Expected grant_valid=1 with all requests active at cycle %0d", cycle);
        error_count++;
      end
      
      // Check that exactly one grant is active
      if ($countones(grant) != 1) begin
        $error("Expected exactly one grant, got %0d at cycle %0d", $countones(grant), cycle);
        error_count++;
      end
      
      // Update history
      for (int i = 0; i < NUM_REQS; i++) begin
        if (grant[i]) grant_history[i]++;
      end
    end
    
    // After one complete round, each requestor should have exactly one grant
    for (int i = 0; i < NUM_REQS; i++) begin
      if (grant_history[i] != 1) begin
        $error("After one round, requestor %0d should have 1 grant, got %0d", i, grant_history[i]);
        error_count++;
      end
    end
    
    req = 0;
    @(posedge clk);
    
    $display("All requests active test completed");
  endtask
  
  // Test 8: Random request patterns
  task test_random_patterns();
    $display("\n--- Test 8: Random Request Patterns ---");
    test_count++;
    
    // Clear grant history
    for (int i = 0; i < NUM_REQS; i++) begin
      grant_history[i] = 0;
    end
    
    // Generate random request patterns
    for (int cycle = 0; cycle < 100; cycle++) begin
      req = $random() & ((1 << NUM_REQS) - 1);
      @(posedge clk);
      
      if (req != 0) begin
        // If there are requests, there should be a grant
        if (!grant_valid) begin
          $error("Expected grant when requests active: req=%b at cycle %0d", req, cycle);
          error_count++;
        end
        
        // Grant should be one-hot
        if ($countones(grant) > 1) begin
          $error("Grant not one-hot: grant=%b at cycle %0d", grant, cycle);
          error_count++;
        end
        
        // Granted request should have been active
        if (!(req & grant)) begin
          $error("Granted inactive request: req=%b, grant=%b at cycle %0d", req, grant, cycle);
          error_count++;
        end
        
        // Update history
        for (int i = 0; i < NUM_REQS; i++) begin
          if (grant[i]) grant_history[i]++;
        end
      end else begin
        // No requests should mean no grant
        if (grant_valid) begin
          $error("Unexpected grant with no requests at cycle %0d", cycle);
          error_count++;
        end
      end
    end
    
    $display("Random patterns grant distribution:");
    for (int i = 0; i < NUM_REQS; i++) begin
      $display("  Requestor %0d: %0d grants", i, grant_history[i]);
    end
    
    req = 0;
    @(posedge clk);
    
    $display("Random patterns test completed");
  endtask
  
  // Continuous monitoring
  always @(posedge clk) begin
    if (rst_n) begin
      // Check grant is one-hot when valid
      if (grant_valid && $countones(grant) != 1) begin
        $error("Grant not one-hot when valid: grant=%b at time %t", grant, $time);
      end
      
      // Check grant_id consistency
      if (grant_valid && !grant[grant_id]) begin
        $error("Grant ID inconsistent with grant vector: grant=%b, grant_id=%0d at time %t", 
               grant, grant_id, $time);
      end
      
      // Check grant implies request
      if (grant_valid && !(req & grant)) begin
        $error("Grant without corresponding request: req=%b, grant=%b at time %t", 
               req, grant, $time);
      end
    end
  end
  
  // Statistics
  logic [31:0] total_grants = 0;
  logic [31:0] total_cycles = 0;
  
  always @(posedge clk) begin
    if (rst_n) begin
      total_cycles++;
      if (grant_valid) total_grants++;
    end else begin
      total_grants = 0;
      total_cycles = 0;
    end
  end
  
  final begin
    $display("\n--- Statistics ---");
    $display("Total cycles: %0d", total_cycles);
    $display("Total grants: %0d", total_grants);
    if (total_cycles > 0) begin
      $display("Grant efficiency: %0.1f%%", (real'(total_grants) / real'(total_cycles)) * 100.0);
    end
  end

endmodule
