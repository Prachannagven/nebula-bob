/**
 * Testbench for nebula_credit_flow_ctrl module
 * 
 * Tests:
 * - Initial credit count
 * - Credit consumption on send
 * - Credit return mechanism
 * - Flow control behavior
 * - Simultaneous send and return
 * - Credit underflow/overflow protection
 */

`timescale 1ns/1ps

import nebula_pkg::*;

module tb_nebula_credit_flow_ctrl;

  // Parameters
  parameter int MAX_CREDITS = 8;
  parameter int CREDIT_WIDTH = $clog2(MAX_CREDITS + 1);
  
  // Clock and reset
  logic clk;
  logic rst_n;
  
  // DUT interface
  logic                      send_flit;
  logic                      credits_available;
  logic                      credit_return;
  logic [CREDIT_WIDTH-1:0]   credit_count;
  
  // Test variables
  int error_count = 0;
  int test_count = 0;
  
  // DUT instantiation
  nebula_credit_flow_ctrl #(
    .MAX_CREDITS(MAX_CREDITS),
    .CREDIT_WIDTH(CREDIT_WIDTH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .send_flit(send_flit),
    .credits_available(credits_available),
    .credit_return(credit_return),
    .credit_count(credit_count)
  );
  
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // Test stimulus
  initial begin
    $display("=== NEBULA CREDIT FLOW CONTROL TESTBENCH START ===");
    
    // Initialize
    rst_n = 0;
    send_flit = 0;
    credit_return = 0;
    
    // Reset
    repeat(3) @(posedge clk);
    rst_n = 1;
    @(posedge clk);
    
    // Test 1: Initial state
    test_initial_state();
    
    // Test 2: Basic credit consumption
    test_credit_consumption();
    
    // Test 3: Credit return mechanism
    test_credit_return();
    
    // Test 4: Flow control behavior
    test_flow_control();
    
    // Test 5: Simultaneous send and return
    test_simultaneous_operations();
    
    // Test 6: Credit boundary conditions
    test_boundary_conditions();
    
    // Test 7: Rapid send/return cycles
    test_rapid_cycles();
    
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
  
  // Test 1: Initial state
  task test_initial_state();
    $display("\n--- Test 1: Initial State ---");
    test_count++;
    
    if (credit_count !== MAX_CREDITS) begin
      $error("Expected initial credit_count=%0d, got %0d", MAX_CREDITS, credit_count);
      error_count++;
    end
    
    if (credits_available !== 1'b1) begin
      $error("Expected credits_available=1 initially, got %b", credits_available);
      error_count++;
    end
    
    $display("Initial state: credit_count=%0d, credits_available=%b", credit_count, credits_available);
    $display("Initial state test completed");
  endtask
  
  // Test 2: Basic credit consumption
  task test_credit_consumption();
    $display("\n--- Test 2: Basic Credit Consumption ---");
    test_count++;
    
    begin
      automatic logic [CREDIT_WIDTH-1:0] initial_credits;
      initial_credits = credit_count;
    
    // Send a flit
    @(posedge clk);
    send_flit = 1;
    
    @(posedge clk);
    send_flit = 0;
    
    @(posedge clk);
    if (credit_count !== initial_credits - 1) begin
      $error("Expected credit_count=%0d after send, got %0d", initial_credits - 1, credit_count);
      error_count++;
    end
    
    if (!credits_available) begin
      $error("Expected credits_available=1 after single send, got %b", credits_available);
      error_count++;
    end
    end // end of automatic begin block
    
    $display("Credit consumption test completed");
  endtask
  
  // Test 3: Credit return mechanism
  task test_credit_return();
    $display("\n--- Test 3: Credit Return Mechanism ---");
    test_count++;
    
    begin
      automatic logic [CREDIT_WIDTH-1:0] initial_credits;
      initial_credits = credit_count;
    
    // Return a credit
    @(posedge clk);
    credit_return = 1;
    
    @(posedge clk);
    credit_return = 0;
    
    @(posedge clk);
    if (credit_count !== initial_credits + 1) begin
      $error("Expected credit_count=%0d after return, got %0d", initial_credits + 1, credit_count);
      error_count++;
    end
    end // end of automatic begin block
    
    $display("Credit return test completed");
  endtask
  
  // Test 4: Flow control behavior
  task test_flow_control();
    $display("\n--- Test 4: Flow Control Behavior ---");
    test_count++;
    
    // Consume all credits
    while (credits_available) begin
      @(posedge clk);
      send_flit = 1;
      @(posedge clk);
      send_flit = 0;
      @(posedge clk);
    end
    
    // Verify no credits available
    if (credits_available !== 1'b0) begin
      $error("Expected credits_available=0 when no credits, got %b", credits_available);
      error_count++;
    end
    
    if (credit_count !== 0) begin
      $error("Expected credit_count=0 when no credits, got %0d", credit_count);
      error_count++;
    end
    
    // Try to send when no credits (should have no effect)
    @(posedge clk);
    send_flit = 1;
    
    @(posedge clk);
    send_flit = 0;
    
    @(posedge clk);
    if (credit_count !== 0) begin
      $error("Credit count should remain 0 when sending without credits, got %0d", credit_count);
      error_count++;
    end
    
    // Return one credit and verify availability
    @(posedge clk);
    credit_return = 1;
    
    @(posedge clk);
    credit_return = 0;
    
    @(posedge clk);
    if (!credits_available) begin
      $error("Expected credits_available=1 after credit return, got %b", credits_available);
      error_count++;
    end
    
    $display("Flow control test completed");
  endtask
  
  // Test 5: Simultaneous send and return
  task test_simultaneous_operations();
    $display("\n--- Test 5: Simultaneous Send and Return ---");
    test_count++;
    
    // Ensure we have some credits but not maximum
    while (credit_count < 4) begin
      @(posedge clk);
      credit_return = 1;
      @(posedge clk);
      credit_return = 0;
      @(posedge clk);
    end
    
    begin
      automatic logic [CREDIT_WIDTH-1:0] initial_credits;
      initial_credits = credit_count;
    
    // Simultaneous send and return
    @(posedge clk);
    send_flit = 1;
    credit_return = 1;
    
    @(posedge clk);
    send_flit = 0;
    credit_return = 0;
    
    @(posedge clk);
    if (credit_count !== initial_credits) begin
      $error("Credit count should remain unchanged during simultaneous send/return: expected %0d, got %0d", 
             initial_credits, credit_count);
      error_count++;
    end
    end  // end automatic begin block
    
    $display("Simultaneous operations test completed");
  endtask
  
  // Test 6: Boundary conditions
  task test_boundary_conditions();
    $display("\n--- Test 6: Boundary Conditions ---");
    test_count++;
    
    // Reset to full credits
    rst_n = 0;
    @(posedge clk);
    rst_n = 1;
    @(posedge clk);
    
    // Try to return credit when at maximum (should be ignored)
    @(posedge clk);
    credit_return = 1;
    
    @(posedge clk);
    credit_return = 0;
    
    @(posedge clk);
    if (credit_count !== MAX_CREDITS) begin
      $error("Credit count should remain at max when returning at full: expected %0d, got %0d", 
             MAX_CREDITS, credit_count);
      error_count++;
    end
    
    // Consume all credits
    for (int i = 0; i < MAX_CREDITS; i++) begin
      @(posedge clk);
      send_flit = 1;
      @(posedge clk);
      send_flit = 0;
      @(posedge clk);
    end
    
    // Verify zero credits
    if (credit_count !== 0) begin
      $error("Expected credit_count=0 after consuming all, got %0d", credit_count);
      error_count++;
    end
    
    if (credits_available !== 1'b0) begin
      $error("Expected credits_available=0 when no credits, got %b", credits_available);
      error_count++;
    end
    
    $display("Boundary conditions test completed");
  endtask
  
  // Test 7: Rapid send/return cycles
  task test_rapid_cycles();
    $display("\n--- Test 7: Rapid Send/Return Cycles ---");
    test_count++;
    
    // Return credits to have some available
    for (int i = 0; i < MAX_CREDITS/2; i++) begin
      @(posedge clk);
      credit_return = 1;
      @(posedge clk);
      credit_return = 0;
      @(posedge clk);
    end
    
    // Rapid alternating send/return for stress test
    for (int i = 0; i < 20; i++) begin
      @(posedge clk);
      send_flit = (i % 2 == 0);
      credit_return = (i % 2 == 1);
    end
    
    @(posedge clk);
    send_flit = 0;
    credit_return = 0;
    
    @(posedge clk);
    
    // Verify credits are within valid range
    if (credit_count > MAX_CREDITS) begin
      $error("Credit count exceeded maximum during rapid cycles: got %0d", credit_count);
      error_count++;
    end
    
    // Verify credits_available is consistent with count
    if ((credit_count > 0) !== credits_available) begin
      $error("credits_available inconsistent with count: count=%0d, available=%b", 
             credit_count, credits_available);
      error_count++;
    end
    
    $display("Rapid cycles test completed");
  endtask
  
  // Monitor for consistency
  always @(posedge clk) begin
    if (rst_n) begin
      // Check credit_count bounds
      if (credit_count > MAX_CREDITS) begin
        $error("Credit count exceeds maximum: %0d > %0d at time %t", credit_count, MAX_CREDITS, $time);
      end
      
      // Check credits_available consistency
      if ((credit_count > 0) !== credits_available) begin
        $error("credits_available inconsistent: count=%0d, available=%b at time %t", 
               credit_count, credits_available, $time);
      end
      
      // Check for illegal send when no credits
      if (send_flit && !credits_available) begin
        $warning("Attempting to send flit without credits at time %t", $time);
      end
    end
  end
  
  // Performance monitoring
  logic [31:0] total_sends = 0;
  logic [31:0] total_returns = 0;
  
  always @(posedge clk) begin
    if (rst_n) begin
      if (send_flit && credits_available) total_sends++;
      if (credit_return) total_returns++;
    end else begin
      total_sends = 0;
      total_returns = 0;
    end
  end
  
  final begin
    $display("\n--- Performance Stats ---");
    $display("Total sends: %0d", total_sends);
    $display("Total returns: %0d", total_returns);
    $display("Net credits consumed: %0d", total_sends - total_returns);
  end

endmodule
