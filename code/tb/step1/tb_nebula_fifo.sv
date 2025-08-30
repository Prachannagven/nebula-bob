/**
 * Testbench for nebula_fifo module
 * 
 * Tests:
 * - Basic read/write operations
 * - Full/empty flag behavior
 * - Almost full/empty thresholds
 * - Data integrity
 * - Overflow/underflow protection
 * - Count accuracy
 */

`timescale 1ns/1ps

import nebula_pkg::*;

module tb_nebula_fifo;

  // Parameters
  parameter int DATA_WIDTH = 32;
  parameter int DEPTH = 8;
  parameter int ALMOST_FULL_THRESH = DEPTH - 2;
  parameter int ALMOST_EMPTY_THRESH = 2;
  
  // Clock and reset
  logic clk;
  logic rst_n;
  
  // FIFO interface
  logic                        wr_en;
  logic [DATA_WIDTH-1:0]       wr_data;
  logic                        full;
  logic                        almost_full;
  logic                        rd_en;
  logic [DATA_WIDTH-1:0]       rd_data;
  logic                        empty;
  logic                        almost_empty;
  logic [$clog2(DEPTH+1)-1:0] count;
  
  // Test variables
  logic [DATA_WIDTH-1:0] test_data_queue[$];
  logic [DATA_WIDTH-1:0] expected_data;
  int error_count = 0;
  int test_count = 0;
  
  // DUT instantiation
  nebula_fifo #(
    .DATA_WIDTH(DATA_WIDTH),
    .DEPTH(DEPTH),
    .ALMOST_FULL_THRESH(ALMOST_FULL_THRESH),
    .ALMOST_EMPTY_THRESH(ALMOST_EMPTY_THRESH)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .wr_en(wr_en),
    .wr_data(wr_data),
    .full(full),
    .almost_full(almost_full),
    .rd_en(rd_en),
    .rd_data(rd_data),
    .empty(empty),
    .almost_empty(almost_empty),
    .count(count)
  );
  
  // Clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end
  
  // Test stimulus
  initial begin
    $display("=== NEBULA FIFO TESTBENCH START ===");
    
    // Initialize
    rst_n = 0;
    wr_en = 0;
    rd_en = 0;
    wr_data = 0;
    
    // Reset
    repeat(3) @(posedge clk);
    rst_n = 1;
    @(posedge clk);
    
    // Test 1: Initial state
    test_initial_state();
    
    // Test 2: Basic write operations
    test_basic_write();
    
    // Test 3: Basic read operations  
    test_basic_read();
    
    // Test 4: Full/empty behavior
    test_full_empty();
    
    // Test 5: Almost full/empty thresholds
    test_almost_flags();
    
    // Test 6: Simultaneous read/write
    test_simultaneous_rw();
    
    // Test 7: Data integrity
    test_data_integrity();
    
    // Test 8: Overflow/underflow protection
    test_overflow_underflow();
    
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
    
    if (empty !== 1'b1) begin
      $error("Expected empty=1, got %b", empty);
      error_count++;
    end
    
    if (full !== 1'b0) begin
      $error("Expected full=0, got %b", full);
      error_count++;
    end
    
    if (count !== 0) begin
      $error("Expected count=0, got %0d", count);
      error_count++;
    end
    
    $display("Initial state test completed");
  endtask
  
  // Test 2: Basic write operations
  task test_basic_write();
    $display("\n--- Test 2: Basic Write Operations ---");
    test_count++;
    
    // Write single item
    @(posedge clk);
    wr_en = 1;
    wr_data = 32'hDEADBEEF;
    test_data_queue.push_back(wr_data);
    
    @(posedge clk);
    wr_en = 0;
    
    @(posedge clk);
    if (empty !== 1'b0) begin
      $error("Expected empty=0 after write, got %b", empty);
      error_count++;
    end
    
    if (count !== 1) begin
      $error("Expected count=1 after write, got %0d", count);
      error_count++;
    end
    
    $display("Basic write test completed");
  endtask
  
  // Test 3: Basic read operations
  task test_basic_read();
    $display("\n--- Test 3: Basic Read Operations ---");
    test_count++;
    
    // Read single item
    @(posedge clk);
    rd_en = 1;
    
    @(posedge clk);
    rd_en = 0;
    expected_data = test_data_queue.pop_front();
    
    if (rd_data !== expected_data) begin
      $error("Data mismatch: expected %h, got %h", expected_data, rd_data);
      error_count++;
    end
    
    @(posedge clk);
    if (empty !== 1'b1) begin
      $error("Expected empty=1 after read, got %b", empty);
      error_count++;
    end
    
    if (count !== 0) begin
      $error("Expected count=0 after read, got %0d", count);
      error_count++;
    end
    
    $display("Basic read test completed");
  endtask
  
  // Test 4: Full/empty behavior
  task test_full_empty();
    $display("\n--- Test 4: Full/Empty Behavior ---");
    test_count++;
    
    // Fill FIFO completely
    for (int i = 0; i < DEPTH; i++) begin
      @(posedge clk);
      wr_en = 1;
      wr_data = i + 100;
      test_data_queue.push_back(wr_data);
      
      if (i == DEPTH-1) begin
        @(posedge clk);
        if (full !== 1'b1) begin
          $error("Expected full=1 when FIFO is full, got %b", full);
          error_count++;
        end
      end
    end
    
    @(posedge clk);
    wr_en = 0;
    
    // Empty FIFO completely
    for (int i = 0; i < DEPTH; i++) begin
      @(posedge clk);
      rd_en = 1;
      
      @(posedge clk);
      rd_en = 0;
      expected_data = test_data_queue.pop_front();
      
      if (rd_data !== expected_data) begin
        $error("Data mismatch at position %0d: expected %h, got %h", i, expected_data, rd_data);
        error_count++;
      end
    end
    
    @(posedge clk);
    if (empty !== 1'b1) begin
      $error("Expected empty=1 after emptying FIFO, got %b", empty);
      error_count++;
    end
    
    $display("Full/empty behavior test completed");
  endtask
  
  // Test 5: Almost full/empty thresholds
  task test_almost_flags();
    $display("\n--- Test 5: Almost Full/Empty Thresholds ---");
    test_count++;
    
    // Test almost_empty threshold
    for (int i = 0; i <= ALMOST_EMPTY_THRESH; i++) begin
      @(posedge clk);
      wr_en = 1;
      wr_data = i + 200;
      test_data_queue.push_back(wr_data);
      
      @(posedge clk);
      wr_en = 0;
      
      if (count <= ALMOST_EMPTY_THRESH && almost_empty !== 1'b1) begin
        $error("Expected almost_empty=1 at count=%0d, got %b", count, almost_empty);
        error_count++;
      end
    end
    
    // Fill to almost full threshold
    for (int i = ALMOST_EMPTY_THRESH + 1; i < ALMOST_FULL_THRESH; i++) begin
      @(posedge clk);
      wr_en = 1;
      wr_data = i + 200;
      test_data_queue.push_back(wr_data);
    end
    
    @(posedge clk);
    wr_en = 0;
    
    @(posedge clk);
    if (almost_full !== 1'b1) begin
      $error("Expected almost_full=1 at threshold, got %b", almost_full);
      error_count++;
    end
    
    // Clear queue for next test
    while (test_data_queue.size() > 0) begin
      @(posedge clk);
      rd_en = 1;
      @(posedge clk);
      rd_en = 0;
      void'(test_data_queue.pop_front());
    end
    
    $display("Almost flags test completed");
  endtask
  
  // Test 6: Simultaneous read/write
  task test_simultaneous_rw();
    $display("\n--- Test 6: Simultaneous Read/Write ---");
    test_count++;
    
    // Add some data first
    for (int i = 0; i < 3; i++) begin
      @(posedge clk);
      wr_en = 1;
      wr_data = i + 300;
      test_data_queue.push_back(wr_data);
    end
    
    @(posedge clk);
    wr_en = 0;
    
    // Simultaneous read/write
    begin
      automatic logic [7:0] initial_count;
      initial_count = count;
      @(posedge clk);
      wr_en = 1;
      rd_en = 1;
      wr_data = 32'hCAFEBABE;
      
      @(posedge clk);
      wr_en = 0;
      rd_en = 0;
      
      expected_data = test_data_queue.pop_front();
      test_data_queue.push_back(32'hCAFEBABE);
      
      if (rd_data !== expected_data) begin
        $error("Simultaneous R/W data mismatch: expected %h, got %h", expected_data, rd_data);
        error_count++;
      end
    
    if (count !== initial_count) begin
      $error("Count should remain same during simultaneous R/W: expected %0d, got %0d", initial_count, count);
      error_count++;
    end
    end // end of automatic begin block
    
    // Clear remaining data
    while (test_data_queue.size() > 0) begin
      @(posedge clk);
      rd_en = 1;
      @(posedge clk);
      rd_en = 0;
      void'(test_data_queue.pop_front());
    end
    
    $display("Simultaneous R/W test completed");
  endtask
  
  // Test 7: Data integrity
  task test_data_integrity();
    $display("\n--- Test 7: Data Integrity ---");
    test_count++;
    
    begin
      automatic logic [DATA_WIDTH-1:0] test_patterns[8];
      test_patterns[0] = 32'h00000000;
      test_patterns[1] = 32'hFFFFFFFF;
      test_patterns[2] = 32'hAAAAAAAA;
      test_patterns[3] = 32'h55555555;
      test_patterns[4] = 32'hDEADBEEF;
      test_patterns[5] = 32'hCAFEBABE;
      test_patterns[6] = 32'h12345678;
      test_patterns[7] = 32'h87654321;
      
      // Write all patterns
      foreach (test_patterns[i]) begin
      @(posedge clk);
      wr_en = 1;
      wr_data = test_patterns[i];
      test_data_queue.push_back(wr_data);
    end
    
    @(posedge clk);
    wr_en = 0;
    
    // Read and verify all patterns
    foreach (test_patterns[i]) begin
      @(posedge clk);
      rd_en = 1;
      
      @(posedge clk);
      rd_en = 0;
      expected_data = test_data_queue.pop_front();
      
      if (rd_data !== expected_data) begin
        $error("Pattern %0d mismatch: expected %h, got %h", i, expected_data, rd_data);
        error_count++;
      end
    end
    end // end of automatic begin block
    
    $display("Data integrity test completed");
  endtask
  
  // Test 8: Overflow/underflow protection
  task test_overflow_underflow();
    $display("\n--- Test 8: Overflow/Underflow Protection ---");
    test_count++;
    
    // Test write when full (should be ignored)
    // First fill FIFO
    for (int i = 0; i < DEPTH; i++) begin
      @(posedge clk);
      wr_en = 1;
      wr_data = i + 400;
    end
    
    @(posedge clk);
    wr_en = 1;
    wr_data = 32'hDEADDEAD; // This should be ignored
    
    @(posedge clk);
    wr_en = 0;
    
    if (count !== DEPTH) begin
      $error("Count should remain %0d when writing to full FIFO, got %0d", DEPTH, count);
      error_count++;
    end
    
    // Empty FIFO
    for (int i = 0; i < DEPTH; i++) begin
      @(posedge clk);
      rd_en = 1;
      @(posedge clk);
      rd_en = 0;
    end
    
    // Test read when empty (should not change state)
    @(posedge clk);
    rd_en = 1;
    
    @(posedge clk);
    rd_en = 0;
    
    if (count !== 0) begin
      $error("Count should remain 0 when reading from empty FIFO, got %0d", count);
      error_count++;
    end
    
    if (empty !== 1'b1) begin
      $error("Empty flag should remain 1 when reading from empty FIFO, got %b", empty);
      error_count++;
    end
    
    $display("Overflow/underflow protection test completed");
  endtask
  
  // Monitor for unexpected changes
  always @(posedge clk) begin
    if (rst_n) begin
      // Check flag consistency
      if (count == 0 && !empty) begin
        $error("Count=0 but empty=0 at time %t", $time);
      end
      
      if (count == DEPTH && !full) begin
        $error("Count=%0d but full=0 at time %t", DEPTH, $time);
      end
      
      if (count > DEPTH) begin
        $error("Count exceeds DEPTH: %0d > %0d at time %t", count, DEPTH, $time);
      end
    end
  end

endmodule
