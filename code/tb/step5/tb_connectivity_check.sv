`timescale 1ns / 1ps

module tb_connectivity_check;
  import nebula_pkg::*;
  
  parameter MESH_SIZE_X = 2;
  parameter MESH_SIZE_Y = 2;
  parameter CLK_PERIOD = 10000; // 10ns = 100MHz
  
  // Clock and reset
  logic clk = 0;
  logic rst_n;
  
  // Local interfaces for testing
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_in_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_in;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_in_ready;
  
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_out_valid;
  noc_flit_t [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_out;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] local_flit_out_ready;
  
  // Status and error monitoring
  error_code_e [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0] error_status;
  logic [MESH_SIZE_X-1:0][MESH_SIZE_Y-1:0][NUM_PORTS-1:0][NUM_VCS-1:0] vc_status;
  
  // Instantiate mesh
  nebula_mesh_top #(
    .MESH_SIZE_X(MESH_SIZE_X),
    .MESH_SIZE_Y(MESH_SIZE_Y)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    .local_flit_in_valid(local_flit_in_valid),
    .local_flit_in(local_flit_in),
    .local_flit_in_ready(local_flit_in_ready),
    .local_flit_out_valid(local_flit_out_valid),
    .local_flit_out(local_flit_out),
    .local_flit_out_ready(local_flit_out_ready),
    .error_status(error_status),
    .vc_status(vc_status)
  );
  
  // Clock generation
  always #(CLK_PERIOD/2) clk = ~clk;
  
  // Test cycle counter
  int cycle_count = 0;
  always @(posedge clk) begin
    if (rst_n) cycle_count <= cycle_count + 1;
  end
  
  initial begin
    $display("=== CONNECTIVITY CHECK TEST STARTING ===");
    $display("Checking ready signal connectivity in 2x2 mesh");
    
    // Initialize inputs
    local_flit_in_valid = '0;
    local_flit_in = '0;
    local_flit_out_ready = '1; // All local ports ready to receive
    rst_n = 1'b0;
    
    // Reset
    repeat(5) @(posedge clk);
    rst_n = 1'b1;
    repeat(5) @(posedge clk);
    
    // Check initial ready states
    $display("[CHECK] @%0dns: Initial ready signal states:", $time);
    $display("  Router[0][0] local_ready=%b", local_flit_in_ready[0][0]);
    $display("  Router[1][0] local_ready=%b", local_flit_in_ready[1][0]);
    $display("  Router[0][1] local_ready=%b", local_flit_in_ready[0][1]);
    $display("  Router[1][1] local_ready=%b", local_flit_in_ready[1][1]);
    
    // Check internal router port ready signals directly
    $display("[CHECK] Direct router port ready signals:");
    $display("  R[0][0] PORT_EAST ready=%b", dut.router_flit_out_ready[0][0][PORT_EAST]);
    $display("  R[1][0] PORT_WEST ready=%b", dut.router_flit_in_ready[1][0][PORT_WEST]);
    $display("  R[1][0] PORT_NORTH ready=%b", dut.router_flit_in_ready[1][0][PORT_NORTH]);
    $display("  R[1][0] PORT_SOUTH ready=%b", dut.router_flit_in_ready[1][0][PORT_SOUTH]);
    $display("  R[1][0] PORT_LOCAL ready=%b", dut.router_flit_in_ready[1][0][PORT_LOCAL]);
    
    repeat(10) @(posedge clk);
    
    $display("=== CONNECTIVITY CHECK TEST COMPLETE ===");
    $finish;
  end
  
endmodule
