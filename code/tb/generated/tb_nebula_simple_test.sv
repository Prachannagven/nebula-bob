`timescale 1ns / 1ps

module tb_nebula_top_traffic();
    import nebula_pkg::*;

    // Clock and reset
    logic clk = 0;
    logic rst_n = 0;
    
    // Parameters
    parameter int MESH_WIDTH = 4;
    parameter int MESH_HEIGHT = 4;
    parameter int NUM_NODES = MESH_WIDTH * MESH_HEIGHT;
    parameter int CONFIG_ADDR_WIDTH = 16;
    parameter int CONFIG_DATA_WIDTH = 32;
    parameter int CHI_REQ_ADDR_WIDTH = 48;
    parameter int CHI_DATA_WIDTH = 512;
    parameter int CHI_BE_WIDTH = 64;

    // Clock generation
    always #5ns clk = ~clk;  // 100MHz clock

    // Configuration interface (tied off for now)
    logic                           config_req_valid = 0;
    logic                           config_req_ready;
    logic                           config_req_write = 0;
    logic [CONFIG_ADDR_WIDTH-1:0]  config_req_addr = 0;
    logic [CONFIG_DATA_WIDTH-1:0]  config_req_data = 0;
    logic                           config_resp_valid;
    logic                           config_resp_ready = 1;
    logic [CONFIG_DATA_WIDTH-1:0]  config_resp_data;
    logic                           config_resp_error;

    // Memory interface (tied off for now)
    logic [NUM_NODES-1:0]                     mem_req_valid;
    logic [NUM_NODES-1:0]                     mem_req_ready = '1;
    logic [NUM_NODES-1:0][CHI_REQ_ADDR_WIDTH-1:0] mem_req_addr;
    logic [NUM_NODES-1:0]                     mem_req_write;
    logic [NUM_NODES-1:0][CHI_DATA_WIDTH-1:0] mem_req_data;
    logic [NUM_NODES-1:0][CHI_BE_WIDTH-1:0]   mem_req_be;

    logic [NUM_NODES-1:0]                     mem_resp_valid = '0;
    logic [NUM_NODES-1:0]                     mem_resp_ready;
    logic [NUM_NODES-1:0][CHI_DATA_WIDTH-1:0] mem_resp_data = '0;
    logic [NUM_NODES-1:0]                     mem_resp_error = '0;

    // AXI interfaces (simplified)
    logic [NUM_NODES-1:0]                     axi_aw_valid = '0;
    logic [NUM_NODES-1:0]                     axi_aw_ready;
    axi_aw_t [NUM_NODES-1:0]                  axi_aw = '0;
    
    logic [NUM_NODES-1:0]                     axi_w_valid = '0;
    logic [NUM_NODES-1:0]                     axi_w_ready;
    axi_w_t [NUM_NODES-1:0]                   axi_w = '0;
    
    logic [NUM_NODES-1:0]                     axi_b_valid;
    logic [NUM_NODES-1:0]                     axi_b_ready = '1;
    axi_b_t [NUM_NODES-1:0]                   axi_b;
    
    logic [NUM_NODES-1:0]                     axi_ar_valid = '0;
    logic [NUM_NODES-1:0]                     axi_ar_ready;
    axi_ar_t [NUM_NODES-1:0]                  axi_ar = '0;
    
    logic [NUM_NODES-1:0]                     axi_r_valid;
    logic [NUM_NODES-1:0]                     axi_r_ready = '1;
    axi_r_t [NUM_NODES-1:0]                   axi_r;

    // CHI interfaces (tied off)
    logic [NUM_NODES-1:0]                     chi_req_valid = '0;
    logic [NUM_NODES-1:0]                     chi_req_ready;
    chi_req_t [NUM_NODES-1:0]                 chi_req = '0;
    
    logic [NUM_NODES-1:0]                     chi_resp_valid;
    logic [NUM_NODES-1:0]                     chi_resp_ready = '1;
    chi_resp_t [NUM_NODES-1:0]                chi_resp;
    
    logic [NUM_NODES-1:0]                     chi_dat_req_valid = '0;
    logic [NUM_NODES-1:0]                     chi_dat_req_ready;
    chi_data_t [NUM_NODES-1:0]                chi_dat_req = '0;
    
    logic [NUM_NODES-1:0]                     chi_dat_resp_valid;
    logic [NUM_NODES-1:0]                     chi_dat_resp_ready = '1;
    chi_data_t [NUM_NODES-1:0]                chi_dat_resp;

    // Status and debug
    logic [31:0]                              system_status;
    logic [31:0]                              error_status;
    logic [31:0]                              performance_counters [15:0];
    logic                                     debug_trace_valid;
    logic [63:0]                              debug_trace_data;
    logic [7:0]                               debug_trace_node_id;

    // DUT instantiation
    nebula_top #(
        .MESH_WIDTH(MESH_WIDTH),
        .MESH_HEIGHT(MESH_HEIGHT)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        
        // Configuration interface
        .config_req_valid(config_req_valid),
        .config_req_ready(config_req_ready),
        .config_req_write(config_req_write),
        .config_req_addr(config_req_addr),
        .config_req_data(config_req_data),
        .config_resp_valid(config_resp_valid),
        .config_resp_ready(config_resp_ready),
        .config_resp_data(config_resp_data),
        .config_resp_error(config_resp_error),
        
        // Memory interface
        .mem_req_valid(mem_req_valid),
        .mem_req_ready(mem_req_ready),
        .mem_req_addr(mem_req_addr),
        .mem_req_write(mem_req_write),
        .mem_req_data(mem_req_data),
        .mem_req_be(mem_req_be),
        .mem_resp_valid(mem_resp_valid),
        .mem_resp_ready(mem_resp_ready),
        .mem_resp_data(mem_resp_data),
        .mem_resp_error(mem_resp_error),
        
        // AXI interfaces
        .axi_aw_valid(axi_aw_valid),
        .axi_aw_ready(axi_aw_ready),
        .axi_aw(axi_aw),
        .axi_w_valid(axi_w_valid),
        .axi_w_ready(axi_w_ready),
        .axi_w(axi_w),
        .axi_b_valid(axi_b_valid),
        .axi_b_ready(axi_b_ready),
        .axi_b(axi_b),
        .axi_ar_valid(axi_ar_valid),
        .axi_ar_ready(axi_ar_ready),
        .axi_ar(axi_ar),
        .axi_r_valid(axi_r_valid),
        .axi_r_ready(axi_r_ready),
        .axi_r(axi_r),
        
        // CHI interfaces
        .chi_req_valid(chi_req_valid),
        .chi_req_ready(chi_req_ready),
        .chi_req(chi_req),
        .chi_resp_valid(chi_resp_valid),
        .chi_resp_ready(chi_resp_ready),
        .chi_resp(chi_resp),
        .chi_dat_req_valid(chi_dat_req_valid),
        .chi_dat_req_ready(chi_dat_req_ready),
        .chi_dat_req(chi_dat_req),
        .chi_dat_resp_valid(chi_dat_resp_valid),
        .chi_dat_resp_ready(chi_dat_resp_ready),
        .chi_dat_resp(chi_dat_resp),
        
        // Status and debug
        .system_status(system_status),
        .error_status(error_status),
        .performance_counters(performance_counters),
        .debug_trace_valid(debug_trace_valid),
        .debug_trace_data(debug_trace_data),
        .debug_trace_node_id(debug_trace_node_id)
    );

    // Test sequence
    initial begin
        $dumpfile("tb_nebula_top.vcd");
        $dumpvars(0, tb_nebula_top_traffic);
        
        // Reset sequence
        $display("Starting test...");
        rst_n = 0;
        repeat(10) @(posedge clk);
        rst_n = 1;
        repeat(5) @(posedge clk);
        
        $display("Reset completed, DUT running...");
        
        // Let it run for a while
        repeat(100) @(posedge clk);
        
        $display("Test completed successfully!");
        $finish;
    end

    // Timeout watchdog
    initial begin
        #10ms;
        $display("ERROR: Test timeout!");
        $finish;
    end

endmodule
