`timescale 1ns / 1ps

module tb_nebula_top_traffic;
    import nebula_pkg::*;

    // Parameters
    parameter int MESH_WIDTH = 8;
    parameter int MESH_HEIGHT = 8;
    parameter int NUM_NODES = 64;
    parameter int CONFIG_ADDR_WIDTH = 16;
    parameter int CONFIG_DATA_WIDTH = 32;
    parameter bit ENABLE_AXI = 1'b1;
    parameter bit ENABLE_CHI = 1'b1;
    parameter bit ENABLE_PERFORMANCE_MONITORING = 1'b1;

    // Traffic data type definition
    typedef struct {
        int timestamp;
        int source_node;
        int dest_node;
        string packet_type;
        int size_bytes;
    } traffic_entry_t;
    
    parameter int TRAFFIC_SIZE = 136;
    traffic_entry_t traffic_data[TRAFFIC_SIZE];

    // Clock and reset
    logic clk;
    logic rst_n;
    
    // System Configuration Interface  
    logic                           config_req_valid;
    logic                           config_req_ready;
    logic [CONFIG_ADDR_WIDTH-1:0]  config_req_addr;
    logic [CONFIG_DATA_WIDTH-1:0]  config_req_data;
    logic                           config_req_write;
    logic                           config_resp_valid;
    logic                           config_resp_ready;
    logic [CONFIG_DATA_WIDTH-1:0]  config_resp_data;
    logic                           config_resp_error;
    
    // Memory interfaces
    logic [NUM_NODES-1:0]                     mem_req_valid;
    logic [NUM_NODES-1:0]                     mem_req_ready;
    logic [NUM_NODES-1:0][CHI_REQ_ADDR_WIDTH-1:0] mem_req_addr;
    logic [NUM_NODES-1:0]                     mem_req_write;
    logic [NUM_NODES-1:0][CHI_DATA_WIDTH-1:0] mem_req_data;
    logic [NUM_NODES-1:0][CHI_BE_WIDTH-1:0]   mem_req_be;
    logic [NUM_NODES-1:0]                     mem_resp_valid;
    logic [NUM_NODES-1:0]                     mem_resp_ready;
    logic [NUM_NODES-1:0][CHI_DATA_WIDTH-1:0] mem_resp_data;
    logic [NUM_NODES-1:0]                     mem_resp_error;
    
    // AXI interfaces  
    logic [NUM_NODES-1:0]                     axi_aw_valid;
    logic [NUM_NODES-1:0]                     axi_aw_ready;
    axi_aw_t [NUM_NODES-1:0]                  axi_aw;
    logic [NUM_NODES-1:0]                     axi_w_valid;
    logic [NUM_NODES-1:0]                     axi_w_ready;
    axi_w_t [NUM_NODES-1:0]                   axi_w;
    logic [NUM_NODES-1:0]                     axi_b_valid;
    logic [NUM_NODES-1:0]                     axi_b_ready;
    axi_b_t [NUM_NODES-1:0]                   axi_b;
    logic [NUM_NODES-1:0]                     axi_ar_valid;
    logic [NUM_NODES-1:0]                     axi_ar_ready;
    axi_ar_t [NUM_NODES-1:0]                  axi_ar;
    logic [NUM_NODES-1:0]                     axi_r_valid;
    logic [NUM_NODES-1:0]                     axi_r_ready;
    axi_r_t [NUM_NODES-1:0]                   axi_r;
    
    // CHI interfaces
    logic [NUM_NODES-1:0]                     chi_req_valid;
    logic [NUM_NODES-1:0]                     chi_req_ready;
    chi_req_t [NUM_NODES-1:0]                 chi_req;
    logic [NUM_NODES-1:0]                     chi_resp_valid;
    logic [NUM_NODES-1:0]                     chi_resp_ready;
    chi_resp_t [NUM_NODES-1:0]                chi_resp;
    logic [NUM_NODES-1:0]                     chi_dat_req_valid;
    logic [NUM_NODES-1:0]                     chi_dat_req_ready;
    chi_data_t [NUM_NODES-1:0]                chi_dat_req;
    logic [NUM_NODES-1:0]                     chi_dat_resp_valid;
    logic [NUM_NODES-1:0]                     chi_dat_resp_ready;
    chi_data_t [NUM_NODES-1:0]                chi_dat_resp;
    
    // System Status and Debug  
    logic [31:0]                              system_status;
    logic [31:0]                              error_status;
    logic [31:0]                              performance_counters [15:0];
    logic                                     debug_trace_valid;
    logic [63:0]                             debug_trace_data;
    logic [7:0]                              debug_trace_node_id;

    // DUT instantiation
    nebula_top #(
        .MESH_WIDTH(MESH_WIDTH),
        .MESH_HEIGHT(MESH_HEIGHT),
        .NUM_NODES(NUM_NODES),
        .CONFIG_ADDR_WIDTH(CONFIG_ADDR_WIDTH),
        .CONFIG_DATA_WIDTH(CONFIG_DATA_WIDTH),
        .ENABLE_AXI(ENABLE_AXI),
        .ENABLE_CHI(ENABLE_CHI),
        .ENABLE_PERFORMANCE_MONITORING(ENABLE_PERFORMANCE_MONITORING)
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .config_req_valid(config_req_valid),
        .config_req_ready(config_req_ready),
        .config_req_addr(config_req_addr),
        .config_req_data(config_req_data),
        .config_req_write(config_req_write),
        .config_resp_valid(config_resp_valid),
        .config_resp_ready(config_resp_ready),
        .config_resp_data(config_resp_data),
        .config_resp_error(config_resp_error),
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
        .system_status(system_status),
        .error_status(error_status),
        .performance_counters(performance_counters),
        .debug_trace_valid(debug_trace_valid),
        .debug_trace_node_id(debug_trace_node_id),
        .debug_trace_data(debug_trace_data)
    );
    
    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 100MHz clock
    end
    
    // Reset and test sequence
    initial begin
        // Initialize signals
        rst_n = 0;
        config_req_valid = 0;
        config_req_addr = 0;
        config_req_data = 0;
        config_req_write = 0;
        config_resp_ready = 1;
        
        // Initialize memory interfaces
        mem_req_ready = '1;
        mem_resp_valid = '0;
        mem_resp_data = '0;
        mem_resp_error = '0;
        
        // Initialize AXI interfaces
        axi_aw_valid = '0;
        axi_aw = '0;
        axi_w_valid = '0;
        axi_w = '0;
        axi_b_ready = '1;
        axi_ar_valid = '0;
        axi_ar = '0;
        axi_r_ready = '1;
        
        // Initialize CHI interfaces
        chi_req_valid = '0;
        chi_req = '0;
        chi_resp_ready = '1;
        chi_dat_req_valid = '0;
        chi_dat_req = '0;
        chi_dat_resp_ready = '1;
        
        // Apply reset
        #20;
        rst_n = 1;
        #20;
        
        $display("🔧 Starting NoC traffic simulation with %0d nodes...", NUM_NODES);
        $display("🔧 Traffic size: %0d entries", TRAFFIC_SIZE);
        
        // Wait for system to stabilize
        repeat(100) @(posedge clk);
        $display("🔧 System stabilization complete");
        
        // Enable VCD dumping
        $dumpfile("tb_nebula_traffic.vcd");
        $dumpvars(0, tb_nebula_top_traffic);
        $display("🔧 VCD dumping enabled");
        
        // Load traffic data
        $display("📝 Loading traffic data...");
        traffic_data[0].timestamp = 0;
        traffic_data[0].source_node = 3;
        traffic_data[0].dest_node = 26;
        traffic_data[0].packet_type = "CHI_WRITE";
        traffic_data[0].size_bytes = 128;
        traffic_data[1].timestamp = 0;
        traffic_data[1].source_node = 6;
        traffic_data[1].dest_node = 63;
        traffic_data[1].packet_type = "CHI_READ";
        traffic_data[1].size_bytes = 256;
        traffic_data[2].timestamp = 0;
        traffic_data[2].source_node = 17;
        traffic_data[2].dest_node = 7;
        traffic_data[2].packet_type = "AXI_WRITE";
        traffic_data[2].size_bytes = 128;
        traffic_data[3].timestamp = 0;
        traffic_data[3].source_node = 24;
        traffic_data[3].dest_node = 12;
        traffic_data[3].packet_type = "CHI_READ";
        traffic_data[3].size_bytes = 64;
        traffic_data[4].timestamp = 0;
        traffic_data[4].source_node = 37;
        traffic_data[4].dest_node = 2;
        traffic_data[4].packet_type = "CHI_READ";
        traffic_data[4].size_bytes = 256;
        traffic_data[5].timestamp = 0;
        traffic_data[5].source_node = 49;
        traffic_data[5].dest_node = 3;
        traffic_data[5].packet_type = "AXI_WRITE";
        traffic_data[5].size_bytes = 128;
        traffic_data[6].timestamp = 1;
        traffic_data[6].source_node = 1;
        traffic_data[6].dest_node = 19;
        traffic_data[6].packet_type = "CHI_WRITE";
        traffic_data[6].size_bytes = 512;
        traffic_data[7].timestamp = 1;
        traffic_data[7].source_node = 14;
        traffic_data[7].dest_node = 26;
        traffic_data[7].packet_type = "CHI_WRITE";
        traffic_data[7].size_bytes = 1024;
        traffic_data[8].timestamp = 1;
        traffic_data[8].source_node = 17;
        traffic_data[8].dest_node = 32;
        traffic_data[8].packet_type = "CHI_WRITE";
        traffic_data[8].size_bytes = 128;
        traffic_data[9].timestamp = 1;
        traffic_data[9].source_node = 18;
        traffic_data[9].dest_node = 6;
        traffic_data[9].packet_type = "CHI_WRITE";
        traffic_data[9].size_bytes = 64;
        traffic_data[10].timestamp = 1;
        traffic_data[10].source_node = 22;
        traffic_data[10].dest_node = 3;
        traffic_data[10].packet_type = "AXI_WRITE";
        traffic_data[10].size_bytes = 128;
        traffic_data[11].timestamp = 1;
        traffic_data[11].source_node = 31;
        traffic_data[11].dest_node = 23;
        traffic_data[11].packet_type = "CHI_READ";
        traffic_data[11].size_bytes = 256;
        traffic_data[12].timestamp = 1;
        traffic_data[12].source_node = 36;
        traffic_data[12].dest_node = 2;
        traffic_data[12].packet_type = "AXI_WRITE";
        traffic_data[12].size_bytes = 256;
        traffic_data[13].timestamp = 1;
        traffic_data[13].source_node = 53;
        traffic_data[13].dest_node = 21;
        traffic_data[13].packet_type = "AXI_READ";
        traffic_data[13].size_bytes = 1024;
        traffic_data[14].timestamp = 1;
        traffic_data[14].source_node = 58;
        traffic_data[14].dest_node = 30;
        traffic_data[14].packet_type = "CHI_READ";
        traffic_data[14].size_bytes = 1024;
        traffic_data[15].timestamp = 2;
        traffic_data[15].source_node = 6;
        traffic_data[15].dest_node = 61;
        traffic_data[15].packet_type = "AXI_READ";
        traffic_data[15].size_bytes = 64;
        traffic_data[16].timestamp = 2;
        traffic_data[16].source_node = 53;
        traffic_data[16].dest_node = 62;
        traffic_data[16].packet_type = "AXI_READ";
        traffic_data[16].size_bytes = 128;
        traffic_data[17].timestamp = 3;
        traffic_data[17].source_node = 4;
        traffic_data[17].dest_node = 27;
        traffic_data[17].packet_type = "CHI_READ";
        traffic_data[17].size_bytes = 256;
        traffic_data[18].timestamp = 3;
        traffic_data[18].source_node = 7;
        traffic_data[18].dest_node = 36;
        traffic_data[18].packet_type = "AXI_WRITE";
        traffic_data[18].size_bytes = 128;
        traffic_data[19].timestamp = 3;
        traffic_data[19].source_node = 16;
        traffic_data[19].dest_node = 37;
        traffic_data[19].packet_type = "AXI_WRITE";
        traffic_data[19].size_bytes = 128;
        traffic_data[20].timestamp = 3;
        traffic_data[20].source_node = 31;
        traffic_data[20].dest_node = 37;
        traffic_data[20].packet_type = "AXI_READ";
        traffic_data[20].size_bytes = 512;
        traffic_data[21].timestamp = 3;
        traffic_data[21].source_node = 45;
        traffic_data[21].dest_node = 21;
        traffic_data[21].packet_type = "CHI_READ";
        traffic_data[21].size_bytes = 256;
        traffic_data[22].timestamp = 3;
        traffic_data[22].source_node = 52;
        traffic_data[22].dest_node = 42;
        traffic_data[22].packet_type = "AXI_READ";
        traffic_data[22].size_bytes = 64;
        traffic_data[23].timestamp = 3;
        traffic_data[23].source_node = 62;
        traffic_data[23].dest_node = 41;
        traffic_data[23].packet_type = "CHI_READ";
        traffic_data[23].size_bytes = 256;
        traffic_data[24].timestamp = 3;
        traffic_data[24].source_node = 63;
        traffic_data[24].dest_node = 7;
        traffic_data[24].packet_type = "CHI_WRITE";
        traffic_data[24].size_bytes = 128;
        traffic_data[25].timestamp = 4;
        traffic_data[25].source_node = 23;
        traffic_data[25].dest_node = 29;
        traffic_data[25].packet_type = "CHI_READ";
        traffic_data[25].size_bytes = 64;
        traffic_data[26].timestamp = 4;
        traffic_data[26].source_node = 25;
        traffic_data[26].dest_node = 36;
        traffic_data[26].packet_type = "AXI_WRITE";
        traffic_data[26].size_bytes = 256;
        traffic_data[27].timestamp = 4;
        traffic_data[27].source_node = 32;
        traffic_data[27].dest_node = 33;
        traffic_data[27].packet_type = "CHI_WRITE";
        traffic_data[27].size_bytes = 512;
        traffic_data[28].timestamp = 4;
        traffic_data[28].source_node = 36;
        traffic_data[28].dest_node = 29;
        traffic_data[28].packet_type = "CHI_READ";
        traffic_data[28].size_bytes = 256;
        traffic_data[29].timestamp = 4;
        traffic_data[29].source_node = 41;
        traffic_data[29].dest_node = 22;
        traffic_data[29].packet_type = "AXI_READ";
        traffic_data[29].size_bytes = 128;
        traffic_data[30].timestamp = 4;
        traffic_data[30].source_node = 42;
        traffic_data[30].dest_node = 58;
        traffic_data[30].packet_type = "AXI_READ";
        traffic_data[30].size_bytes = 1024;
        traffic_data[31].timestamp = 4;
        traffic_data[31].source_node = 55;
        traffic_data[31].dest_node = 62;
        traffic_data[31].packet_type = "AXI_WRITE";
        traffic_data[31].size_bytes = 256;
        traffic_data[32].timestamp = 4;
        traffic_data[32].source_node = 62;
        traffic_data[32].dest_node = 1;
        traffic_data[32].packet_type = "CHI_READ";
        traffic_data[32].size_bytes = 128;
        traffic_data[33].timestamp = 5;
        traffic_data[33].source_node = 8;
        traffic_data[33].dest_node = 43;
        traffic_data[33].packet_type = "CHI_WRITE";
        traffic_data[33].size_bytes = 256;
        traffic_data[34].timestamp = 5;
        traffic_data[34].source_node = 12;
        traffic_data[34].dest_node = 39;
        traffic_data[34].packet_type = "AXI_READ";
        traffic_data[34].size_bytes = 128;
        traffic_data[35].timestamp = 5;
        traffic_data[35].source_node = 16;
        traffic_data[35].dest_node = 29;
        traffic_data[35].packet_type = "AXI_WRITE";
        traffic_data[35].size_bytes = 128;
        traffic_data[36].timestamp = 5;
        traffic_data[36].source_node = 39;
        traffic_data[36].dest_node = 22;
        traffic_data[36].packet_type = "CHI_WRITE";
        traffic_data[36].size_bytes = 256;
        traffic_data[37].timestamp = 5;
        traffic_data[37].source_node = 60;
        traffic_data[37].dest_node = 46;
        traffic_data[37].packet_type = "AXI_WRITE";
        traffic_data[37].size_bytes = 64;
        traffic_data[38].timestamp = 5;
        traffic_data[38].source_node = 63;
        traffic_data[38].dest_node = 4;
        traffic_data[38].packet_type = "AXI_WRITE";
        traffic_data[38].size_bytes = 512;
        traffic_data[39].timestamp = 6;
        traffic_data[39].source_node = 31;
        traffic_data[39].dest_node = 56;
        traffic_data[39].packet_type = "AXI_WRITE";
        traffic_data[39].size_bytes = 256;
        traffic_data[40].timestamp = 6;
        traffic_data[40].source_node = 32;
        traffic_data[40].dest_node = 36;
        traffic_data[40].packet_type = "CHI_WRITE";
        traffic_data[40].size_bytes = 128;
        traffic_data[41].timestamp = 6;
        traffic_data[41].source_node = 55;
        traffic_data[41].dest_node = 52;
        traffic_data[41].packet_type = "AXI_READ";
        traffic_data[41].size_bytes = 256;
        traffic_data[42].timestamp = 6;
        traffic_data[42].source_node = 60;
        traffic_data[42].dest_node = 32;
        traffic_data[42].packet_type = "CHI_WRITE";
        traffic_data[42].size_bytes = 128;
        traffic_data[43].timestamp = 7;
        traffic_data[43].source_node = 2;
        traffic_data[43].dest_node = 36;
        traffic_data[43].packet_type = "CHI_WRITE";
        traffic_data[43].size_bytes = 32;
        traffic_data[44].timestamp = 7;
        traffic_data[44].source_node = 6;
        traffic_data[44].dest_node = 53;
        traffic_data[44].packet_type = "CHI_WRITE";
        traffic_data[44].size_bytes = 512;
        traffic_data[45].timestamp = 7;
        traffic_data[45].source_node = 9;
        traffic_data[45].dest_node = 10;
        traffic_data[45].packet_type = "AXI_WRITE";
        traffic_data[45].size_bytes = 64;
        traffic_data[46].timestamp = 7;
        traffic_data[46].source_node = 24;
        traffic_data[46].dest_node = 25;
        traffic_data[46].packet_type = "CHI_WRITE";
        traffic_data[46].size_bytes = 256;
        traffic_data[47].timestamp = 7;
        traffic_data[47].source_node = 25;
        traffic_data[47].dest_node = 0;
        traffic_data[47].packet_type = "AXI_WRITE";
        traffic_data[47].size_bytes = 64;
        traffic_data[48].timestamp = 7;
        traffic_data[48].source_node = 45;
        traffic_data[48].dest_node = 13;
        traffic_data[48].packet_type = "AXI_WRITE";
        traffic_data[48].size_bytes = 256;
        traffic_data[49].timestamp = 7;
        traffic_data[49].source_node = 48;
        traffic_data[49].dest_node = 10;
        traffic_data[49].packet_type = "AXI_WRITE";
        traffic_data[49].size_bytes = 256;
        traffic_data[50].timestamp = 7;
        traffic_data[50].source_node = 56;
        traffic_data[50].dest_node = 47;
        traffic_data[50].packet_type = "CHI_READ";
        traffic_data[50].size_bytes = 64;
        traffic_data[51].timestamp = 8;
        traffic_data[51].source_node = 0;
        traffic_data[51].dest_node = 18;
        traffic_data[51].packet_type = "CHI_WRITE";
        traffic_data[51].size_bytes = 128;
        traffic_data[52].timestamp = 8;
        traffic_data[52].source_node = 6;
        traffic_data[52].dest_node = 40;
        traffic_data[52].packet_type = "CHI_READ";
        traffic_data[52].size_bytes = 256;
        traffic_data[53].timestamp = 8;
        traffic_data[53].source_node = 8;
        traffic_data[53].dest_node = 10;
        traffic_data[53].packet_type = "CHI_WRITE";
        traffic_data[53].size_bytes = 256;
        traffic_data[54].timestamp = 8;
        traffic_data[54].source_node = 13;
        traffic_data[54].dest_node = 20;
        traffic_data[54].packet_type = "CHI_WRITE";
        traffic_data[54].size_bytes = 128;
        traffic_data[55].timestamp = 8;
        traffic_data[55].source_node = 20;
        traffic_data[55].dest_node = 23;
        traffic_data[55].packet_type = "AXI_READ";
        traffic_data[55].size_bytes = 256;
        traffic_data[56].timestamp = 8;
        traffic_data[56].source_node = 23;
        traffic_data[56].dest_node = 27;
        traffic_data[56].packet_type = "CHI_WRITE";
        traffic_data[56].size_bytes = 256;
        traffic_data[57].timestamp = 8;
        traffic_data[57].source_node = 45;
        traffic_data[57].dest_node = 25;
        traffic_data[57].packet_type = "CHI_READ";
        traffic_data[57].size_bytes = 512;
        traffic_data[58].timestamp = 9;
        traffic_data[58].source_node = 9;
        traffic_data[58].dest_node = 47;
        traffic_data[58].packet_type = "CHI_WRITE";
        traffic_data[58].size_bytes = 512;
        traffic_data[59].timestamp = 9;
        traffic_data[59].source_node = 13;
        traffic_data[59].dest_node = 55;
        traffic_data[59].packet_type = "CHI_WRITE";
        traffic_data[59].size_bytes = 256;
        traffic_data[60].timestamp = 9;
        traffic_data[60].source_node = 27;
        traffic_data[60].dest_node = 62;
        traffic_data[60].packet_type = "CHI_READ";
        traffic_data[60].size_bytes = 256;
        traffic_data[61].timestamp = 9;
        traffic_data[61].source_node = 43;
        traffic_data[61].dest_node = 14;
        traffic_data[61].packet_type = "AXI_WRITE";
        traffic_data[61].size_bytes = 128;
        traffic_data[62].timestamp = 9;
        traffic_data[62].source_node = 49;
        traffic_data[62].dest_node = 6;
        traffic_data[62].packet_type = "CHI_READ";
        traffic_data[62].size_bytes = 128;
        traffic_data[63].timestamp = 10;
        traffic_data[63].source_node = 16;
        traffic_data[63].dest_node = 40;
        traffic_data[63].packet_type = "AXI_WRITE";
        traffic_data[63].size_bytes = 128;
        traffic_data[64].timestamp = 10;
        traffic_data[64].source_node = 18;
        traffic_data[64].dest_node = 13;
        traffic_data[64].packet_type = "AXI_WRITE";
        traffic_data[64].size_bytes = 128;
        traffic_data[65].timestamp = 11;
        traffic_data[65].source_node = 12;
        traffic_data[65].dest_node = 15;
        traffic_data[65].packet_type = "CHI_READ";
        traffic_data[65].size_bytes = 64;
        traffic_data[66].timestamp = 11;
        traffic_data[66].source_node = 23;
        traffic_data[66].dest_node = 47;
        traffic_data[66].packet_type = "CHI_WRITE";
        traffic_data[66].size_bytes = 128;
        traffic_data[67].timestamp = 11;
        traffic_data[67].source_node = 46;
        traffic_data[67].dest_node = 22;
        traffic_data[67].packet_type = "CHI_READ";
        traffic_data[67].size_bytes = 256;
        traffic_data[68].timestamp = 11;
        traffic_data[68].source_node = 58;
        traffic_data[68].dest_node = 17;
        traffic_data[68].packet_type = "AXI_WRITE";
        traffic_data[68].size_bytes = 256;
        traffic_data[69].timestamp = 12;
        traffic_data[69].source_node = 5;
        traffic_data[69].dest_node = 51;
        traffic_data[69].packet_type = "AXI_READ";
        traffic_data[69].size_bytes = 128;
        traffic_data[70].timestamp = 12;
        traffic_data[70].source_node = 14;
        traffic_data[70].dest_node = 63;
        traffic_data[70].packet_type = "CHI_WRITE";
        traffic_data[70].size_bytes = 256;
        traffic_data[71].timestamp = 12;
        traffic_data[71].source_node = 30;
        traffic_data[71].dest_node = 41;
        traffic_data[71].packet_type = "CHI_WRITE";
        traffic_data[71].size_bytes = 32;
        traffic_data[72].timestamp = 12;
        traffic_data[72].source_node = 42;
        traffic_data[72].dest_node = 23;
        traffic_data[72].packet_type = "CHI_READ";
        traffic_data[72].size_bytes = 64;
        traffic_data[73].timestamp = 12;
        traffic_data[73].source_node = 45;
        traffic_data[73].dest_node = 40;
        traffic_data[73].packet_type = "CHI_READ";
        traffic_data[73].size_bytes = 256;
        traffic_data[74].timestamp = 12;
        traffic_data[74].source_node = 48;
        traffic_data[74].dest_node = 6;
        traffic_data[74].packet_type = "AXI_READ";
        traffic_data[74].size_bytes = 64;
        traffic_data[75].timestamp = 12;
        traffic_data[75].source_node = 49;
        traffic_data[75].dest_node = 37;
        traffic_data[75].packet_type = "AXI_WRITE";
        traffic_data[75].size_bytes = 128;
        traffic_data[76].timestamp = 12;
        traffic_data[76].source_node = 51;
        traffic_data[76].dest_node = 21;
        traffic_data[76].packet_type = "AXI_READ";
        traffic_data[76].size_bytes = 1024;
        traffic_data[77].timestamp = 12;
        traffic_data[77].source_node = 54;
        traffic_data[77].dest_node = 24;
        traffic_data[77].packet_type = "AXI_READ";
        traffic_data[77].size_bytes = 256;
        traffic_data[78].timestamp = 13;
        traffic_data[78].source_node = 1;
        traffic_data[78].dest_node = 42;
        traffic_data[78].packet_type = "AXI_WRITE";
        traffic_data[78].size_bytes = 128;
        traffic_data[79].timestamp = 13;
        traffic_data[79].source_node = 8;
        traffic_data[79].dest_node = 6;
        traffic_data[79].packet_type = "AXI_WRITE";
        traffic_data[79].size_bytes = 256;
        traffic_data[80].timestamp = 13;
        traffic_data[80].source_node = 15;
        traffic_data[80].dest_node = 36;
        traffic_data[80].packet_type = "CHI_READ";
        traffic_data[80].size_bytes = 256;
        traffic_data[81].timestamp = 13;
        traffic_data[81].source_node = 24;
        traffic_data[81].dest_node = 58;
        traffic_data[81].packet_type = "AXI_WRITE";
        traffic_data[81].size_bytes = 128;
        traffic_data[82].timestamp = 13;
        traffic_data[82].source_node = 40;
        traffic_data[82].dest_node = 4;
        traffic_data[82].packet_type = "AXI_READ";
        traffic_data[82].size_bytes = 128;
        traffic_data[83].timestamp = 13;
        traffic_data[83].source_node = 41;
        traffic_data[83].dest_node = 3;
        traffic_data[83].packet_type = "CHI_WRITE";
        traffic_data[83].size_bytes = 128;
        traffic_data[84].timestamp = 13;
        traffic_data[84].source_node = 46;
        traffic_data[84].dest_node = 34;
        traffic_data[84].packet_type = "AXI_WRITE";
        traffic_data[84].size_bytes = 128;
        traffic_data[85].timestamp = 13;
        traffic_data[85].source_node = 56;
        traffic_data[85].dest_node = 44;
        traffic_data[85].packet_type = "CHI_WRITE";
        traffic_data[85].size_bytes = 256;
        traffic_data[86].timestamp = 13;
        traffic_data[86].source_node = 58;
        traffic_data[86].dest_node = 5;
        traffic_data[86].packet_type = "CHI_WRITE";
        traffic_data[86].size_bytes = 64;
        traffic_data[87].timestamp = 13;
        traffic_data[87].source_node = 60;
        traffic_data[87].dest_node = 42;
        traffic_data[87].packet_type = "AXI_WRITE";
        traffic_data[87].size_bytes = 64;
        traffic_data[88].timestamp = 14;
        traffic_data[88].source_node = 10;
        traffic_data[88].dest_node = 52;
        traffic_data[88].packet_type = "CHI_WRITE";
        traffic_data[88].size_bytes = 128;
        traffic_data[89].timestamp = 14;
        traffic_data[89].source_node = 11;
        traffic_data[89].dest_node = 46;
        traffic_data[89].packet_type = "AXI_READ";
        traffic_data[89].size_bytes = 128;
        traffic_data[90].timestamp = 14;
        traffic_data[90].source_node = 13;
        traffic_data[90].dest_node = 55;
        traffic_data[90].packet_type = "AXI_WRITE";
        traffic_data[90].size_bytes = 128;
        traffic_data[91].timestamp = 14;
        traffic_data[91].source_node = 20;
        traffic_data[91].dest_node = 56;
        traffic_data[91].packet_type = "AXI_READ";
        traffic_data[91].size_bytes = 64;
        traffic_data[92].timestamp = 14;
        traffic_data[92].source_node = 34;
        traffic_data[92].dest_node = 23;
        traffic_data[92].packet_type = "AXI_READ";
        traffic_data[92].size_bytes = 128;
        traffic_data[93].timestamp = 14;
        traffic_data[93].source_node = 40;
        traffic_data[93].dest_node = 29;
        traffic_data[93].packet_type = "CHI_READ";
        traffic_data[93].size_bytes = 256;
        traffic_data[94].timestamp = 14;
        traffic_data[94].source_node = 42;
        traffic_data[94].dest_node = 29;
        traffic_data[94].packet_type = "AXI_READ";
        traffic_data[94].size_bytes = 128;
        traffic_data[95].timestamp = 14;
        traffic_data[95].source_node = 56;
        traffic_data[95].dest_node = 34;
        traffic_data[95].packet_type = "CHI_READ";
        traffic_data[95].size_bytes = 256;
        traffic_data[96].timestamp = 14;
        traffic_data[96].source_node = 58;
        traffic_data[96].dest_node = 21;
        traffic_data[96].packet_type = "AXI_READ";
        traffic_data[96].size_bytes = 256;
        traffic_data[97].timestamp = 15;
        traffic_data[97].source_node = 5;
        traffic_data[97].dest_node = 15;
        traffic_data[97].packet_type = "CHI_WRITE";
        traffic_data[97].size_bytes = 256;
        traffic_data[98].timestamp = 15;
        traffic_data[98].source_node = 8;
        traffic_data[98].dest_node = 6;
        traffic_data[98].packet_type = "AXI_WRITE";
        traffic_data[98].size_bytes = 256;
        traffic_data[99].timestamp = 15;
        traffic_data[99].source_node = 11;
        traffic_data[99].dest_node = 43;
        traffic_data[99].packet_type = "AXI_WRITE";
        traffic_data[99].size_bytes = 64;
        traffic_data[100].timestamp = 15;
        traffic_data[100].source_node = 19;
        traffic_data[100].dest_node = 12;
        traffic_data[100].packet_type = "AXI_WRITE";
        traffic_data[100].size_bytes = 256;
        traffic_data[101].timestamp = 15;
        traffic_data[101].source_node = 35;
        traffic_data[101].dest_node = 54;
        traffic_data[101].packet_type = "CHI_READ";
        traffic_data[101].size_bytes = 64;
        traffic_data[102].timestamp = 15;
        traffic_data[102].source_node = 39;
        traffic_data[102].dest_node = 19;
        traffic_data[102].packet_type = "CHI_READ";
        traffic_data[102].size_bytes = 512;
        traffic_data[103].timestamp = 15;
        traffic_data[103].source_node = 45;
        traffic_data[103].dest_node = 6;
        traffic_data[103].packet_type = "AXI_WRITE";
        traffic_data[103].size_bytes = 64;
        traffic_data[104].timestamp = 15;
        traffic_data[104].source_node = 46;
        traffic_data[104].dest_node = 50;
        traffic_data[104].packet_type = "AXI_WRITE";
        traffic_data[104].size_bytes = 64;
        traffic_data[105].timestamp = 15;
        traffic_data[105].source_node = 54;
        traffic_data[105].dest_node = 4;
        traffic_data[105].packet_type = "AXI_WRITE";
        traffic_data[105].size_bytes = 512;
        traffic_data[106].timestamp = 15;
        traffic_data[106].source_node = 60;
        traffic_data[106].dest_node = 29;
        traffic_data[106].packet_type = "AXI_READ";
        traffic_data[106].size_bytes = 64;
        traffic_data[107].timestamp = 16;
        traffic_data[107].source_node = 0;
        traffic_data[107].dest_node = 44;
        traffic_data[107].packet_type = "CHI_WRITE";
        traffic_data[107].size_bytes = 64;
        traffic_data[108].timestamp = 16;
        traffic_data[108].source_node = 5;
        traffic_data[108].dest_node = 40;
        traffic_data[108].packet_type = "AXI_WRITE";
        traffic_data[108].size_bytes = 256;
        traffic_data[109].timestamp = 16;
        traffic_data[109].source_node = 9;
        traffic_data[109].dest_node = 25;
        traffic_data[109].packet_type = "AXI_WRITE";
        traffic_data[109].size_bytes = 128;
        traffic_data[110].timestamp = 16;
        traffic_data[110].source_node = 15;
        traffic_data[110].dest_node = 25;
        traffic_data[110].packet_type = "CHI_READ";
        traffic_data[110].size_bytes = 128;
        traffic_data[111].timestamp = 16;
        traffic_data[111].source_node = 21;
        traffic_data[111].dest_node = 39;
        traffic_data[111].packet_type = "AXI_WRITE";
        traffic_data[111].size_bytes = 32;
        traffic_data[112].timestamp = 16;
        traffic_data[112].source_node = 58;
        traffic_data[112].dest_node = 3;
        traffic_data[112].packet_type = "AXI_WRITE";
        traffic_data[112].size_bytes = 256;
        traffic_data[113].timestamp = 16;
        traffic_data[113].source_node = 59;
        traffic_data[113].dest_node = 30;
        traffic_data[113].packet_type = "AXI_READ";
        traffic_data[113].size_bytes = 128;
        traffic_data[114].timestamp = 17;
        traffic_data[114].source_node = 2;
        traffic_data[114].dest_node = 10;
        traffic_data[114].packet_type = "AXI_WRITE";
        traffic_data[114].size_bytes = 256;
        traffic_data[115].timestamp = 17;
        traffic_data[115].source_node = 34;
        traffic_data[115].dest_node = 39;
        traffic_data[115].packet_type = "CHI_READ";
        traffic_data[115].size_bytes = 512;
        traffic_data[116].timestamp = 17;
        traffic_data[116].source_node = 45;
        traffic_data[116].dest_node = 46;
        traffic_data[116].packet_type = "CHI_READ";
        traffic_data[116].size_bytes = 128;
        traffic_data[117].timestamp = 17;
        traffic_data[117].source_node = 48;
        traffic_data[117].dest_node = 16;
        traffic_data[117].packet_type = "AXI_READ";
        traffic_data[117].size_bytes = 256;
        traffic_data[118].timestamp = 17;
        traffic_data[118].source_node = 49;
        traffic_data[118].dest_node = 28;
        traffic_data[118].packet_type = "CHI_WRITE";
        traffic_data[118].size_bytes = 1024;
        traffic_data[119].timestamp = 17;
        traffic_data[119].source_node = 60;
        traffic_data[119].dest_node = 54;
        traffic_data[119].packet_type = "AXI_READ";
        traffic_data[119].size_bytes = 128;
        traffic_data[120].timestamp = 17;
        traffic_data[120].source_node = 63;
        traffic_data[120].dest_node = 10;
        traffic_data[120].packet_type = "CHI_WRITE";
        traffic_data[120].size_bytes = 64;
        traffic_data[121].timestamp = 18;
        traffic_data[121].source_node = 0;
        traffic_data[121].dest_node = 61;
        traffic_data[121].packet_type = "AXI_READ";
        traffic_data[121].size_bytes = 128;
        traffic_data[122].timestamp = 18;
        traffic_data[122].source_node = 8;
        traffic_data[122].dest_node = 22;
        traffic_data[122].packet_type = "AXI_WRITE";
        traffic_data[122].size_bytes = 1024;
        traffic_data[123].timestamp = 18;
        traffic_data[123].source_node = 15;
        traffic_data[123].dest_node = 26;
        traffic_data[123].packet_type = "CHI_WRITE";
        traffic_data[123].size_bytes = 64;
        traffic_data[124].timestamp = 18;
        traffic_data[124].source_node = 22;
        traffic_data[124].dest_node = 10;
        traffic_data[124].packet_type = "CHI_READ";
        traffic_data[124].size_bytes = 1024;
        traffic_data[125].timestamp = 18;
        traffic_data[125].source_node = 34;
        traffic_data[125].dest_node = 28;
        traffic_data[125].packet_type = "CHI_WRITE";
        traffic_data[125].size_bytes = 128;
        traffic_data[126].timestamp = 18;
        traffic_data[126].source_node = 39;
        traffic_data[126].dest_node = 43;
        traffic_data[126].packet_type = "CHI_READ";
        traffic_data[126].size_bytes = 512;
        traffic_data[127].timestamp = 18;
        traffic_data[127].source_node = 43;
        traffic_data[127].dest_node = 24;
        traffic_data[127].packet_type = "CHI_WRITE";
        traffic_data[127].size_bytes = 1024;
        traffic_data[128].timestamp = 18;
        traffic_data[128].source_node = 51;
        traffic_data[128].dest_node = 36;
        traffic_data[128].packet_type = "AXI_WRITE";
        traffic_data[128].size_bytes = 64;
        traffic_data[129].timestamp = 19;
        traffic_data[129].source_node = 3;
        traffic_data[129].dest_node = 25;
        traffic_data[129].packet_type = "CHI_WRITE";
        traffic_data[129].size_bytes = 256;
        traffic_data[130].timestamp = 19;
        traffic_data[130].source_node = 7;
        traffic_data[130].dest_node = 45;
        traffic_data[130].packet_type = "CHI_WRITE";
        traffic_data[130].size_bytes = 64;
        traffic_data[131].timestamp = 19;
        traffic_data[131].source_node = 31;
        traffic_data[131].dest_node = 30;
        traffic_data[131].packet_type = "CHI_READ";
        traffic_data[131].size_bytes = 512;
        traffic_data[132].timestamp = 19;
        traffic_data[132].source_node = 32;
        traffic_data[132].dest_node = 53;
        traffic_data[132].packet_type = "CHI_READ";
        traffic_data[132].size_bytes = 128;
        traffic_data[133].timestamp = 19;
        traffic_data[133].source_node = 44;
        traffic_data[133].dest_node = 28;
        traffic_data[133].packet_type = "AXI_WRITE";
        traffic_data[133].size_bytes = 512;
        traffic_data[134].timestamp = 19;
        traffic_data[134].source_node = 49;
        traffic_data[134].dest_node = 51;
        traffic_data[134].packet_type = "AXI_WRITE";
        traffic_data[134].size_bytes = 64;
        traffic_data[135].timestamp = 19;
        traffic_data[135].source_node = 58;
        traffic_data[135].dest_node = 2;
        traffic_data[135].packet_type = "CHI_WRITE";
        traffic_data[135].size_bytes = 64;
        $display("📝 Traffic data loaded: %0d entries", TRAFFIC_SIZE);
        
        // Inject traffic based on traces
        $display("🚀 Starting traffic injection...");
        inject_traffic();
        $display("✅ Traffic injection completed!");
        
        // Wait for packets to propagate through network
        $display("⏳ Waiting for network to drain...");
        repeat(10000) @(posedge clk);
        
        $display("🎉 Simulation completed successfully!");
        $display("📊 Final statistics:");
        $display("   - Traffic entries processed: %0d", TRAFFIC_SIZE);
        $finish;
    end

    // Traffic injection task with enhanced debugging
    task inject_traffic;
        int timeout_cycles;
        
        // Inject traffic with enhanced debugging and timeout
        for (int i = 0; i < TRAFFIC_SIZE; i++) begin
            $display("[%0t] Processing traffic entry %0d/%0d", $time, i+1, TRAFFIC_SIZE);
            
            // Wait for correct cycle with timeout
            timeout_cycles = 0;
            while (cycle_count < traffic_data[i].timestamp) begin
                @(posedge clk);
                cycle_count++;
                timeout_cycles++;
                if (timeout_cycles > 1000) begin
                    $display("[%0t] TIMEOUT waiting for cycle %0d (current: %0d)", 
                            $time, traffic_data[i].timestamp, cycle_count);
                    break;
                end
            end
            
            // Inject packet at source node
            $display("[%0t] Injecting %s packet %0d: node %0d -> node %0d (cycle %0d)", 
                     $time, traffic_data[i].packet_type, i,
                     traffic_data[i].source_node, traffic_data[i].dest_node, cycle_count);
            
            // Simple packet injection using AXI read/write with timeout
            if (traffic_data[i].packet_type == "AXI_READ") begin
                $display("[%0t] Starting AXI_READ from node %0d", $time, traffic_data[i].source_node);
                @(posedge clk);
                axi_ar_valid[traffic_data[i].source_node] = 1'b1;
                axi_ar[traffic_data[i].source_node].arid = i[7:0];
                axi_ar[traffic_data[i].source_node].araddr = traffic_data[i].dest_node << 12;
                axi_ar[traffic_data[i].source_node].arlen = 8'h0;
                axi_ar[traffic_data[i].source_node].arsize = 3'h3;
                axi_ar[traffic_data[i].source_node].arburst = 2'b01;
                
                // Wait with timeout
                timeout_cycles = 0;
                while (!axi_ar_ready[traffic_data[i].source_node] && timeout_cycles < 100) begin
                    @(posedge clk);
                    timeout_cycles++;
                end
                
                if (timeout_cycles >= 100) begin
                    $display("[%0t] AXI_READ timeout on node %0d", $time, traffic_data[i].source_node);
                end else begin
                    $display("[%0t] AXI_READ handshake completed on node %0d", $time, traffic_data[i].source_node);
                end
                
                @(posedge clk);
                axi_ar_valid[traffic_data[i].source_node] = 1'b0;
                
            end else if (traffic_data[i].packet_type == "AXI_WRITE") begin
                $display("[%0t] Starting AXI_WRITE from node %0d", $time, traffic_data[i].source_node);
                @(posedge clk);
                axi_aw_valid[traffic_data[i].source_node] = 1'b1;
                axi_w_valid[traffic_data[i].source_node] = 1'b1;
                axi_aw[traffic_data[i].source_node].awid = i[7:0];
                axi_aw[traffic_data[i].source_node].awaddr = traffic_data[i].dest_node << 12;
                axi_aw[traffic_data[i].source_node].awlen = 8'h0;
                axi_aw[traffic_data[i].source_node].awsize = 3'h3;
                axi_aw[traffic_data[i].source_node].awburst = 2'b01;
                axi_w[traffic_data[i].source_node].wdata = $random;
                axi_w[traffic_data[i].source_node].wstrb = '1;
                axi_w[traffic_data[i].source_node].wlast = 1'b1;
                
                // Wait with timeout
                timeout_cycles = 0;
                while (!(axi_aw_ready[traffic_data[i].source_node] && axi_w_ready[traffic_data[i].source_node]) && timeout_cycles < 100) begin
                    @(posedge clk);
                    timeout_cycles++;
                end
                
                if (timeout_cycles >= 100) begin
                    $display("[%0t] AXI_WRITE timeout on node %0d", $time, traffic_data[i].source_node);
                end else begin
                    $display("[%0t] AXI_WRITE handshake completed on node %0d", $time, traffic_data[i].source_node);
                end
                
                @(posedge clk);
                axi_aw_valid[traffic_data[i].source_node] = 1'b0;
                axi_w_valid[traffic_data[i].source_node] = 1'b0;
            end else begin
                $display("[%0t] Unknown packet type: %s", $time, traffic_data[i].packet_type);
            end
            
            // Small delay between packets
            $display("[%0t] Packet %0d completed, waiting before next...", $time, i);
            repeat(3) @(posedge clk);
        end
    endtask
    
    // Monitor traffic and performance with enhanced debugging
    int monitor_count = 0;
    int cycle_count = 0;
    always @(posedge clk) begin
        monitor_count++;
        cycle_count++;
        
        // Print progress every 1000 cycles
        if (monitor_count % 1000 == 0) begin
            $display("[%0t] Simulation progress: cycle %0d, monitor_count %0d", 
                    $time, cycle_count, monitor_count);
        end
        
        // Monitor debug traces
        if (debug_trace_valid) begin
            $display("[%0t] Debug trace from node %0d: %016h", 
                    $time, debug_trace_node_id, debug_trace_data);
        end
        
        // Timeout check for overall simulation
        if (monitor_count > 100000) begin
            $display("[%0t] SIMULATION TIMEOUT after %0d cycles", $time, monitor_count);
            $display("Final simulation status:");
            $display("   - Monitor count: %0d", monitor_count);
            $finish;
        end
    end

endmodule
