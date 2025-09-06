/**
 * Nebula Single Router Implementation
 * 
 * Five-stage pipeline router with the following stages:
 * 1. Buffer Write (BW) - Input port management and VC FIFO allocation  
 * 2. Route Computation (RC) - XY routing algorithm and destination extraction
 * 3. Virtual Channel Allocation (VA) - VC state machines and downstream VC allocation
 * 4. Switch Allocation (SA) - Crossbar arbitration and round-robin scheduling
 * 5. Switch Traversal (ST) - Crossbar switching and credit management
 *
 * Features:
 * - XY dimension-ordered routing (deadlock-free)
 * - Multiple VCs per input port (4 VCs, 16 flit depth each)
 * - Credit-based flow control with backpressure
 * - Round-robin arbitration for fairness
 * - Parameterizable for different mesh sizes
 *
 * Authors: Team Bob (Pranav Chandra, Pramit Pal, Meghadri Ghosh)
 * Date: August 2025
 */

import nebula_pkg::*;

module nebula_router #(
  parameter int ROUTER_X = 0,  // This router's X coordinate
  parameter int ROUTER_Y = 0,  // This router's Y coordinate 
  parameter int MESH_SIZE_X = MESH_SIZE_X_DEFAULT,
  parameter int MESH_SIZE_Y = MESH_SIZE_Y_DEFAULT
)(
  input  logic                                    clk,
  input  logic                                    rst_n,
  
  // Input ports [North, South, East, West, Local]
  input  logic [NUM_PORTS-1:0]                   flit_in_valid,
  input  noc_flit_t [NUM_PORTS-1:0]              flit_in,
  output logic [NUM_PORTS-1:0]                   flit_in_ready,
  
  // Output ports [North, South, East, West, Local] 
  output logic [NUM_PORTS-1:0]                   flit_out_valid,
  output noc_flit_t [NUM_PORTS-1:0]              flit_out,
  input  logic [NUM_PORTS-1:0]                   flit_out_ready,
  
  // Debug and status
  output logic [NUM_PORTS-1:0][NUM_VCS-1:0]      vc_status,
  output logic [PERF_COUNTER_WIDTH-1:0]          packets_routed,
  output error_code_e                            error_status
);

  // ============================================================================
  // INTERNAL SIGNALS AND STRUCTURES
  // ============================================================================

  // VC state definitions
  typedef enum logic [2:0] {
    VC_IDLE       = 3'b000,
    VC_ROUTING    = 3'b001, 
    VC_WAITING_VC = 3'b010,
    VC_WAITING_SW = 3'b011,
    VC_ACTIVE     = 3'b100
  } vc_state_e;

  // Input buffer structures
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]             vc_write_en;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]             vc_read_en;
  noc_flit_t [NUM_PORTS-1:0][NUM_VCS-1:0]       vc_write_data;
  noc_flit_t [NUM_PORTS-1:0][NUM_VCS-1:0]       vc_read_data;
  
  // Bit-level conversion for FIFO interface
  logic [NUM_PORTS-1:0][NUM_VCS-1:0][FLIT_WIDTH-1:0] vc_write_data_bits;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0][FLIT_WIDTH-1:0] vc_read_data_bits;
  
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]             vc_full;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]             vc_empty;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0][VC_PTR_WIDTH:0] vc_count;

  // VC state machines
  vc_state_e [NUM_PORTS-1:0][NUM_VCS-1:0]       vc_state;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0][2:0]       vc_out_port;  // Which output port this VC is routed to
  logic [NUM_PORTS-1:0][NUM_VCS-1:0][VC_ID_WIDTH-1:0] vc_out_vc; // Which output VC is allocated

  // Pipeline stage registers
  
  // RC stage outputs
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]             rc_valid;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0][2:0]        rc_out_port;
  noc_flit_t [NUM_PORTS-1:0][NUM_VCS-1:0]       rc_flit;
  
  // VA stage outputs  
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]             va_valid;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0][2:0]        va_out_port;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0][VC_ID_WIDTH-1:0] va_out_vc;
  noc_flit_t [NUM_PORTS-1:0][NUM_VCS-1:0]       va_flit;
  
  // SA stage outputs
  logic [NUM_PORTS-1:0]                          sa_valid;
  logic [NUM_PORTS-1:0][2:0]                     sa_in_port;   // Which input port won arbitration
  logic [NUM_PORTS-1:0][VC_ID_WIDTH-1:0]         sa_in_vc;     // Which input VC won arbitration
  noc_flit_t [NUM_PORTS-1:0]                    sa_flit;
  
  // Grant persistence tracking for backpressure handling
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]            granted_but_blocked;
  
  // Credit management
  logic [NUM_PORTS-1:0][NUM_VCS-1:0][CREDIT_WIDTH-1:0] credit_count;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]             credit_inc;
  logic [NUM_PORTS-1:0][NUM_VCS-1:0]             credit_dec;

  // Arbitration signals
  logic [NUM_PORTS-1:0][NUM_PORTS*NUM_VCS-1:0]   arb_req;      // Requests for each output port
  logic [NUM_PORTS-1:0][NUM_PORTS*NUM_VCS-1:0]   arb_grant;    // Grants for each output port  
  
  // Struct to bits conversion for FIFO interface
  always_comb begin
    for (int p = 0; p < NUM_PORTS; p++) begin
      for (int v = 0; v < NUM_VCS; v++) begin
        // Convert struct to bits using casting - this preserves bit layout
        vc_write_data_bits[p][v] = vc_write_data[p][v];
        
        // Convert bits back to struct using casting - this preserves bit layout  
        vc_read_data[p][v] = vc_read_data_bits[p][v];
      end
    end
  end
  
  genvar g_port, g_vc, g_out_port;

  // ============================================================================
  // BUFFER WRITE STAGE (BW) - INPUT PORT MANAGEMENT 
  // ============================================================================
  
  generate
    for (g_port = 0; g_port < NUM_PORTS; g_port++) begin : gen_input_ports
      
      // Input port VC selection logic
      always_comb begin
        logic [VC_ID_WIDTH-1:0] selected_vc;
        logic any_vc_available;
        
        // Ready signal indicates availability to accept flits
        // More robust ready signal generation
        any_vc_available = 1'b0;
        for (int v = 0; v < NUM_VCS; v++) begin
          // Check if VC has space (not full) and is initialized properly
          if (!vc_full[g_port][v] && rst_n) begin
            any_vc_available = 1'b1;
            break; // Early exit for efficiency
          end
        end
        
        // Only assert ready when reset is complete and VCs are available
        flit_in_ready[g_port] = rst_n && any_vc_available;
        
        selected_vc = '0; // Default value to prevent latch
        for (int v = 0; v < NUM_VCS; v++) begin
          vc_write_en[g_port][v] = 1'b0;
          vc_write_data[g_port][v] = flit_in[g_port];
        end
        
        if (flit_in_valid[g_port]) begin
          // Use VC from flit header for VC selection
          selected_vc = flit_in[g_port].vc_id;
          
          if (selected_vc < NUM_VCS && !vc_full[g_port][selected_vc]) begin
            vc_write_en[g_port][selected_vc] = 1'b1;
            $display("[DEBUG] @%0t: Writing to VC[%0d][%0d]: flit_type=%0d, dest=(%0d,%0d), src=(%0d,%0d)", 
                     $time, g_port, selected_vc, flit_in[g_port].flit_type, 
                     flit_in[g_port].dest_x, flit_in[g_port].dest_y, 
                     flit_in[g_port].src_x, flit_in[g_port].src_y);
          end
        end
      end
      
      // Instantiate VC buffers
      for (g_vc = 0; g_vc < NUM_VCS; g_vc++) begin : gen_vc_buffers
        nebula_fifo #(
          .DATA_WIDTH(FLIT_WIDTH),
          .DEPTH(VC_DEPTH)
        ) vc_buffer (
          .clk(clk),
          .rst_n(rst_n),
          .wr_en(vc_write_en[g_port][g_vc]),
          .wr_data(vc_write_data_bits[g_port][g_vc]),
          .full(vc_full[g_port][g_vc]),
          .almost_full(),  // Not used
          .rd_en(vc_read_en[g_port][g_vc]),
          .rd_data(vc_read_data_bits[g_port][g_vc]),
          .empty(vc_empty[g_port][g_vc]),
          .almost_empty(), // Not used
          .count(vc_count[g_port][g_vc])
        );
      end
    end
  endgenerate

  // ============================================================================
  // ROUTE COMPUTATION STAGE (RC) - XY ROUTING
  // ============================================================================
  
  generate
    for (g_port = 0; g_port < NUM_PORTS; g_port++) begin : gen_rc_stage
      for (g_vc = 0; g_vc < NUM_VCS; g_vc++) begin : gen_rc_vc
        
        always_ff @(posedge clk or negedge rst_n) begin
          if (!rst_n) begin
            rc_valid[g_port][g_vc] <= 1'b0;
            rc_out_port[g_port][g_vc] <= 3'b0;
            rc_flit[g_port][g_vc] <= '0;
          end else begin
            noc_flit_t current_flit;
            
            rc_valid[g_port][g_vc] <= 1'b0;
            
            // Route computation for head flits or when VC needs routing
            if (!vc_empty[g_port][g_vc] && vc_state[g_port][g_vc] == VC_ROUTING) begin
              current_flit = vc_read_data[g_port][g_vc];  // Now uses show-ahead FIFO
              
              if (current_flit.flit_type == FLIT_TYPE_HEAD || 
                  current_flit.flit_type == FLIT_TYPE_SINGLE) begin
                rc_valid[g_port][g_vc] <= 1'b1;
                rc_flit[g_port][g_vc] <= current_flit;
                
                $display("[DEBUG] @%0t: RC[%0d][%0d] Processing flit, dest=(%0d,%0d), router=(%0d,%0d)", 
                         $time, g_port, g_vc, current_flit.dest_x, current_flit.dest_y, ROUTER_X, ROUTER_Y);
                
                // XY routing algorithm (dimension-ordered)
                if (current_flit.dest_x != ROUTER_X) begin
                  // Route in X dimension first
                  if (current_flit.dest_x > ROUTER_X) begin
                    rc_out_port[g_port][g_vc] <= PORT_EAST;
                    $display("[DEBUG] @%0t: RC[%0d][%0d] Routing EAST (dest_x=%0d > router_x=%0d)", 
                             $time, g_port, g_vc, current_flit.dest_x, ROUTER_X);
                  end else begin
                    rc_out_port[g_port][g_vc] <= PORT_WEST;
                    $display("[DEBUG] @%0t: RC[%0d][%0d] Routing WEST (dest_x=%0d < router_x=%0d)", 
                             $time, g_port, g_vc, current_flit.dest_x, ROUTER_X);
                  end
                end else if (current_flit.dest_y != ROUTER_Y) begin
                  // Route in Y dimension if X matches
                  if (current_flit.dest_y > ROUTER_Y) begin
                    rc_out_port[g_port][g_vc] <= PORT_NORTH;
                    $display("[DEBUG] @%0t: RC[%0d][%0d] Routing NORTH (dest_y=%0d > router_y=%0d)", 
                             $time, g_port, g_vc, current_flit.dest_y, ROUTER_Y);
                  end else begin
                    rc_out_port[g_port][g_vc] <= PORT_SOUTH;
                    $display("[DEBUG] @%0t: RC[%0d][%0d] Routing SOUTH (dest_y=%0d < router_y=%0d)", 
                             $time, g_port, g_vc, current_flit.dest_y, ROUTER_Y);
                  end
                end else begin
                  // Destination reached - route to local port
                  rc_out_port[g_port][g_vc] <= PORT_LOCAL;
                  $display("[DEBUG] @%0t: RC[%0d][%0d] Routing LOCAL (dest matches router pos)", 
                           $time, g_port, g_vc);
                end
              end
            end
          end
        end
      end
    end
  endgenerate

  // ============================================================================
  // VIRTUAL CHANNEL ALLOCATION STAGE (VA)
  // ============================================================================
  
  generate
    for (g_port = 0; g_port < NUM_PORTS; g_port++) begin : gen_va_stage
      for (g_vc = 0; g_vc < NUM_VCS; g_vc++) begin : gen_va_vc
        
        always_ff @(posedge clk or negedge rst_n) begin
          if (!rst_n) begin
            va_valid[g_port][g_vc] <= 1'b0;
            va_out_port[g_port][g_vc] <= 3'b0;
            va_out_vc[g_port][g_vc] <= 2'b0;
            va_flit[g_port][g_vc] <= '0;
            vc_out_port[g_port][g_vc] <= 3'b0;
            vc_out_vc[g_port][g_vc] <= 2'b0;
          end else begin
            logic [VC_ID_WIDTH-1:0] selected_out_vc;
            logic vc_allocated;
            
            va_valid[g_port][g_vc] <= 1'b0;
            
            if (rc_valid[g_port][g_vc]) begin
              // Try to allocate output VC (round-robin for simplicity)
              vc_allocated = 1'b0;
              
              $display("[DEBUG] @%0t: VA[%0d][%0d] Processing RC output, out_port=%0d", 
                       $time, g_port, g_vc, rc_out_port[g_port][g_vc]);
              
              for (int out_vc = 0; out_vc < NUM_VCS && !vc_allocated; out_vc++) begin
                if (credit_count[rc_out_port[g_port][g_vc]][out_vc] > 0) begin
                  selected_out_vc = out_vc[VC_ID_WIDTH-1:0];
                  vc_allocated = 1'b1;
                  $display("[DEBUG] @%0t: VA[%0d][%0d] Allocated out_vc=%0d, credits=%0d", 
                           $time, g_port, g_vc, out_vc, credit_count[rc_out_port[g_port][g_vc]][out_vc]);
                end
              end
              
              if (vc_allocated) begin
                va_valid[g_port][g_vc] <= 1'b1;
                va_out_port[g_port][g_vc] <= rc_out_port[g_port][g_vc];
                va_out_vc[g_port][g_vc] <= selected_out_vc;
                va_flit[g_port][g_vc] <= rc_flit[g_port][g_vc];
                
                // Store allocation in VC state
                vc_out_port[g_port][g_vc] <= rc_out_port[g_port][g_vc];
                vc_out_vc[g_port][g_vc] <= selected_out_vc;
              end
            end
          end
        end
      end
    end
  endgenerate

  // ============================================================================
  // SWITCH ALLOCATION STAGE (SA) - CROSSBAR ARBITRATION WITH BACKPRESSURE HANDLING
  // ============================================================================
  
  // Grant persistence tracking for backpressure handling
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      granted_but_blocked <= '0;
    end else begin
      for (int g_in_port = 0; g_in_port < NUM_PORTS; g_in_port++) begin
        for (int g_in_vc = 0; g_in_vc < NUM_VCS; g_in_vc++) begin
          // Check if this VC was granted but blocked by backpressure
          logic was_granted_but_blocked = 1'b0;
          logic was_successfully_transmitted = 1'b0;
          
          for (int g_out_port = 0; g_out_port < NUM_PORTS; g_out_port++) begin
            int arb_idx = g_in_port * NUM_VCS + g_in_vc;
            
            // New grant this cycle but blocked by backpressure
            if (arb_grant[g_out_port][arb_idx] && !flit_out_ready[g_out_port]) begin
              was_granted_but_blocked = 1'b1;
            end
            
            // Successfully transmitted (clear the block)
            if (granted_but_blocked[g_in_port][g_in_vc] && 
                va_valid[g_in_port][g_in_vc] && 
                va_out_port[g_in_port][g_in_vc] == g_out_port &&
                flit_out_valid[g_out_port] && flit_out_ready[g_out_port]) begin
              was_successfully_transmitted = 1'b1;
            end
          end
          
          // Update the granted_but_blocked state
          if (was_granted_but_blocked) begin
            granted_but_blocked[g_in_port][g_in_vc] <= 1'b1;
          end else if (was_successfully_transmitted) begin
            granted_but_blocked[g_in_port][g_in_vc] <= 1'b0;
          end
        end
      end
    end
  end
  
  generate
    for (g_out_port = 0; g_out_port < NUM_PORTS; g_out_port++) begin : gen_sa_stage
      
      // Build arbitration requests for this output port
      always_comb begin
        arb_req[g_out_port] = '0;
        
        for (int in_port = 0; in_port < NUM_PORTS; in_port++) begin
          for (int in_vc = 0; in_vc < NUM_VCS; in_vc++) begin
            int arb_idx = in_port * NUM_VCS + in_vc;
            
            // Only request if VC is valid, targets this output, has credits, and is not already blocked
            if (va_valid[in_port][in_vc] && 
                va_out_port[in_port][in_vc] == g_out_port &&
                credit_count[g_out_port][va_out_vc[in_port][in_vc]] > 0 &&
                !granted_but_blocked[in_port][in_vc]) begin
              arb_req[g_out_port][arb_idx] = 1'b1;
            end
          end
        end
      end
      
      // Round-robin arbiter for this output port
      nebula_rr_arbiter #(
        .NUM_REQS(NUM_PORTS * NUM_VCS)
      ) output_arbiter (
        .clk(clk),
        .rst_n(rst_n),
        .req(arb_req[g_out_port]),
        .grant(arb_grant[g_out_port]),
        .grant_valid(),  // Not used
        .grant_id()      // Not used
      );
      
      // SA stage output generation - combine new grants with persistent blocked grants
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          sa_valid[g_out_port] <= 1'b0;
          sa_in_port[g_out_port] <= 3'b0;
          sa_in_vc[g_out_port] <= 2'b0;
          sa_flit[g_out_port] <= '0;
        end else begin
          sa_valid[g_out_port] <= 1'b0;
          
          // Check for persistent blocked grants first (higher priority)
          for (int in_port = 0; in_port < NUM_PORTS; in_port++) begin
            for (int in_vc = 0; in_vc < NUM_VCS; in_vc++) begin
              if (granted_but_blocked[in_port][in_vc] && 
                  va_out_port[in_port][in_vc] == g_out_port) begin
                sa_valid[g_out_port] <= 1'b1;
                sa_in_port[g_out_port] <= in_port[2:0];
                sa_in_vc[g_out_port] <= in_vc[VC_ID_WIDTH-1:0];
                sa_flit[g_out_port] <= va_flit[in_port][in_vc];
                $display("[DEBUG] @%0t: SA output_port=%0d serving persistent blocked grant from input[%0d][%0d]", 
                         $time, g_out_port, in_port, in_vc);
              end
            end
          end
          
          // If no persistent grants, check for new grants
          if (!sa_valid[g_out_port]) begin
            for (int in_port = 0; in_port < NUM_PORTS; in_port++) begin
              for (int in_vc = 0; in_vc < NUM_VCS; in_vc++) begin
                int arb_idx = in_port * NUM_VCS + in_vc;
                
                if (arb_grant[g_out_port][arb_idx]) begin
                  sa_valid[g_out_port] <= 1'b1;
                  sa_in_port[g_out_port] <= in_port[2:0];
                  sa_in_vc[g_out_port] <= in_vc[VC_ID_WIDTH-1:0];
                  sa_flit[g_out_port] <= va_flit[in_port][in_vc];
                  $display("[DEBUG] @%0t: SA output_port=%0d granted to input[%0d][%0d]", 
                           $time, g_out_port, in_port, in_vc);
                end
              end
            end
          end
        end
      end
    end
  endgenerate

  // ============================================================================
  // SWITCH TRAVERSAL STAGE (ST) - OUTPUT TRANSMISSION
  // ============================================================================
  
  generate
    for (g_port = 0; g_port < NUM_PORTS; g_port++) begin : gen_st_stage
      
      always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
          flit_out_valid[g_port] <= 1'b0;
          flit_out[g_port] <= '0;
        end else begin
          // Only assert flit_out_valid when both SA grants access AND downstream is ready
          if (sa_valid[g_port] && flit_out_ready[g_port]) begin
            flit_out_valid[g_port] <= 1'b1;
            flit_out[g_port] <= sa_flit[g_port];
            flit_out[g_port].vc_id <= vc_out_vc[sa_in_port[g_port]][sa_in_vc[g_port]];
            $display("[DEBUG] @%0t: ST output_port=%0d successfully transmitted flit, type=%0d, payload=%0h", 
                     $time, g_port, sa_flit[g_port].flit_type, sa_flit[g_port].payload[7:0]);
          end else begin
            flit_out_valid[g_port] <= 1'b0;
            
            // Debug: Show when we have grant but are blocked by backpressure
            if (sa_valid[g_port] && !flit_out_ready[g_port]) begin
              $display("[DEBUG] @%0t: ST output_port=%0d blocked by backpressure (sa_valid=1, ready=0)", 
                       $time, g_port);
            end
          end
        end
      end
    end
  endgenerate

  // ============================================================================
  // VC STATE MACHINE MANAGEMENT
  // ============================================================================
  
  generate
    for (g_port = 0; g_port < NUM_PORTS; g_port++) begin : gen_vc_fsm
      for (g_vc = 0; g_vc < NUM_VCS; g_vc++) begin : gen_vc_fsm_vc
        
        always_ff @(posedge clk or negedge rst_n) begin
          if (!rst_n) begin
            vc_state[g_port][g_vc] <= VC_IDLE;
            vc_read_en[g_port][g_vc] <= 1'b0;
          end else begin
            noc_flit_t head_flit, current_flit;
            logic can_send;
            
            vc_read_en[g_port][g_vc] <= 1'b0;
            
            case (vc_state[g_port][g_vc])
              
              VC_IDLE: begin
                if (!vc_empty[g_port][g_vc]) begin
                  head_flit = vc_read_data[g_port][g_vc];
                  if (head_flit.flit_type == FLIT_TYPE_HEAD || 
                      head_flit.flit_type == FLIT_TYPE_SINGLE) begin
                    vc_state[g_port][g_vc] <= VC_ROUTING;
                    $display("[DEBUG] @%0t: VC[%0d][%0d] IDLE->ROUTING, flit_type=%0d", 
                             $time, g_port, g_vc, head_flit.flit_type);
                  end
                end
              end
              
              VC_ROUTING: begin
                if (rc_valid[g_port][g_vc]) begin
                  vc_state[g_port][g_vc] <= VC_WAITING_VC;
                  $display("[DEBUG] @%0t: VC[%0d][%0d] ROUTING->WAITING_VC, rc_valid=1", 
                           $time, g_port, g_vc);
                end
              end
              
              VC_WAITING_VC: begin
                if (va_valid[g_port][g_vc]) begin
                  vc_state[g_port][g_vc] <= VC_ACTIVE;
                  $display("[DEBUG] @%0t: VC[%0d][%0d] WAITING_VC->ACTIVE, va_valid=1", 
                           $time, g_port, g_vc);
                end
              end
              
              VC_ACTIVE: begin
                // Check if this VC won switch arbitration and can send flit
                can_send = 1'b0;
                for (int out_p = 0; out_p < NUM_PORTS; out_p++) begin
                  if (sa_valid[out_p] && 
                      sa_in_port[out_p] == g_port &&
                      sa_in_vc[out_p] == g_vc &&
                      flit_out_ready[out_p]) begin
                    can_send = 1'b1;
                  end
                end
                
                if (can_send && !vc_empty[g_port][g_vc]) begin
                  vc_read_en[g_port][g_vc] <= 1'b1;
                  
                  $display("[DEBUG] @%0t: VC[%0d][%0d] ACTIVE: Reading flit from buffer", 
                           $time, g_port, g_vc);
                  
                  // Check if this is the last flit
                  current_flit = vc_read_data[g_port][g_vc];
                  if (current_flit.flit_type == FLIT_TYPE_TAIL || 
                      current_flit.flit_type == FLIT_TYPE_SINGLE) begin
                    vc_state[g_port][g_vc] <= VC_IDLE;
                    $display("[DEBUG] @%0t: VC[%0d][%0d] ACTIVE->IDLE (last flit)", 
                             $time, g_port, g_vc);
                  end
                end
              end
              
              default: begin
                vc_state[g_port][g_vc] <= VC_IDLE;
              end
              
            endcase
          end
        end
      end
    end
  endgenerate

  // ============================================================================
  // CREDIT MANAGEMENT
  // ============================================================================
  
  generate
    for (g_port = 0; g_port < NUM_PORTS; g_port++) begin : gen_credits
      for (g_vc = 0; g_vc < NUM_VCS; g_vc++) begin : gen_credits_vc
        
        // Credit increment when downstream accepts a flit
        always_comb begin
          credit_inc[g_port][g_vc] = 1'b0;
          if (flit_out_valid[g_port] && flit_out_ready[g_port] && 
              flit_out[g_port].vc_id == g_vc) begin
            credit_inc[g_port][g_vc] = 1'b1;
          end
        end
        
        // Credit decrement when we allocate a VC
        always_comb begin
          credit_dec[g_port][g_vc] = 1'b0;
          for (int in_p = 0; in_p < NUM_PORTS; in_p++) begin
            for (int in_v = 0; in_v < NUM_VCS; in_v++) begin
              if (va_valid[in_p][in_v] && 
                  va_out_port[in_p][in_v] == g_port && 
                  va_out_vc[in_p][in_v] == g_vc) begin
                credit_dec[g_port][g_vc] = 1'b1;
              end
            end
          end
        end
        
        nebula_credit_flow_ctrl #(
          .MAX_CREDITS(VC_DEPTH)
        ) credit_ctrl (
          .clk(clk),
          .rst_n(rst_n),
          .send_flit(credit_dec[g_port][g_vc]),
          .credit_return(credit_inc[g_port][g_vc]),
          .credit_count(credit_count[g_port][g_vc]),
          .credits_available()  // Not used
        );
      end
    end
  endgenerate

  // ============================================================================
  // STATUS AND DEBUG OUTPUTS
  // ============================================================================
  
  always_comb begin
    for (int p = 0; p < NUM_PORTS; p++) begin
      for (int v = 0; v < NUM_VCS; v++) begin
        vc_status[p][v] = (vc_state[p][v] != VC_IDLE);
      end
    end
  end
  
  // Performance counter
  logic packet_sent;
  always_comb begin
    packet_sent = 1'b0;
    for (int p = 0; p < NUM_PORTS; p++) begin
      if (flit_out_valid[p] && flit_out_ready[p] &&
          (flit_out[p].flit_type == FLIT_TYPE_TAIL || 
           flit_out[p].flit_type == FLIT_TYPE_SINGLE)) begin
        packet_sent = 1'b1;
      end
    end
  end
  
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      packets_routed <= '0;
      error_status <= ERR_NONE;
    end else begin
      if (packet_sent) begin
        packets_routed <= packets_routed + 1;
      end
      // Basic error detection (can be expanded)
      error_status <= ERR_NONE;
    end
  end

endmodule
