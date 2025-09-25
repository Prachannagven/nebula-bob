# Nebula GPU Interconnect System

A scalable, cache-coherent Network-on-Chip (NoC) architecture for multi-GPU systems, featuring a 2D mesh topology, AXI4/CHI protocol support, and a real-time web dashboard for simulation and visualization.

---

## Project Structure

```
.
├── code/
│   ├── Makefile
│   ├── python/
│   │   ├── nebula_traffic_generator.py
│   │   └── nebula_vcd_parser.py
│   ├── rtl/
│   │   ├── nebula_mesh_top.sv
│   │   ├── nebula_router.sv
│   │   ├── nebula_axi_noc_bridge.sv
│   │   ├── nebula_chi_noc_bridge.sv
│   │   ├── nebula_packet_assembler.sv
│   │   ├── nebula_packet_disassembler.sv
│   │   └── ...
│   └── tb/
│       └── ...
├── docs/
│   ├── abstract.tex/pdf
│   ├── final_report.tex/pdf
│   ├── presentation.tex/pdf
│   └── images/
├── web_dashboard/
│   ├── backend/ (Flask API)
│   ├── frontend/ (Vite + Tailwind)
│   ├── setup.sh
│   ├── start.sh
│   └── README.md
├── LICENSE
└── .gitignore
```

---

## Key Components

- **RTL (SystemVerilog):**
  - `nebula_mesh_top.sv`, `nebula_router.sv`: Mesh topology and router microarchitecture.
  - `nebula_axi_noc_bridge.sv`, `nebula_chi_noc_bridge.sv`: Protocol translation bridges.
  - `nebula_packet_assembler.sv`, `nebula_packet_disassembler.sv`: Packet/flit conversion.
  - `nebula_credit_flow_ctrl.sv`, `nebula_rr_arbiter.sv`: Flow control and arbitration.

- **Python Tools:**
  - [`nebula_traffic_generator.py`](code/python/nebula_traffic_generator.py): Generates traffic patterns and testbenches.
  - [`nebula_vcd_parser.py`](code/python/nebula_vcd_parser.py): Parses VCD simulation traces for analysis.

- **Testbenches:**
  - Located in `code/tb/`, covering unit, integration, and system-level tests.

- **Web Dashboard:**
  - Real-time mesh visualization, simulation control, and performance monitoring.
  - Backend: Flask + Socket.IO ([`web_dashboard/backend/app.py`](web_dashboard/backend/app.py))
  - Frontend: Vanilla JS + Vite + Tailwind ([`web_dashboard/frontend/`](web_dashboard/frontend/))

- **Documentation:**
  - Technical reports, presentations, and architecture diagrams in `docs/`.

---

## Quick Start

### 1. Setup

```sh
cd web_dashboard
chmod +x setup.sh start.sh
./setup.sh
```

### 2. Run the Dashboard

```sh
./start.sh
```

- The dashboard will be available at [http://localhost:5000](http://localhost:5000).

### 3. Run Verilog Simulations

- Use the dashboard to generate traffic, launch simulations, and visualize results.
- For manual runs:
  ```sh
  cd code
  make tb_nebula_traffic
  ```

---

## Features

- **Scalable 2D mesh topology (2×2 to 8×8)**
- **Five-stage router pipeline with virtual channels**
- **AXI4 and CHI protocol support**
- **Adaptive and deterministic routing**
- **Credit-based flow control**
- **Python-based traffic generation and VCD analysis**
- **Web dashboard for real-time visualization and performance monitoring**

---

## Documentation

- [docs/abstract.tex](docs/abstract.tex): Project abstract
- [docs/final_report.tex](docs/final_report.tex): Technical implementation report
- [docs/presentation.tex](docs/presentation.tex): Technical presentation (LaTeX Beamer)

---

## License

See [LICENSE](LICENSE) for details.

---

## Authors

- Pranav Chandra
- Pramit Pal
- Meghadri Ghosh

Team Bob

---

## RTL Module Technical Reference (code/rtl/)

### nebula_top.sv
Top-level system integration. Instantiates the mesh, protocol bridges, configuration, monitoring, and debug logic. Entry point for the full NoC system.

```systemverilog
parameter int MESH_WIDTH = 8;
```
Defines the mesh width (number of columns) as a configurable parameter.

```systemverilog
input  logic clk,
input  logic rst_n,
```
Standard clock and active-low reset inputs for synchronous logic.

```systemverilog
function automatic logic [COORD_WIDTH-1:0] get_x_coord(input int node_id);
  return node_id % MESH_WIDTH;
endfunction
```
Utility function to compute the X coordinate of a node in the mesh from its node ID.

```systemverilog
generate
  for (genvar i = 0; i < NUM_NODES; i++) begin : gen_nodes
    // ... instantiation ...
  end
endgenerate
```
Instantiates all mesh nodes (routers, bridges, etc.) using a generate loop.

```systemverilog
assign config_write_enable = config_req_valid && config_req_ready && config_req_write;
```
Determines when a configuration register write should occur.

```systemverilog
assign system_status = {
  16'h5A5A, 4'h0, 4'(MESH_HEIGHT), 4'(MESH_WIDTH), 1'b0, ENABLE_CHI, ENABLE_AXI, 1'b1
};
```
Aggregates system status into a single 32-bit register for monitoring.

```systemverilog
always_ff @(posedge clk) begin
  if (!rst_n) begin
    node_errors <= '0;
  end else begin
    // ... error aggregation ...
  end
end
```
Aggregates error signals from all nodes for system-level error reporting.

---

### nebula_system_top.sv
System-level integration for mesh, memory, and protocol interfaces.

```systemverilog
nebula_mesh_top #(.MESH_WIDTH(4), .MESH_HEIGHT(4)) mesh_inst (...);
```
Instantiates the mesh topology with specified dimensions.

```systemverilog
assign mem_addr = global_addr[ADDR_WIDTH-1:0];
```
Maps a global address to a memory address for the system.

```systemverilog
always_ff @(posedge clk) begin
  if (!rst_n) begin
    // ... reset logic ...
  end else begin
    // ... system-level coordination ...
  end
end
```
Handles system-level reset and coordination logic.

---

### nebula_mesh_top.sv
Mesh topology generator.

```systemverilog
generate
  for (genvar x = 0; x < MESH_WIDTH; x++) begin
    for (genvar y = 0; y < MESH_HEIGHT; y++) begin
      nebula_router router_inst (...);
    end
  end
endgenerate
```
Instantiates routers in a 2D grid based on mesh parameters.

```systemverilog
assign router_ports[i][PORT_NORTH] = (y == 0) ? '0 : router_ports[neighbor_north][PORT_SOUTH];
```
Connects router ports to their neighbors, handling edge conditions.

---

### nebula_router.sv
Five-stage router microarchitecture.

```systemverilog
always_ff @(posedge clk) begin
  if (in_valid && in_ready) begin
    input_fifo.push(in_flit);
  end
end
```
Buffer Write stage: pushes incoming flits into the input FIFO.

```systemverilog
route = (dest_x > x) ? EAST : (dest_x < x) ? WEST : (dest_y > y) ? SOUTH : NORTH;
```
Route Computation stage: determines output direction based on destination coordinates.

```systemverilog
if (vc_credits[vc_id] > 0) begin
  // VC Allocation stage: allocate VC if credits available
end
```
Checks if a virtual channel has available credits before allocation.

```systemverilog
arbiter.request[port] = input_fifo[port].valid;
```
Switch Allocation stage: requests crossbar access for valid input ports.

```systemverilog
output_fifo.push(input_fifo[grant_port].pop());
```
Switch Traversal stage: moves flit from input to output FIFO after arbitration.

```systemverilog
if (input_fifo.full) begin
  error_flag <= 1'b1;
end
```
Error detection: sets error flag if input FIFO overflows.

---

### nebula_axi_if.sv
AXI4 interface wrapper.

```systemverilog
assign axi_aw_ready = !aw_fifo.full;
```
Indicates AXI write address channel is ready if FIFO is not full.

```systemverilog
always_ff @(posedge clk) begin
  if (axi_w_valid && axi_w_ready) begin
    w_fifo.push(axi_w_data);
  end
end
```
Captures AXI write data into a FIFO.

```systemverilog
assign axi_b_valid = !b_fifo.empty;
```
Indicates AXI write response is valid if response FIFO is not empty.

---

### nebula_axi_noc_bridge.sv
AXI4-to-NoC protocol bridge.

```systemverilog
if (axi_aw_valid && axi_aw_ready) begin
  // Start burst to NoC packet conversion
end
```
Detects the start of an AXI burst and initiates packetization.

```systemverilog
reorder_buffer[axi_id] = ...;
```
Stores transaction info for out-of-order response handling.

```systemverilog
if (noc_flit_valid && noc_flit_ready) begin
  // Assemble AXI response from NoC flits
end
```
Reassembles AXI responses from incoming NoC flits.

---

### nebula_chi_interface.sv
CHI protocol interface logic.

```systemverilog
always_ff @(posedge clk) begin
  if (chi_req_valid) begin
    // CHI protocol FSM
  end
end
```
Implements the CHI protocol finite state machine for request handling.

```systemverilog
assign chi_resp_ready = !resp_fifo.full;
```
Indicates CHI response channel is ready if FIFO is not full.

---

### nebula_chi_noc_bridge.sv
CHI-to-NoC protocol bridge.

```systemverilog
case (chi_msg_type)
  CHI_SNP: // Map to NoC VC for snoop
  CHI_REQ: // Map to NoC VC for request
endcase
```
Maps CHI message types to NoC virtual channels for prioritization.

```systemverilog
if (timeout) begin
  // Handle snoop response timeout
end
```
Handles timeouts for snoop responses.

---

### nebula_chi_directory.sv
Directory-based MOESI cache coherency controller for CHI.

```systemverilog
always_ff @(posedge clk) begin
  if (snoop_req) begin
    // Directory state update
  end
end
```
Updates directory state on snoop requests.

```systemverilog
case (moesi_state)
  MOESI_M: // Handle Modified state
  MOESI_O: // Handle Owned state
  // ...
endcase
```
Implements MOESI state transitions for cache lines.

---

### nebula_niu_axi.sv
Network Interface Unit for AXI.

```systemverilog
assign router_flit_in = assembled_flit;
```
Sends assembled flits from the protocol bridge to the router.

```systemverilog
if (router_flit_out_valid) begin
  // Depacketize and send to AXI
end
```
Receives flits from the router and depacketizes them for the AXI interface.

---

### nebula_packet_assembler.sv
Packet assembler for protocol-to-NoC conversion.

```systemverilog
flit.header = '{type: HEAD, src: src_id, dest: dest_id, ...};
```
Constructs the flit header for the first flit of a packet.

```systemverilog
for (int i = 0; i < num_flits; i++) begin
  flit[i].payload = ...;
end
```
Segments the payload across multiple flits if needed.

---

### nebula_packet_disassembler.sv
Packet disassembler for NoC-to-protocol conversion.

```systemverilog
if (flit.header.type == TAIL) begin
  // Complete transaction assembly
end
```
Detects the last flit of a packet and triggers transaction reassembly.

```systemverilog
if (crc_check_failed) begin
  error_flag <= 1'b1;
end
```
Sets an error flag if CRC check fails on a received packet.

---

### nebula_pkg.sv
Global package file.

```systemverilog
parameter int FLIT_WIDTH = 256;
```
Defines the width of a NoC flit.

```systemverilog
typedef struct packed {
  logic [3:0] flit_type;
  logic [7:0] src_id, dest_id;
  logic [255:0] payload;
} noc_flit_t;
```
Defines the structure of a NoC flit.

```systemverilog
enum logic [2:0] {NORTH, SOUTH, EAST, WEST, LOCAL} port_dir_e;
```
Enumerates the possible router port directions.

---

### nebula_top_simple.sv
Simplified top-level integration.

```systemverilog
module nebula_top_simple(...);
  // Minimal mesh instantiation
endmodule
```
A minimal top-level module for basic mesh and protocol testing.

---

### common/
Reusable modules for core NoC functionality:

**nebula_crc.sv**
```systemverilog
function logic [31:0] crc32(input logic [255:0] data);
  // CRC calculation logic
endfunction
```
Implements CRC-32 calculation for error detection.

**nebula_credit_flow_ctrl.sv**
```systemverilog
always_ff @(posedge clk) begin
  if (flit_sent) credits <= credits - 1;
  if (flit_accepted) credits <= credits + 1;
end
```
Implements per-VC credit-based flow control.

**nebula_fifo.sv**
```systemverilog
always_ff @(posedge clk) begin
  if (write_en) mem[wr_ptr] <= data_in;
  if (read_en) data_out <= mem[rd_ptr];
end
```
Implements a parameterized FIFO buffer.

**nebula_rr_arbiter.sv**
```systemverilog
always_ff @(posedge clk) begin
  if (grant) last_grant <= next_grant;
end
```
Implements round-robin arbitration for fair resource allocation.