# Nebula Dashboard - Python VCD Integration

## Overview

The Nebula Dashboard now includes comprehensive VCD (Value Change Dump) integration that allows you to:

1. **Load VCD files** generated from Verilog simulations
2. **Replay traffic patterns** based on real simulation data
3. **Visualize actual NoC behavior** from hardware simulations

## VCD Integration Features

### Simple VCD Parser
- **Custom parser** (`nebula_vcd_parser.py`) designed specifically for Nebula NoC signals
- **Extracts packet events** (injection, forwarding, arrival) from router signals
- **Router activity analysis** and utilization calculation
- **Lightweight and fast** - no external dependencies required

### VCD Dashboard Controls

| Key | Action | Description |
|-----|---------|-------------|
| `L` | Load VCD | Automatically searches for recent VCD files |
| `T` | Toggle Replay | Start/pause VCD-based traffic replay |
| `↑/↓` | Replay Speed | Adjust replay speed (0.1x to 10x) |
| `0` | Reset Replay | Return to start of VCD trace |

### VCD File Sources

The dashboard automatically looks for VCD files in these locations:
- `../build/obj_dir/tb_nebula_top.vcd` - Top-level system simulation
- `../build/nebula_mesh_integration_tb.vcd` - Mesh integration test
- `../build/nebula_router_tb.vcd` - Individual router test

## Usage Examples

### 1. Generate VCD from Simulation
```bash
# Run a Verilog simulation to generate VCD trace
make tb_nebula_top

# The simulation will create a VCD file with traffic patterns
```

### 2. Load and Replay VCD
```bash
# Start the dashboard
make dashboard

# In the dashboard:
# 1. Press 'L' to load the most recent VCD file
# 2. Press 'T' to start VCD replay
# 3. Use ↑/↓ to adjust replay speed
# 4. Watch real simulation traffic patterns!
```

### 3. Analyze VCD Data
```python
# Use the parser directly for analysis
from nebula_vcd_parser import SimpleVCDParser

parser = SimpleVCDParser("simulation.vcd")
if parser.parse():
    print(f"Found {len(parser.packet_events)} packet events")
    print(f"Simulation duration: {parser.get_simulation_duration()}")
    
    # Get router activity
    activity = parser.get_router_activity()
    for router_id, events in activity.items():
        print(f"Router {router_id}: {len(events)} events")
```

## VCD Signal Mapping

The parser looks for these signal patterns in VCD files:

### Router Signals
- `*router_*` - Router instance hierarchy
- `*valid*in*` - Input valid signals (packet injection detection)
- `*valid*out*` - Output valid signals (packet forwarding detection)
- `*flit*in*` - Input flit data
- `*flit*out*` - Output flit data

### Packet Event Extraction
1. **Injection Events**: When input_valid transitions from 0→1
2. **Forward Events**: When output_valid transitions from 0→1
3. **Router Activity**: Tracked per router based on signal changes

## Advanced Features

### Real-time Visualization
- VCD events are converted to visual packets in real-time
- Packet colors and types are assigned based on simulation data
- Router utilization reflects actual simulation activity

### Performance Analysis
- Router utilization calculated from VCD events
- Traffic pattern recognition from simulation traces
- Congestion visualization based on real hardware behavior

### Integration with Live Simulation
- Load VCD files while simulations are running
- Automatic file detection and loading
- Seamless switching between synthetic and real traffic

## Troubleshooting

### VCD File Not Found
- Ensure simulation completed successfully: `make tb_nebula_top`
- Check build directory: `ls ../build/obj_dir/*.vcd`
- Verify VCD generation in testbench: `$dumpfile` and `$dumpvars`

### Parser Errors
- Check VCD file format with: `head -50 file.vcd`
- Ensure signal names match expected patterns
- Try with a simpler testbench first

### Performance Issues
- Large VCD files may slow replay - adjust speed with ↑/↓
- Use time-limited simulations for better performance
- Consider extracting specific time ranges for analysis

## Implementation Notes

### VCD Parser Design
- **Hierarchical signal parsing**: Handles nested module structures
- **Time-based event extraction**: Correlates signal changes with timestamps
- **Router identification**: Uses signal naming patterns to identify routers
- **Packet event correlation**: Links input/output events to packet flow

### Dashboard Integration
- **Non-blocking operation**: VCD replay runs alongside live simulation
- **Dynamic packet creation**: VCD events create visualization packets
- **Status display**: Real-time VCD replay status and progress
- **Speed control**: Adjustable replay rate for analysis

This integration provides a powerful bridge between Verilog simulation and interactive visualization, enabling comprehensive analysis of NoC behavior with real hardware simulation data.
