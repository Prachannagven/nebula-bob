# Nebula GPU Interconnect - Step 1 Implementation

## Overview

This directory contains the Step 1 implementation of the Nebula GPU Interconnect system, focusing on core infrastructure and basic packet structures.

## Directory Structure

```
code/
├── rtl/                          # RTL source files
│   ├── nebula_pkg.sv            # Main package with constants and types
│   └── common/                   # Common utility modules
│       ├── nebula_fifo.sv       # Parameterizable FIFO buffer
│       ├── nebula_credit_flow_ctrl.sv # Credit-based flow control
│       ├── nebula_rr_arbiter.sv # Round-robin arbiter
│       ├── nebula_crc.sv        # CRC generator and checker
│       ├── nebula_packet_assembler.sv   # Packet assembly
│       └── nebula_packet_disassembler.sv # Packet disassembly
├── tb/                           # Testbench directory (for future tests)
├── Makefile                      # Build system
└── README.md                     # This file
```

## Implemented Components

### 1. SystemVerilog Package (`nebula_pkg.sv`)
- **Parameters**: Grid sizes, buffer depths, data widths optimized for GPU workloads
- **Structures**: NoC flit format, AXI4/CHI transaction types
- **Constants**: Virtual channel assignments, QoS levels, error codes
- **Functions**: Utility functions for coordinate validation and distance calculation

### 2. FIFO Buffer (`nebula_fifo.sv`)
- **Features**: Parameterizable width and depth, full/empty flags, data count
- **Optimizations**: Almost full/empty thresholds for flow control
- **Verification**: Built-in assertions for overflow/underflow detection

### 3. Credit-Based Flow Control (`nebula_credit_flow_ctrl.sv`)
- **Implementation**: Hardware credit counters with automatic management
- **Features**: Configurable initial credits, underflow/overflow protection
- **Use Case**: Prevents buffer overflow in NoC links

### 4. Round-Robin Arbiter (`nebula_rr_arbiter.sv`)
- **Algorithm**: True round-robin with rotating priority
- **Features**: N-way arbitration, one-hot grant output, fairness guarantee
- **Components**: Includes priority encoder helper module

### 5. CRC Generator/Checker (`nebula_crc.sv`)
- **Standard**: CRC-32 IEEE 802.3 polynomial
- **Implementation**: Parallel LFSR for high-speed operation
- **Features**: Both generation and verification modes

### 6. Packet Assembly (`nebula_packet_assembler.sv`)
- **Functionality**: Converts payload data to multi-flit NoC packets
- **Features**: Automatic header generation, sequence numbering, CRC insertion
- **State Machine**: Handles HEAD, BODY, TAIL flit generation

### 7. Packet Disassembly (`nebula_packet_disassembler.sv`)
- **Functionality**: Reconstructs payload from incoming NoC flits
- **Features**: Sequence verification, error detection, payload reconstruction
- **Error Handling**: Protocol violation detection and reporting

## Key Design Decisions

### Parameter Selection
- **Flit Width**: 256 bits (matches GPU memory interfaces)
- **Virtual Channels**: 4 VCs per port (maps to CHI message classes)
- **Buffer Depth**: 16 flits per VC (industry standard for GPU traffic)
- **Address Width**: 64 bits (supports large GPU memory spaces)

### NoC Packet Format
- **Header**: 48 bits including routing info, sequence numbers, QoS
- **Payload**: 208 bits per flit (256 - 48 header bits)
- **CRC**: 32-bit IEEE 802.3 polynomial for strong error detection

### Flow Control
- **Credit-based**: Prevents buffer overflow, enables high utilization
- **Per-VC**: Independent flow control for each virtual channel
- **Backpressure**: Automatic stall propagation when buffers full

## Building and Testing

### Prerequisites
- Verilator 5.0+ (for simulation)
- SystemC 3.0+ (for TLM models)
- Make (for build automation)

### Build Commands
```bash
# Compile all RTL
make compile

# Run linting
make lint

# Clean build artifacts
make clean

# Format code (requires verible)
make format
```

### Verification Strategy
Each module includes:
- **Assertions**: SystemVerilog assertions for runtime checking
- **Properties**: Formal properties for key behaviors
- **Error Detection**: Built-in error checking and reporting

## Next Steps (Step 2)

The infrastructure implemented in Step 1 provides the foundation for:
1. **Router Implementation**: 5-stage pipeline using these utility modules
2. **Buffer Architecture**: Multiple VCs using the FIFO and flow control
3. **Routing Logic**: XY routing using the coordinate utilities
4. **Testing Framework**: Unit tests for each utility module

## Key Features Implemented

✅ **Parameterizable Design**: All modules scale with configuration  
✅ **Industry Standards**: 256-bit flits, CRC-32, credit-based flow control  
✅ **Error Detection**: CRC checking, protocol violations, buffer overflows  
✅ **Performance Optimized**: Parallel processing, pipelined operations  
✅ **Verification Ready**: Comprehensive assertions and property checking  

## Module Interfaces

All modules follow consistent interface conventions:
- **Clock/Reset**: Standard active-low reset
- **Valid/Ready**: Standard handshaking protocol
- **Parameterizable**: Configurable via SystemVerilog parameters
- **Assertions**: Built-in verification properties

This implementation provides a solid foundation for the remaining steps of the Nebula GPU interconnect system.
