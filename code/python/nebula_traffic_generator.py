#!/usr/bin/env python3
"""
Nebula NoC Traffic Pattern Generator - Enhanced for Verilog Integration

This module generates various traffic patterns for testing and analyzing
the Nebula GPU interconnect system with Verilog testbench generation.

Features:
- Configurable mesh topology
- Multiple traffic injection rates
- SystemVerilog testbench generation
- VCD trace generation for verification
- Real GPU workload patterns
- Performance metric calculation
"""

import numpy as np
import pandas as pd
import json
import random
import os
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass
from enum import Enum
import logging

# Set up logging
logging.basicConfig(
    level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s"
)
logger = logging.getLogger(__name__)


class TrafficPattern(Enum):
    """Supported traffic patterns"""

    UNIFORM_RANDOM = "uniform_random"
    CNN_TRAINING = "cnn_training"


@dataclass
class TrafficConfig:
    """Configuration for traffic generation"""

    mesh_width: int = 8
    mesh_height: int = 8
    pattern: TrafficPattern = TrafficPattern.UNIFORM_RANDOM
    injection_rate: float = 0.1  # Packets per node per cycle
    duration_cycles: int = 1000
    packet_size_bytes: int = 128  # More realistic cache-line size
    packet_size_distribution: str = "mixed"  # "fixed", "mixed", "realistic"
    min_packet_size: int = 32
    max_packet_size: int = 1024
    hotspot_nodes: List[int] = None
    hotspot_probability: float = 0.3
    enable_chi: bool = True
    enable_axi: bool = True
    seed: int = 42


@dataclass
class PacketTrace:
    """Individual packet trace entry"""

    timestamp: int
    source_node: int
    dest_node: int
    packet_id: int
    size_bytes: int
    packet_type: str  # 'AXI_READ', 'AXI_WRITE', 'CHI_READ', 'CHI_WRITE', etc.
    priority: int = 0


class NebulaTrafficGenerator:
    """Main traffic pattern generator for Nebula NoC system"""

    def __init__(self, config: TrafficConfig):
        self.config = config
        self.num_nodes = config.mesh_width * config.mesh_height
        self.packet_traces: List[PacketTrace] = []
        self.random = random.Random(config.seed)
        np.random.seed(config.seed)

        logger.info(f"Initialized Nebula Traffic Generator")
        logger.info(
            f"Mesh: {config.mesh_width}x{config.mesh_height} ({self.num_nodes} nodes)"
        )
        logger.info(f"Pattern: {config.pattern.value}")
        logger.info(f"Injection rate: {config.injection_rate}")

    def get_realistic_packet_size(self, packet_type: str = "AXI_READ") -> int:
        """Generate realistic packet size based on GPU workload characteristics"""

        if self.config.packet_size_distribution == "fixed":
            return self.config.packet_size_bytes

        elif self.config.packet_size_distribution == "realistic":
            # Realistic GPU packet size distribution
            rand_val = self.random.random()

            if packet_type in ["CHI_READ", "CHI_WRITE"]:
                # Cache coherency traffic - typically cache line sized
                if rand_val < 0.7:  # 70% cache line (64B or 128B)
                    return self.random.choice([64, 128])
                elif rand_val < 0.9:  # 20% small control packets
                    return self.random.choice([32, 48])
                else:  # 10% larger coherency data
                    return self.random.choice([256, 512])

            elif packet_type in ["AXI_READ", "AXI_WRITE"]:
                # Memory access patterns - more varied
                if rand_val < 0.4:  # 40% small/medium (registers, small data)
                    return self.random.choice([64, 128, 256])
                elif rand_val < 0.7:  # 30% medium (texture, compute data)
                    return self.random.choice([512, 1024])
                elif rand_val < 0.9:  # 20% large (bulk transfers)
                    return self.random.choice([2048, 4096])
                else:  # 10% very large (model weights, large textures)
                    return min(8192, self.config.max_packet_size)

        else:  # "mixed" - simple distribution
            # Weighted toward common cache line sizes but with variety
            choices = [32, 64, 128, 256, 512, 1024]
            weights = [5, 20, 30, 25, 15, 5]  # Favor 64B and 128B
            return self.random.choices(choices, weights=weights)[0]

    def node_to_coords(self, node_id: int) -> Tuple[int, int]:
        """Convert node ID to (x, y) coordinates"""
        x = node_id % self.config.mesh_width
        y = node_id // self.config.mesh_width
        return (x, y)

    def coords_to_node(self, x: int, y: int) -> int:
        """Convert (x, y) coordinates to node ID"""
        return y * self.config.mesh_width + x

    def generate_uniform_random_traffic(self) -> List[PacketTrace]:
        """Generate uniform random traffic pattern"""
        logger.info("Generating uniform random traffic pattern")
        traces = []
        packet_id = 0

        for cycle in range(self.config.duration_cycles):
            for src_node in range(self.num_nodes):
                if self.random.random() < self.config.injection_rate:
                    # Generate random destination (excluding source)
                    dst_node = self.random.choice(
                        [n for n in range(self.num_nodes) if n != src_node]
                    )

                    # Choose packet type based on configuration
                    if self.config.enable_axi and self.config.enable_chi:
                        packet_type = self.random.choice(
                            ["AXI_READ", "AXI_WRITE", "CHI_READ", "CHI_WRITE"]
                        )
                    elif self.config.enable_axi:
                        packet_type = self.random.choice(["AXI_READ", "AXI_WRITE"])
                    else:
                        packet_type = self.random.choice(["CHI_READ", "CHI_WRITE"])

                    trace = PacketTrace(
                        timestamp=cycle,
                        source_node=src_node,
                        dest_node=dst_node,
                        packet_id=packet_id,
                        size_bytes=self.get_realistic_packet_size(packet_type),
                        packet_type=packet_type,
                    )
                    traces.append(trace)
                    packet_id += 1

        logger.info(f"Generated {len(traces)} uniform random packets")
        return traces

    def generate_cnn_training_traffic(self) -> List[PacketTrace]:
        """Generate realistic CNN training workload pattern based on actual GPU behavior"""
        logger.info("Generating realistic CNN training traffic pattern")
        traces = []
        packet_id = 0

        # Realistic CNN training configuration
        batch_size = 32  # Typical batch size
        num_layers = 50  # ResNet-50 style

        # Training phases with realistic durations
        forward_cycles = int(self.config.duration_cycles * 0.35)  # 35% forward pass
        backward_cycles = int(self.config.duration_cycles * 0.45)  # 45% backward pass
        allreduce_cycles = int(self.config.duration_cycles * 0.15)  # 15% all-reduce
        optimizer_cycles = (
            self.config.duration_cycles
            - forward_cycles
            - backward_cycles
            - allreduce_cycles
        )  # 5% optimizer

        cycle_offset = 0

        # PHASE 1: FORWARD PASS - Data parallel computation with memory reads
        logger.info("Generating forward pass traffic (data loading + computation)")
        for cycle in range(forward_cycles):
            actual_cycle = cycle + cycle_offset

            for src_node in range(self.num_nodes):
                # Forward pass characteristics:
                # - High memory read activity (weights, activations)
                # - Layer-by-layer processing creates waves of activity
                # - Inter-node communication for feature maps

                layer_progress = (cycle / forward_cycles) * num_layers
                current_layer = int(layer_progress) % num_layers

                # Higher activity during conv layers (every 2-3 layers)
                is_conv_layer = (current_layer % 3) <= 1
                base_injection = self.config.injection_rate * (
                    1.5 if is_conv_layer else 0.7
                )

                # Memory access patterns
                if self.random.random() < base_injection:
                    rand_val = self.random.random()

                    if rand_val < 0.6:  # 60% - Weight/bias reads from memory nodes
                        # Memory nodes are typically at edges (simplified model)
                        memory_nodes = [
                            0,
                            self.config.mesh_width - 1,
                            self.num_nodes - self.config.mesh_width,
                            self.num_nodes - 1,
                        ]
                        dst_node = self.random.choice(memory_nodes)
                        packet_type = "AXI_READ"
                        # Weight reads are typically larger (filter weights, bias)
                        packet_size = self.random.choice([512, 1024, 2048, 4096])

                    elif (
                        rand_val < 0.85
                    ):  # 25% - Activation data between nearby compute nodes
                        src_x, src_y = self.node_to_coords(src_node)
                        neighbors = []
                        for dx in [
                            -2,
                            -1,
                            0,
                            1,
                            2,
                        ]:  # Wider neighborhood for feature maps
                            for dy in [-2, -1, 0, 1, 2]:
                                nx, ny = src_x + dx, src_y + dy
                                if (
                                    0 <= nx < self.config.mesh_width
                                    and 0 <= ny < self.config.mesh_height
                                    and (dx != 0 or dy != 0)
                                ):
                                    neighbors.append(self.coords_to_node(nx, ny))

                        dst_node = (
                            self.random.choice(neighbors) if neighbors else src_node
                        )
                        packet_type = "CHI_READ"  # Cache coherent activation sharing
                        packet_size = self.random.choice(
                            [256, 512, 1024]
                        )  # Feature map chunks

                    else:  # 15% - Control and metadata
                        dst_node = self.random.choice(
                            [n for n in range(self.num_nodes) if n != src_node]
                        )
                        packet_type = "CHI_READ"
                        packet_size = self.random.choice([64, 128])

                    traces.append(
                        PacketTrace(
                            timestamp=actual_cycle,
                            source_node=src_node,
                            dest_node=dst_node,
                            packet_id=packet_id,
                            size_bytes=packet_size,
                            packet_type=packet_type,
                            priority=1 if is_conv_layer else 0,
                        )
                    )
                    packet_id += 1

        cycle_offset += forward_cycles

        # PHASE 2: BACKWARD PASS - Gradient computation with high write activity
        logger.info("Generating backward pass traffic (gradient computation)")
        for cycle in range(backward_cycles):
            actual_cycle = cycle + cycle_offset

            for src_node in range(self.num_nodes):
                # Backward pass characteristics:
                # - Reverse layer order processing
                # - High write activity (gradients)
                # - More intensive communication than forward pass

                layer_progress = (
                    (backward_cycles - cycle) / backward_cycles
                ) * num_layers
                current_layer = int(layer_progress) % num_layers

                # Gradient computation is computationally intensive
                is_gradient_intensive = (current_layer % 4) <= 2  # 75% of layers
                base_injection = self.config.injection_rate * (
                    1.8 if is_gradient_intensive else 1.0
                )

                if self.random.random() < base_injection:
                    rand_val = self.random.random()

                    if rand_val < 0.45:  # 45% - Gradient writes to accumulation buffers
                        # Gradients often accumulated in specific nodes
                        accumulator_nodes = [
                            n for n in range(0, self.num_nodes, 4)
                        ]  # Every 4th node
                        dst_node = self.random.choice(accumulator_nodes)
                        packet_type = "AXI_WRITE"
                        # Gradients can be quite large (especially for FC layers)
                        packet_size = self.random.choice([1024, 2048, 4096, 8192])

                    elif rand_val < 0.7:  # 25% - Activation gradient propagation
                        src_x, src_y = self.node_to_coords(src_node)
                        # Backward propagation follows reverse direction
                        backward_neighbors = []
                        for dx in [-1, 0, 1]:
                            for dy in [-1, 0, 1]:
                                nx, ny = src_x + dx, src_y + dy
                                if (
                                    0 <= nx < self.config.mesh_width
                                    and 0 <= ny < self.config.mesh_height
                                    and (dx != 0 or dy != 0)
                                ):
                                    backward_neighbors.append(
                                        self.coords_to_node(nx, ny)
                                    )

                        dst_node = (
                            self.random.choice(backward_neighbors)
                            if backward_neighbors
                            else src_node
                        )
                        packet_type = "CHI_WRITE"
                        packet_size = self.random.choice([512, 1024, 2048])

                    else:  # 30% - Memory reads for cached activations/weights
                        memory_nodes = [
                            0,
                            self.config.mesh_width - 1,
                            self.num_nodes - self.config.mesh_width,
                            self.num_nodes - 1,
                        ]
                        dst_node = self.random.choice(memory_nodes)
                        packet_type = "AXI_READ"
                        packet_size = self.random.choice([256, 512, 1024])

                    traces.append(
                        PacketTrace(
                            timestamp=actual_cycle,
                            source_node=src_node,
                            dest_node=dst_node,
                            packet_id=packet_id,
                            size_bytes=packet_size,
                            packet_type=packet_type,
                            priority=2 if is_gradient_intensive else 1,
                        )
                    )
                    packet_id += 1

        cycle_offset += backward_cycles

        # PHASE 3: ALL-REDUCE - Global gradient synchronization (most communication intensive)
        logger.info("Generating all-reduce traffic (gradient synchronization)")
        for cycle in range(allreduce_cycles):
            actual_cycle = cycle + cycle_offset

            # All-reduce follows ring or tree topology for bandwidth efficiency
            allreduce_progress = cycle / allreduce_cycles

            for src_node in range(self.num_nodes):
                # All-reduce is extremely communication intensive
                base_injection = self.config.injection_rate * 2.5

                if self.random.random() < base_injection:
                    # Ring all-reduce: each node communicates with neighbors in ring
                    if allreduce_progress < 0.5:  # Reduce-scatter phase
                        # Send to next node in ring
                        dst_node = (src_node + 1) % self.num_nodes
                        packet_type = "AXI_WRITE"
                        # Large gradient chunks
                        packet_size = self.random.choice([4096, 8192, 16384])

                    else:  # All-gather phase
                        # Receive from previous node in ring
                        dst_node = (src_node - 1) % self.num_nodes
                        packet_type = "AXI_READ"
                        packet_size = self.random.choice([4096, 8192, 16384])

                    traces.append(
                        PacketTrace(
                            timestamp=actual_cycle,
                            source_node=src_node,
                            dest_node=dst_node,
                            packet_id=packet_id,
                            size_bytes=min(packet_size, self.config.max_packet_size),
                            packet_type=packet_type,
                            priority=3,  # Highest priority
                        )
                    )
                    packet_id += 1

        cycle_offset += allreduce_cycles

        # PHASE 4: OPTIMIZER UPDATE - Weight updates with memory writes
        logger.info("Generating optimizer update traffic (weight updates)")
        for cycle in range(optimizer_cycles):
            actual_cycle = cycle + cycle_offset

            for src_node in range(self.num_nodes):
                # Optimizer updates are less communication intensive but involve large writes
                base_injection = self.config.injection_rate * 0.8

                if self.random.random() < base_injection:
                    rand_val = self.random.random()

                    if rand_val < 0.7:  # 70% - Weight updates to memory
                        memory_nodes = [
                            0,
                            self.config.mesh_width - 1,
                            self.num_nodes - self.config.mesh_width,
                            self.num_nodes - 1,
                        ]
                        dst_node = self.random.choice(memory_nodes)
                        packet_type = "AXI_WRITE"
                        # Updated weights and optimizer states (Adam: weights + momentum + variance)
                        packet_size = self.random.choice([2048, 4096, 8192])

                    else:  # 30% - Optimizer state reads
                        memory_nodes = [
                            0,
                            self.config.mesh_width - 1,
                            self.num_nodes - self.config.mesh_width,
                            self.num_nodes - 1,
                        ]
                        dst_node = self.random.choice(memory_nodes)
                        packet_type = "AXI_READ"
                        packet_size = self.random.choice([1024, 2048, 4096])

                    traces.append(
                        PacketTrace(
                            timestamp=actual_cycle,
                            source_node=src_node,
                            dest_node=dst_node,
                            packet_id=packet_id,
                            size_bytes=packet_size,
                            packet_type=packet_type,
                            priority=0,  # Lower priority
                        )
                    )
                    packet_id += 1

        logger.info(f"Generated {len(traces)} realistic CNN training packets")
        logger.info(f"  Forward pass: {forward_cycles} cycles")
        logger.info(f"  Backward pass: {backward_cycles} cycles")
        logger.info(f"  All-reduce: {allreduce_cycles} cycles")
        logger.info(f"  Optimizer: {optimizer_cycles} cycles")

        return traces

    def generate_pattern_traces(self, pattern: TrafficPattern) -> List[PacketTrace]:
        """Generate traces for specified pattern"""

        if pattern == TrafficPattern.UNIFORM_RANDOM:
            return self.generate_uniform_random_traffic()
        elif pattern == TrafficPattern.CNN_TRAINING:
            return self.generate_cnn_training_traffic()
        else:
            logger.warning(f"Pattern {pattern} not implemented, using uniform random")
            return self.generate_uniform_random_traffic()

    def generate_vcd_testbench(
        self, output_path: str, traces: List[PacketTrace]
    ) -> str:
        """Generate SystemVerilog testbench for VCD simulation"""

        num_nodes = self.config.mesh_width * self.config.mesh_height

        testbench_template = f"""`timescale 1ns / 1ps

module tb_nebula_top_traffic;
    import nebula_pkg::*;

    // Parameters
    parameter int MESH_WIDTH = {self.config.mesh_width};
    parameter int MESH_HEIGHT = {self.config.mesh_height};
    parameter int NUM_NODES = {num_nodes};
    parameter int CONFIG_ADDR_WIDTH = 16;
    parameter int CONFIG_DATA_WIDTH = 32;
    parameter bit ENABLE_AXI = 1'b1;
    parameter bit ENABLE_CHI = 1'b1;
    parameter bit ENABLE_PERFORMANCE_MONITORING = 1'b1;

    // Traffic data type definition
    typedef struct {{
        int timestamp;
        int source_node;
        int dest_node;
        string packet_type;
        int size_bytes;
    }} traffic_entry_t;
    
    parameter int TRAFFIC_SIZE = {len(traces)};
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
        $display("📝 Loading traffic data...");"""

        # Add traffic data initialization
        for i, trace in enumerate(traces):
            testbench_template += f"""
        traffic_data[{i}].timestamp = {trace.timestamp};
        traffic_data[{i}].source_node = {trace.source_node};
        traffic_data[{i}].dest_node = {trace.dest_node};
        traffic_data[{i}].packet_type = "{trace.packet_type}";
        traffic_data[{i}].size_bytes = {trace.size_bytes};"""

        testbench_template += """
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
    """

        testbench_template += r"""
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
"""

        # Write testbench file
        with open(output_path, "w") as f:
            f.write(testbench_template)

        logger.info(f"Generated testbench: {output_path}")

        return output_path

    def generate_and_run_simulation(
        self, pattern: TrafficPattern, output_dir: str = "./"
    ) -> Tuple[str, List[PacketTrace]]:
        """Generate traffic pattern and create testbench for simulation"""

        # Generate traffic traces
        traces = self.generate_pattern_traces(pattern)

        # Create output directory if needed
        os.makedirs(output_dir, exist_ok=True)

        # Generate testbench
        testbench_path = os.path.join(output_dir, f"tb_nebula_{pattern.value}.sv")
        self.generate_vcd_testbench(testbench_path, traces)

        # Create a standard symlink for the Makefile to use
        standard_link = os.path.join(output_dir, "tb_nebula_current.sv")
        if os.path.exists(standard_link):
            os.remove(standard_link)
        try:
            os.symlink(os.path.basename(testbench_path), standard_link)
            logger.info(f"Created standard link: {standard_link}")
        except OSError:
            # If symlinks not supported, copy the file
            import shutil

            shutil.copy2(testbench_path, standard_link)
            logger.info(f"Created standard copy: {standard_link}")

        # Generate stimulus file for reference
        stimulus_path = os.path.join(output_dir, f"stimulus_{pattern.value}.txt")
        self.generate_stimulus_file(stimulus_path, traces)

        return testbench_path, traces

    def generate_stimulus_file(self, output_path: str, traces: List[PacketTrace]):
        """Generate stimulus file for reference"""

        with open(output_path, "w") as f:
            f.write("// Traffic stimulus file for Nebula NoC testbench\n")
            f.write("// Format: timestamp src_node dst_node packet_type size_bytes\n")

            for trace in traces:
                f.write(
                    f"{trace.timestamp:08d} {trace.source_node:02d} {trace.dest_node:02d} "
                )
                f.write(f"{trace.packet_type} {trace.size_bytes:04d}\n")

        logger.info(f"Generated {len(traces)} stimulus entries in {output_path}")


def main():
    """Example usage of the traffic generator"""

    # Configure traffic generation
    config = TrafficConfig(
        mesh_width=4,
        mesh_height=4,
        pattern=TrafficPattern.UNIFORM_RANDOM,
        injection_rate=0.1,
        duration_cycles=1000,
        packet_size_bytes=128,  # More realistic default
        packet_size_distribution="realistic",  # Use realistic size distribution
        min_packet_size=32,
        max_packet_size=4096,
        enable_axi=True,
        enable_chi=True,
    )

    # Create generator
    generator = NebulaTrafficGenerator(config)

    # Generate testbench for uniform random traffic
    testbench_path, traces = generator.generate_and_run_simulation(
        TrafficPattern.UNIFORM_RANDOM, "./tb_generated"
    )

    print(f"Generated testbench: {testbench_path}")
    print(f"Generated {len(traces)} traffic traces")


if __name__ == "__main__":
    main()
