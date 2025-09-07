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
    HOTSPOT = "hotspot"
    TRANSPOSE = "transpose"
    BIT_REVERSE = "bit_reverse"
    CNN_TRAINING = "cnn_training"
    MATRIX_MULTIPLY = "matrix_multiply"
    TRANSFORMER = "transformer"
    TORNADO = "tornado"
    BIT_COMPLEMENT = "bit_complement"


@dataclass
class TrafficConfig:
    """Configuration for traffic generation"""

    mesh_width: int = 4
    mesh_height: int = 4
    pattern: TrafficPattern = TrafficPattern.UNIFORM_RANDOM
    injection_rate: float = 0.1  # Packets per node per cycle
    duration_cycles: int = 1000
    packet_size_bytes: int = 64
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
                        size_bytes=self.config.packet_size_bytes,
                        packet_type=packet_type,
                    )
                    traces.append(trace)
                    packet_id += 1

        logger.info(f"Generated {len(traces)} uniform random packets")
        return traces

    def generate_hotspot_traffic(self) -> List[PacketTrace]:
        """Generate hotspot traffic pattern"""
        logger.info("Generating hotspot traffic pattern")
        traces = []
        packet_id = 0

        # Default hotspot nodes if not specified
        hotspot_nodes = self.config.hotspot_nodes or [
            0,
            self.num_nodes // 2,
            self.num_nodes - 1,
        ]

        for cycle in range(self.config.duration_cycles):
            for src_node in range(self.num_nodes):
                if self.random.random() < self.config.injection_rate:
                    # Choose destination: hotspot with configured probability
                    if self.random.random() < self.config.hotspot_probability:
                        dst_node = self.random.choice(hotspot_nodes)
                    else:
                        dst_node = self.random.choice(
                            [n for n in range(self.num_nodes) if n != src_node]
                        )

                    packet_type = self.random.choice(
                        ["AXI_READ", "AXI_WRITE", "CHI_READ", "CHI_WRITE"]
                    )

                    trace = PacketTrace(
                        timestamp=cycle,
                        source_node=src_node,
                        dest_node=dst_node,
                        packet_id=packet_id,
                        size_bytes=self.config.packet_size_bytes,
                        packet_type=packet_type,
                    )
                    traces.append(trace)
                    packet_id += 1

        logger.info(f"Generated {len(traces)} hotspot packets")
        return traces

    def generate_transpose_traffic(self) -> List[PacketTrace]:
        """Generate transpose traffic pattern"""
        logger.info("Generating transpose traffic pattern")
        traces = []
        packet_id = 0

        for cycle in range(self.config.duration_cycles):
            for src_node in range(self.num_nodes):
                if self.random.random() < self.config.injection_rate:
                    # Transpose: (x,y) -> (y,x)
                    src_x, src_y = self.node_to_coords(src_node)
                    dst_x, dst_y = src_y, src_x

                    # Ensure destination is within bounds
                    if (
                        dst_x < self.config.mesh_width
                        and dst_y < self.config.mesh_height
                    ):
                        dst_node = self.coords_to_node(dst_x, dst_y)

                        packet_type = self.random.choice(["AXI_READ", "AXI_WRITE"])

                        trace = PacketTrace(
                            timestamp=cycle,
                            source_node=src_node,
                            dest_node=dst_node,
                            packet_id=packet_id,
                            size_bytes=self.config.packet_size_bytes,
                            packet_type=packet_type,
                        )
                        traces.append(trace)
                        packet_id += 1

        logger.info(f"Generated {len(traces)} transpose packets")
        return traces

    def generate_cnn_training_traffic(self) -> List[PacketTrace]:
        """Generate CNN training workload pattern"""
        logger.info("Generating CNN training traffic pattern")
        traces = []
        packet_id = 0

        # CNN training phases
        phase_duration = self.config.duration_cycles // 3

        for cycle in range(self.config.duration_cycles):
            phase = cycle // phase_duration

            for src_node in range(self.num_nodes):
                injection_prob = self.config.injection_rate

                # Adjust injection based on phase
                if phase == 0:  # Forward pass
                    injection_prob *= 0.8
                elif phase == 1:  # Backward pass
                    injection_prob *= 1.2
                else:  # Weight update/all-reduce
                    injection_prob *= 0.6

                if self.random.random() < injection_prob:
                    if phase <= 1:  # Forward/backward - local communication
                        src_x, src_y = self.node_to_coords(src_node)
                        # Prefer communication with nearby nodes
                        neighbors = []
                        for dx in [-1, 0, 1]:
                            for dy in [-1, 0, 1]:
                                nx, ny = src_x + dx, src_y + dy
                                if (
                                    0 <= nx < self.config.mesh_width
                                    and 0 <= ny < self.config.mesh_height
                                    and (dx != 0 or dy != 0)
                                ):
                                    neighbors.append(self.coords_to_node(nx, ny))

                        if neighbors:
                            dst_node = self.random.choice(neighbors)
                        else:
                            dst_node = self.random.choice(
                                [n for n in range(self.num_nodes) if n != src_node]
                            )
                    else:  # All-reduce - global communication
                        dst_node = self.random.choice(
                            [n for n in range(self.num_nodes) if n != src_node]
                        )

                    packet_type = "AXI_WRITE" if phase == 0 else "AXI_READ"

                    trace = PacketTrace(
                        timestamp=cycle,
                        source_node=src_node,
                        dest_node=dst_node,
                        packet_id=packet_id,
                        size_bytes=self.config.packet_size_bytes
                        * (2 if phase == 2 else 1),
                        packet_type=packet_type,
                    )
                    traces.append(trace)
                    packet_id += 1

        logger.info(f"Generated {len(traces)} CNN training packets")
        return traces

    def generate_pattern_traces(self, pattern: TrafficPattern) -> List[PacketTrace]:
        """Generate traces for specified pattern"""

        if pattern == TrafficPattern.UNIFORM_RANDOM:
            return self.generate_uniform_random_traffic()
        elif pattern == TrafficPattern.HOTSPOT:
            return self.generate_hotspot_traffic()
        elif pattern == TrafficPattern.TRANSPOSE:
            return self.generate_transpose_traffic()
        elif pattern == TrafficPattern.CNN_TRAINING:
            return self.generate_cnn_training_traffic()
        else:
            logger.warning(f"Pattern {pattern} not implemented, using uniform random")
            return self.generate_uniform_random_traffic()

    def generate_vcd_testbench(
        self, output_path: str, traces: List[PacketTrace]
    ) -> str:
        """Generate SystemVerilog testbench for VCD simulation"""

        testbench_template = f"""`timescale 1ns / 1ps

module tb_nebula_top_traffic;

    // Clock and reset
    logic clk;
    logic rst_n;
    
    // Traffic stimulus data
    typedef struct {{
        int timestamp;
        int source_node;
        int dest_node;
        string packet_type;
        int size_bytes;
    }} traffic_entry_t;
    
    parameter int TRAFFIC_SIZE = {len(traces)};
    traffic_entry_t traffic_data[TRAFFIC_SIZE];
    
    // DUT instantiation
    nebula_top #(
        .MESH_WIDTH({self.config.mesh_width}),
        .MESH_HEIGHT({self.config.mesh_height}),
        .ENABLE_AXI({1 if self.config.enable_axi else 0}),
        .ENABLE_CHI({1 if self.config.enable_chi else 0})
    ) dut (
        .clk(clk),
        .rst_n(rst_n),
        .config_req_valid(1'b0),
        .config_req_ready(),
        .config_req_addr(16'h0),
        .config_req_data(32'h0),
        .config_req_write(1'b0),
        .config_resp_valid(),
        .config_resp_ready(1'b1),
        .config_resp_data(),
        .config_resp_error(),
        .debug_trace_node_id()
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  // 100MHz clock
    end

    // Reset generation
    initial begin
        rst_n = 0;
        repeat(10) @(posedge clk);
        rst_n = 1;
        $display("Reset released at time %0t", $time);
    end

    // Traffic injection
    initial begin
        // Wait for reset
        wait(rst_n);
        repeat(5) @(posedge clk);
        
        $display("Starting traffic injection...");
        load_traffic_data();
        inject_traffic();
        
        // Let simulation run for additional cycles
        repeat(100) @(posedge clk);
        
        $display("Simulation completed");
        $finish;
    end

    // VCD dumping
    initial begin
        $dumpfile("tb_nebula_top.vcd");
        $dumpvars(0, tb_nebula_top_traffic);
        $display("VCD dump started");
    end

    // Load traffic data
    task load_traffic_data();
        // Load pre-generated traffic pattern
"""

        # Add traffic data initialization
        for i, trace in enumerate(traces):
            testbench_template += f"""        traffic_data[{i}].timestamp = {trace.timestamp};
        traffic_data[{i}].source_node = {trace.source_node};
        traffic_data[{i}].dest_node = {trace.dest_node};
        traffic_data[{i}].packet_type = "{trace.packet_type}";
        traffic_data[{i}].size_bytes = {trace.size_bytes};
"""

        testbench_template += (
            """    endtask

    // Traffic injection task
    task inject_traffic();
        int cycle_count = 0;
        
        for (int i = 0; i < TRAFFIC_SIZE; i++) begin
            // Wait for correct cycle
            while (cycle_count < traffic_data[i].timestamp) begin
                @(posedge clk);
                cycle_count++;
            end
            
            // Inject packet at source node
            inject_packet(
                traffic_data[i].source_node,
                traffic_data[i].dest_node,
                traffic_data[i].packet_type,
                traffic_data[i].size_bytes
            );
        end
    endtask

    // Packet injection task
    task inject_packet(int src_node, int dst_node, string pkt_type, int size);
        // Convert node IDs to coordinates
        int src_x = src_node % """
            + str(self.config.mesh_width)
            + """;
        int src_y = src_node / """
            + str(self.config.mesh_width)
            + """;
        int dst_x = dst_node % """
            + str(self.config.mesh_width)
            + """;
        int dst_y = dst_node / """
            + str(self.config.mesh_width)
            + """;
        
        $display("Time %0t: Injecting %s packet from (%0d,%0d) to (%0d,%0d), size=%0d", 
                 $time, pkt_type, src_x, src_y, dst_x, dst_y, size);
                 
        // TODO: Add actual AXI/CHI transaction injection based on packet type
        // This would interface with the DUT's AXI/CHI interfaces
    endtask

endmodule
"""
        )

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
        packet_size_bytes=64,
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
