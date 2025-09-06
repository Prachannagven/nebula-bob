#!/usr/bin/env python3
"""
Nebula NoC Traffic Pattern Generator

This module generates various traffic patterns for testing and analyzing
the Nebula GPU interconnect system. It supports:
- Uniform random traffic
- Hotspot traffic patterns
- Transpose and bit-reverse patterns
- GPU-specific workload patterns
- Custom application traces

Features:
- Configurable mesh topology
- Multiple traffic injection rates
- Statistical analysis and visualization
- VCD trace generation for verification
- Performance metric calculation
"""

import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import argparse
import json
import random
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
    NEIGHBOR = "neighbor"
    GPU_WORKLOAD = "gpu_workload"
    MATRIX_MULTIPLY = "matrix_multiply"
    CONVOLUTION = "convolution"
    ALLREDUCE = "allreduce"


@dataclass
class TrafficConfig:
    """Configuration for traffic generation"""

    mesh_width: int = 4
    mesh_height: int = 4
    pattern: TrafficPattern = TrafficPattern.UNIFORM_RANDOM
    injection_rate: float = 0.1  # Packets per node per cycle
    duration_cycles: int = 10000
    packet_size_bytes: int = 64
    hotspot_nodes: List[int] = None
    hotspot_probability: float = 0.3
    burst_size: int = 1
    inter_burst_delay: int = 0
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


@dataclass
class PerformanceMetrics:
    """Performance analysis results"""

    total_packets: int
    total_bytes: int
    avg_latency_cycles: float
    max_latency_cycles: int
    throughput_gbps: float
    network_utilization: float
    hotspot_congestion: float
    load_balance_index: float


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

    def manhattan_distance(self, src_node: int, dst_node: int) -> int:
        """Calculate Manhattan distance between two nodes"""
        src_x, src_y = self.node_to_coords(src_node)
        dst_x, dst_y = self.node_to_coords(dst_node)
        return abs(dst_x - src_x) + abs(dst_y - src_y)

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

        logger.info(f"Generated {len(traces)} packets for uniform random traffic")
        return traces

    def generate_hotspot_traffic(self) -> List[PacketTrace]:
        """Generate hotspot traffic pattern"""
        logger.info("Generating hotspot traffic pattern")
        traces = []
        packet_id = 0

        # Default hotspot nodes (center nodes)
        if self.config.hotspot_nodes is None:
            center_x = self.config.mesh_width // 2
            center_y = self.config.mesh_height // 2
            hotspot_nodes = [self.coords_to_node(center_x, center_y)]
            if self.config.mesh_width > 2 and self.config.mesh_height > 2:
                hotspot_nodes.extend(
                    [
                        self.coords_to_node(center_x - 1, center_y),
                        self.coords_to_node(center_x + 1, center_y),
                        self.coords_to_node(center_x, center_y - 1),
                        self.coords_to_node(center_x, center_y + 1),
                    ]
                )
            hotspot_nodes = [n for n in hotspot_nodes if 0 <= n < self.num_nodes]
        else:
            hotspot_nodes = self.config.hotspot_nodes

        logger.info(f"Hotspot nodes: {hotspot_nodes}")

        for cycle in range(self.config.duration_cycles):
            for src_node in range(self.num_nodes):
                if self.random.random() < self.config.injection_rate:
                    # Choose destination: hotspot with probability, otherwise random
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

        logger.info(f"Generated {len(traces)} packets for hotspot traffic")
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
                    else:
                        dst_node = self.random.choice(
                            [n for n in range(self.num_nodes) if n != src_node]
                        )

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

        logger.info(f"Generated {len(traces)} packets for transpose traffic")
        return traces

    def generate_gpu_workload_traffic(self) -> List[PacketTrace]:
        """Generate GPU-specific workload traffic patterns"""
        logger.info("Generating GPU workload traffic pattern")
        traces = []
        packet_id = 0

        # GPU workloads typically have:
        # 1. High bandwidth memory access (AXI)
        # 2. Cache coherency traffic (CHI)
        # 3. Bursty behavior
        # 4. Spatial locality

        for cycle in range(self.config.duration_cycles):
            for src_node in range(self.num_nodes):
                injection_prob = self.config.injection_rate

                # Increase injection for certain "compute" nodes
                compute_nodes = [
                    n for n in range(0, self.num_nodes, 2)
                ]  # Even numbered nodes
                if src_node in compute_nodes:
                    injection_prob *= 2.0

                if self.random.random() < injection_prob:
                    # GPU workload destinations show spatial locality
                    src_x, src_y = self.node_to_coords(src_node)

                    # 70% chance for nearby nodes, 30% for distant
                    if self.random.random() < 0.7:
                        # Nearby destination (within 2 hops)
                        nearby_nodes = []
                        for dx in range(-2, 3):
                            for dy in range(-2, 3):
                                new_x, new_y = src_x + dx, src_y + dy
                                if (
                                    0 <= new_x < self.config.mesh_width
                                    and 0 <= new_y < self.config.mesh_height
                                ):
                                    node = self.coords_to_node(new_x, new_y)
                                    if node != src_node:
                                        nearby_nodes.append(node)

                        dst_node = (
                            self.random.choice(nearby_nodes)
                            if nearby_nodes
                            else src_node
                        )
                    else:
                        # Distant destination
                        dst_node = self.random.choice(
                            [n for n in range(self.num_nodes) if n != src_node]
                        )

                    # GPU workloads are memory intensive (larger packets)
                    if self.random.random() < 0.6:  # 60% AXI memory traffic
                        packet_type = self.random.choice(["AXI_READ", "AXI_WRITE"])
                        size_bytes = self.config.packet_size_bytes * self.random.choice(
                            [1, 2, 4, 8]
                        )
                    else:  # 40% CHI coherency traffic
                        packet_type = self.random.choice(["CHI_READ", "CHI_WRITE"])
                        size_bytes = self.config.packet_size_bytes

                    trace = PacketTrace(
                        timestamp=cycle,
                        source_node=src_node,
                        dest_node=dst_node,
                        packet_id=packet_id,
                        size_bytes=size_bytes,
                        packet_type=packet_type,
                        priority=1 if packet_type.startswith("CHI") else 0,
                    )
                    traces.append(trace)
                    packet_id += 1

        logger.info(f"Generated {len(traces)} packets for GPU workload traffic")
        return traces

    def generate_traffic(self) -> List[PacketTrace]:
        """Generate traffic based on configured pattern"""
        if self.config.pattern == TrafficPattern.UNIFORM_RANDOM:
            return self.generate_uniform_random_traffic()
        elif self.config.pattern == TrafficPattern.HOTSPOT:
            return self.generate_hotspot_traffic()
        elif self.config.pattern == TrafficPattern.TRANSPOSE:
            return self.generate_transpose_traffic()
        elif self.config.pattern == TrafficPattern.GPU_WORKLOAD:
            return self.generate_gpu_workload_traffic()
        else:
            logger.warning(
                f"Pattern {self.config.pattern} not implemented, using uniform random"
            )
            return self.generate_uniform_random_traffic()

    def analyze_performance(self, traces: List[PacketTrace]) -> PerformanceMetrics:
        """Analyze performance metrics from packet traces"""
        if not traces:
            return PerformanceMetrics(0, 0, 0, 0, 0, 0, 0, 0)

        total_packets = len(traces)
        total_bytes = sum(trace.size_bytes for trace in traces)

        # Calculate latencies (simplified: use Manhattan distance * 2 cycles per hop)
        latencies = []
        for trace in traces:
            hops = self.manhattan_distance(trace.source_node, trace.dest_node)
            latency = max(1, hops * 2)  # Minimum 1 cycle latency
            latencies.append(latency)

        avg_latency = np.mean(latencies)
        max_latency = max(latencies)

        # Calculate throughput (simplified)
        duration_seconds = self.config.duration_cycles * 1e-9  # Assuming 1 GHz clock
        throughput_gbps = (total_bytes * 8) / (duration_seconds * 1e9)

        # Network utilization (simplified)
        max_possible_packets = self.num_nodes * self.config.duration_cycles
        network_utilization = total_packets / max_possible_packets

        # Hotspot congestion analysis
        dest_counts = {}
        for trace in traces:
            dest_counts[trace.dest_node] = dest_counts.get(trace.dest_node, 0) + 1

        if dest_counts:
            avg_dest_traffic = np.mean(list(dest_counts.values()))
            max_dest_traffic = max(dest_counts.values())
            hotspot_congestion = (
                max_dest_traffic / avg_dest_traffic if avg_dest_traffic > 0 else 1.0
            )
        else:
            hotspot_congestion = 1.0

        # Load balance index (coefficient of variation)
        if dest_counts:
            traffic_std = np.std(list(dest_counts.values()))
            load_balance_index = (
                traffic_std / avg_dest_traffic if avg_dest_traffic > 0 else 0.0
            )
        else:
            load_balance_index = 0.0

        return PerformanceMetrics(
            total_packets=total_packets,
            total_bytes=total_bytes,
            avg_latency_cycles=avg_latency,
            max_latency_cycles=max_latency,
            throughput_gbps=throughput_gbps,
            network_utilization=network_utilization,
            hotspot_congestion=hotspot_congestion,
            load_balance_index=load_balance_index,
        )

    def save_traces(self, traces: List[PacketTrace], filename: str):
        """Save packet traces to JSON file"""
        trace_data = []
        for trace in traces:
            trace_data.append(
                {
                    "timestamp": trace.timestamp,
                    "source_node": trace.source_node,
                    "dest_node": trace.dest_node,
                    "packet_id": trace.packet_id,
                    "size_bytes": trace.size_bytes,
                    "packet_type": trace.packet_type,
                    "priority": trace.priority,
                }
            )

        output_data = {
            "config": {
                "mesh_width": self.config.mesh_width,
                "mesh_height": self.config.mesh_height,
                "pattern": self.config.pattern.value,
                "injection_rate": self.config.injection_rate,
                "duration_cycles": self.config.duration_cycles,
                "seed": self.config.seed,
            },
            "traces": trace_data,
        }

        with open(filename, "w") as f:
            json.dump(output_data, f, indent=2)

        logger.info(f"Saved {len(traces)} traces to {filename}")

    def generate_vcd_testbench(self, traces: List[PacketTrace], filename: str):
        """Generate SystemVerilog testbench for VCD simulation"""
        with open(filename, "w") as f:
            f.write(
                f"""`timescale 1ns / 1ps

module tb_nebula_traffic_pattern();
  
  localparam int CLK_PERIOD = 10; // 100 MHz clock
  localparam int MESH_WIDTH = {self.config.mesh_width};
  localparam int MESH_HEIGHT = {self.config.mesh_height};
  localparam int NUM_NODES = MESH_WIDTH * MESH_HEIGHT;
  
  logic clk = 0;
  logic rst_n = 0;
  
  // Clock generation
  always #(CLK_PERIOD/2) clk = ~clk;
  
  // DUT instantiation
  nebula_top #(
    .MESH_WIDTH(MESH_WIDTH),
    .MESH_HEIGHT(MESH_HEIGHT)
  ) dut (
    .clk(clk),
    .rst_n(rst_n),
    // Other signals...
  );
  
  initial begin
    $dumpfile("nebula_traffic_pattern.vcd");
    $dumpvars(0, tb_nebula_traffic_pattern);
    
    // Reset sequence
    rst_n = 0;
    #(CLK_PERIOD * 5);
    rst_n = 1;
    #(CLK_PERIOD * 2);
    
    // Traffic injection based on generated pattern
"""
            )

            # Group traces by timestamp for efficient simulation
            traces_by_time = {}
            for trace in traces:
                if trace.timestamp not in traces_by_time:
                    traces_by_time[trace.timestamp] = []
                traces_by_time[trace.timestamp].append(trace)

            current_cycle = 0
            for timestamp in sorted(traces_by_time.keys()):
                if timestamp > current_cycle:
                    f.write(f"    // Wait until cycle {timestamp}\\n")
                    f.write(
                        f"    repeat({timestamp - current_cycle}) @(posedge clk);\\n"
                    )
                    current_cycle = timestamp

                f.write(f"    // Inject packets at cycle {timestamp}\\n")
                for trace in traces_by_time[timestamp]:
                    f.write(
                        f"    // Packet {trace.packet_id}: {trace.source_node} -> {trace.dest_node} ({trace.packet_type})\\n"
                    )
                    f.write(
                        f'    inject_packet({trace.source_node}, {trace.dest_node}, {trace.size_bytes}, "{trace.packet_type}");\\n'
                    )

            f.write(
                f"""
    // Wait for completion
    repeat(1000) @(posedge clk);
    
    $display("Traffic pattern simulation completed");
    $finish;
  end
  
  task inject_packet(
    input int src_node,
    input int dst_node, 
    input int size_bytes,
    input string pkt_type
  );
    // Implementation depends on specific interface
    $display("[%0t] Injecting %s packet: %0d -> %0d (%0d bytes)", 
             $time, pkt_type, src_node, dst_node, size_bytes);
  endtask

endmodule
"""
            )

        logger.info(f"Generated VCD testbench: {filename}")


def create_visualizations(
    generator: NebulaTrafficGenerator,
    traces: List[PacketTrace],
    metrics: PerformanceMetrics,
    output_dir: str = "analysis/plots",
):
    """Create visualizations for traffic analysis"""
    import os

    os.makedirs(output_dir, exist_ok=True)

    # Set style
    plt.style.use("seaborn-v0_8")
    sns.set_palette("husl")

    # 1. Traffic matrix heatmap
    fig, ax = plt.subplots(figsize=(10, 8))
    traffic_matrix = np.zeros((generator.num_nodes, generator.num_nodes))

    for trace in traces:
        traffic_matrix[trace.source_node][trace.dest_node] += 1

    sns.heatmap(traffic_matrix, annot=True, fmt="g", cmap="YlOrRd", ax=ax)
    ax.set_title(f"Traffic Matrix - {generator.config.pattern.value.title()}")
    ax.set_xlabel("Destination Node")
    ax.set_ylabel("Source Node")
    plt.tight_layout()
    plt.savefig(f"{output_dir}/traffic_matrix.png", dpi=300, bbox_inches="tight")
    plt.close()

    # 2. Temporal traffic distribution
    fig, ax = plt.subplots(figsize=(12, 6))
    timestamps = [trace.timestamp for trace in traces]
    ax.hist(timestamps, bins=50, alpha=0.7, edgecolor="black")
    ax.set_title("Temporal Traffic Distribution")
    ax.set_xlabel("Simulation Cycle")
    ax.set_ylabel("Number of Packets")
    ax.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(f"{output_dir}/temporal_distribution.png", dpi=300, bbox_inches="tight")
    plt.close()

    # 3. Node utilization
    fig, ax = plt.subplots(figsize=(12, 6))
    src_counts = {}
    dst_counts = {}

    for trace in traces:
        src_counts[trace.source_node] = src_counts.get(trace.source_node, 0) + 1
        dst_counts[trace.dest_node] = dst_counts.get(trace.dest_node, 0) + 1

    nodes = list(range(generator.num_nodes))
    src_values = [src_counts.get(node, 0) for node in nodes]
    dst_values = [dst_counts.get(node, 0) for node in nodes]

    width = 0.35
    x = np.arange(len(nodes))
    ax.bar(x - width / 2, src_values, width, label="Source", alpha=0.8)
    ax.bar(x + width / 2, dst_values, width, label="Destination", alpha=0.8)

    ax.set_title("Node Utilization")
    ax.set_xlabel("Node ID")
    ax.set_ylabel("Number of Packets")
    ax.set_xticks(x)
    ax.set_xticklabels(nodes)
    ax.legend()
    ax.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(f"{output_dir}/node_utilization.png", dpi=300, bbox_inches="tight")
    plt.close()

    # 4. Performance metrics summary
    fig, ((ax1, ax2), (ax3, ax4)) = plt.subplots(2, 2, figsize=(12, 10))

    # Latency distribution
    latencies = []
    for trace in traces:
        hops = generator.manhattan_distance(trace.source_node, trace.dest_node)
        latency = max(1, hops * 2)
        latencies.append(latency)

    ax1.hist(latencies, bins=20, alpha=0.7, edgecolor="black")
    ax1.set_title("Latency Distribution")
    ax1.set_xlabel("Latency (cycles)")
    ax1.set_ylabel("Number of Packets")
    ax1.axvline(
        metrics.avg_latency_cycles,
        color="red",
        linestyle="--",
        label=f"Avg: {metrics.avg_latency_cycles:.1f}",
    )
    ax1.legend()
    ax1.grid(True, alpha=0.3)

    # Packet type distribution
    type_counts = {}
    for trace in traces:
        type_counts[trace.packet_type] = type_counts.get(trace.packet_type, 0) + 1

    types = list(type_counts.keys())
    counts = list(type_counts.values())
    ax2.pie(counts, labels=types, autopct="%1.1f%%", startangle=90)
    ax2.set_title("Packet Type Distribution")

    # Performance metrics bar chart
    metric_names = [
        "Throughput\\n(Gbps)",
        "Network\\nUtilization",
        "Hotspot\\nCongestion",
        "Load Balance\\nIndex",
    ]
    metric_values = [
        metrics.throughput_gbps,
        metrics.network_utilization,
        metrics.hotspot_congestion,
        metrics.load_balance_index,
    ]

    bars = ax3.bar(metric_names, metric_values, alpha=0.8)
    ax3.set_title("Performance Metrics")
    ax3.set_ylabel("Value")
    for i, bar in enumerate(bars):
        height = bar.get_height()
        ax3.text(
            bar.get_x() + bar.get_width() / 2.0,
            height + 0.01,
            f"{metric_values[i]:.3f}",
            ha="center",
            va="bottom",
        )
    ax3.grid(True, alpha=0.3)

    # Distance distribution
    distances = []
    for trace in traces:
        dist = generator.manhattan_distance(trace.source_node, trace.dest_node)
        distances.append(dist)

    ax4.hist(distances, bins=range(max(distances) + 2), alpha=0.7, edgecolor="black")
    ax4.set_title("Communication Distance Distribution")
    ax4.set_xlabel("Manhattan Distance (hops)")
    ax4.set_ylabel("Number of Packets")
    ax4.grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(f"{output_dir}/performance_summary.png", dpi=300, bbox_inches="tight")
    plt.close()

    logger.info(f"Generated visualizations in {output_dir}/")


def main():
    parser = argparse.ArgumentParser(description="Nebula NoC Traffic Pattern Generator")
    parser.add_argument("--mesh-width", type=int, default=4, help="Mesh width")
    parser.add_argument("--mesh-height", type=int, default=4, help="Mesh height")
    parser.add_argument(
        "--pattern",
        type=str,
        default="uniform_random",
        choices=[p.value for p in TrafficPattern],
        help="Traffic pattern",
    )
    parser.add_argument(
        "--injection-rate",
        type=float,
        default=0.1,
        help="Injection rate (packets per node per cycle)",
    )
    parser.add_argument(
        "--duration", type=int, default=10000, help="Simulation duration (cycles)"
    )
    parser.add_argument(
        "--packet-size", type=int, default=64, help="Packet size (bytes)"
    )
    parser.add_argument("--seed", type=int, default=42, help="Random seed")
    parser.add_argument(
        "--output",
        type=str,
        default="analysis/traffic_trace.json",
        help="Output trace file",
    )
    parser.add_argument(
        "--generate-vcd", action="store_true", help="Generate VCD testbench"
    )
    parser.add_argument(
        "--visualize", action="store_true", help="Generate visualization plots"
    )

    args = parser.parse_args()

    # Create configuration
    config = TrafficConfig(
        mesh_width=args.mesh_width,
        mesh_height=args.mesh_height,
        pattern=TrafficPattern(args.pattern),
        injection_rate=args.injection_rate,
        duration_cycles=args.duration,
        packet_size_bytes=args.packet_size,
        seed=args.seed,
    )

    # Generate traffic
    generator = NebulaTrafficGenerator(config)
    traces = generator.generate_traffic()

    # Analyze performance
    metrics = generator.analyze_performance(traces)

    # Print results
    print("\\n" + "=" * 60)
    print("NEBULA NOC TRAFFIC ANALYSIS RESULTS")
    print("=" * 60)
    print(f"Configuration:")
    print(
        f"  Mesh: {config.mesh_width}x{config.mesh_height} ({generator.num_nodes} nodes)"
    )
    print(f"  Pattern: {config.pattern.value}")
    print(f"  Injection Rate: {config.injection_rate}")
    print(f"  Duration: {config.duration_cycles} cycles")
    print(f"\\nPerformance Metrics:")
    print(f"  Total Packets: {metrics.total_packets:,}")
    print(f"  Total Bytes: {metrics.total_bytes:,}")
    print(f"  Avg Latency: {metrics.avg_latency_cycles:.2f} cycles")
    print(f"  Max Latency: {metrics.max_latency_cycles} cycles")
    print(f"  Throughput: {metrics.throughput_gbps:.3f} Gbps")
    print(f"  Network Utilization: {metrics.network_utilization:.3f}")
    print(f"  Hotspot Congestion: {metrics.hotspot_congestion:.3f}")
    print(f"  Load Balance Index: {metrics.load_balance_index:.3f}")
    print("=" * 60)

    # Save traces
    generator.save_traces(traces, args.output)

    # Generate VCD testbench if requested
    if args.generate_vcd:
        vcd_filename = args.output.replace(".json", "_tb.sv")
        generator.generate_vcd_testbench(traces, vcd_filename)

    # Generate visualizations if requested
    if args.visualize:
        create_visualizations(generator, traces, metrics)


if __name__ == "__main__":
    main()
