#!/usr/bin/env python3
"""
Nebula GPU Interconnect System Dashboard

A comprehensive pygame-based dashboard that demonstrates the capabilities
of the Nebula NoC system by interfacing with Verilog simulations and
providing real-time visualization of network traffic, performance metrics,
and system status.

Features:
- Real-time mesh topology visualization
- Traffic flow animation with packet tracking
- Performance monitoring with graphs and metrics
- Interactive controls for traffic patterns
- VCD file analysis and replay with custom parser
- Router status and congestion visualization
- Protocol-aware packet visualization (AXI4/CHI)
- Integration with live Verilog simulation data

VCD Integration:
- Load VCD files from Verilog simulations (press 'L')
- Replay real traffic patterns from hardware traces (press 'T')
- Adjust replay speed and analyze router utilization
- Seamless integration with live simulation generation
"""

import pygame
import sys
import os
import json
import time
import math
import random
import subprocess
import threading
import queue
from enum import Enum
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional
import numpy as np

# Try to import vcd parser for trace analysis
try:
    import vcdvcd

    VCD_AVAILABLE = True
except ImportError:
    VCD_AVAILABLE = False
    print("Warning: vcdvcd not available. VCD analysis features disabled.")

# Import our simple VCD parser
try:
    from nebula_vcd_parser import SimpleVCDParser, PacketEvent

    VCD_PARSER_AVAILABLE = True
except ImportError:
    VCD_PARSER_AVAILABLE = False
    print("Warning: nebula_vcd_parser not available. Simple VCD parsing disabled.")

# Initialize Pygame
pygame.init()

# Dashboard Configuration
WINDOW_WIDTH = 1400
WINDOW_HEIGHT = 900
FPS = 60

# Colors
COLORS = {
    "background": (20, 20, 30),
    "panel_bg": (40, 40, 50),
    "mesh_bg": (30, 30, 40),
    "router_idle": (100, 100, 120),
    "router_active": (80, 200, 80),
    "router_congested": (200, 80, 80),
    "router_border": (150, 150, 170),
    "link_idle": (60, 60, 80),
    "link_active": (100, 150, 200),
    "packet_req": (255, 100, 100),
    "packet_resp": (100, 255, 100),
    "packet_snoop": (100, 100, 255),
    "packet_data": (255, 255, 100),
    "text": (255, 255, 255),
    "text_dim": (180, 180, 180),
    "button": (70, 70, 90),
    "button_hover": (90, 90, 110),
    "button_active": (60, 120, 200),
    "grid_line": (50, 50, 60),
    "performance_good": (80, 200, 80),
    "performance_medium": (200, 200, 80),
    "performance_bad": (200, 80, 80),
}


# Packet Types for Protocol Visualization
class PacketType(Enum):
    REQ = "REQ"  # CHI Request
    RSP = "RSP"  # CHI Response
    SNP = "SNP"  # CHI Snoop
    DAT = "DAT"  # CHI Data
    AXI_AR = "AR"  # AXI Address Read
    AXI_AW = "AW"  # AXI Address Write
    AXI_W = "W"  # AXI Write Data
    AXI_R = "R"  # AXI Read Data
    AXI_B = "B"  # AXI Write Response


@dataclass
class Packet:
    """Represents a packet moving through the NoC"""

    id: int
    src_x: int
    src_y: int
    dst_x: int
    dst_y: int
    packet_type: PacketType
    current_x: float
    current_y: float
    path: List[Tuple[int, int]]
    hop_index: int
    timestamp: float
    size_flits: int = 1


@dataclass
class RouterStats:
    """Router performance statistics"""

    node_id: int
    x: int
    y: int
    packets_received: int = 0
    packets_sent: int = 0
    buffer_utilization: float = 0.0
    average_latency: float = 0.0
    congestion_level: float = 0.0
    active_vcs: int = 0


class TrafficPattern(Enum):
    UNIFORM_RANDOM = "uniform_random"
    HOTSPOT = "hotspot"
    TRANSPOSE = "transpose"
    GPU_WORKLOAD = "gpu_workload"
    CUSTOM = "custom"


class NebulaDashboard:
    def __init__(self):
        self.screen = pygame.display.set_mode((WINDOW_WIDTH, WINDOW_HEIGHT))
        pygame.display.set_caption("Nebula GPU Interconnect Dashboard")
        self.clock = pygame.time.Clock()
        self.font_large = pygame.font.Font(None, 24)
        self.font_medium = pygame.font.Font(None, 18)
        self.font_small = pygame.font.Font(None, 14)

        # Mesh configuration
        self.mesh_width = 4
        self.mesh_height = 4
        self.num_nodes = self.mesh_width * self.mesh_height

        # Dashboard state
        self.running = True
        self.paused = False
        self.simulation_running = False
        self.current_pattern = TrafficPattern.UNIFORM_RANDOM
        self.injection_rate = 0.1
        self.packets = []
        self.packet_counter = 0
        self.router_stats = [
            RouterStats(i, i % self.mesh_width, i // self.mesh_width)
            for i in range(self.num_nodes)
        ]

        # Performance tracking
        self.performance_history = []
        self.max_history_length = 100
        self.last_stats_update = time.time()

        # UI Layout
        self.setup_ui_layout()

        # Simulation control
        self.verilog_process = None
        self.vcd_file = None
        self.vcd_data = None
        self.vcd_parser = None
        self.vcd_replay_active = False
        self.vcd_replay_time = 0
        self.vcd_replay_speed = 1.0

        # Traffic generation
        self.traffic_thread = None
        self.traffic_queue = queue.Queue()

        print("Nebula Dashboard initialized successfully!")

    def setup_ui_layout(self):
        """Setup UI panel positions and sizes"""
        # Main mesh visualization area
        self.mesh_panel = pygame.Rect(20, 80, 600, 600)

        # Control panels
        self.control_panel = pygame.Rect(640, 80, 200, 300)
        self.stats_panel = pygame.Rect(640, 400, 200, 280)
        self.performance_panel = pygame.Rect(860, 80, 520, 600)

        # Mesh grid setup
        self.router_size = 40
        self.router_spacing = 120
        self.mesh_start_x = self.mesh_panel.x + 60
        self.mesh_start_y = self.mesh_panel.y + 60

    def get_router_position(self, x, y):
        """Get screen position of router at mesh coordinates (x,y)"""
        screen_x = self.mesh_start_x + x * self.router_spacing
        screen_y = self.mesh_start_y + y * self.router_spacing
        return (screen_x, screen_y)

    def xy_routing_path(self, src_x, src_y, dst_x, dst_y):
        """Calculate XY routing path between source and destination"""
        path = [(src_x, src_y)]
        current_x, current_y = src_x, src_y

        # Move in X direction first
        while current_x != dst_x:
            if current_x < dst_x:
                current_x += 1
            else:
                current_x -= 1
            path.append((current_x, current_y))

        # Then move in Y direction
        while current_y != dst_y:
            if current_y < dst_y:
                current_y += 1
            else:
                current_y -= 1
            path.append((current_x, current_y))

        return path

    def generate_packet(self, pattern: TrafficPattern = None):
        """Generate a new packet based on traffic pattern"""
        if pattern is None:
            pattern = self.current_pattern

        # Source selection
        src_x = random.randint(0, self.mesh_width - 1)
        src_y = random.randint(0, self.mesh_height - 1)

        # Destination selection based on pattern
        if pattern == TrafficPattern.UNIFORM_RANDOM:
            dst_x = random.randint(0, self.mesh_width - 1)
            dst_y = random.randint(0, self.mesh_height - 1)

        elif pattern == TrafficPattern.HOTSPOT:
            # 70% traffic goes to hotspot node (3,3)
            if random.random() < 0.7:
                dst_x, dst_y = 3, 3
            else:
                dst_x = random.randint(0, self.mesh_width - 1)
                dst_y = random.randint(0, self.mesh_height - 1)

        elif pattern == TrafficPattern.TRANSPOSE:
            # Transpose pattern: (x,y) -> (y,x)
            dst_x, dst_y = src_y, src_x

        elif pattern == TrafficPattern.GPU_WORKLOAD:
            # GPU-like pattern: memory controllers at edges, compute in center
            if src_x == 0 or src_x == self.mesh_width - 1:  # Memory controller
                # Send to compute nodes in center
                dst_x = random.randint(1, self.mesh_width - 2)
                dst_y = random.randint(1, self.mesh_height - 2)
            else:  # Compute node
                # Send to memory controllers
                dst_x = random.choice([0, self.mesh_width - 1])
                dst_y = random.randint(0, self.mesh_height - 1)
        else:
            dst_x = random.randint(0, self.mesh_width - 1)
            dst_y = random.randint(0, self.mesh_height - 1)

        # Don't generate self-packets
        if src_x == dst_x and src_y == dst_y:
            return None

        # Select packet type based on workload
        packet_types = [PacketType.REQ, PacketType.RSP, PacketType.DAT, PacketType.SNP]
        if pattern == TrafficPattern.GPU_WORKLOAD:
            # GPU workload has more data and requests
            packet_types = [
                PacketType.REQ,
                PacketType.DAT,
                PacketType.DAT,
                PacketType.RSP,
            ]

        packet_type = random.choice(packet_types)

        # Calculate routing path
        path = self.xy_routing_path(src_x, src_y, dst_x, dst_y)
        start_pos = self.get_router_position(src_x, src_y)

        packet = Packet(
            id=self.packet_counter,
            src_x=src_x,
            src_y=src_y,
            dst_x=dst_x,
            dst_y=dst_y,
            packet_type=packet_type,
            current_x=float(start_pos[0]),
            current_y=float(start_pos[1]),
            path=path,
            hop_index=0,
            timestamp=time.time(),
            size_flits=random.randint(1, 4),
        )

        self.packet_counter += 1
        return packet

    def update_packets(self, dt):
        """Update packet positions and handle routing"""
        speed = 100.0  # pixels per second

        packets_to_remove = []

        for packet in self.packets:
            if packet.hop_index >= len(packet.path) - 1:
                # Packet has reached destination
                packets_to_remove.append(packet)
                self.update_router_stats(packet, arrived=True)
                continue

            # Calculate target position for next hop
            next_hop = packet.path[packet.hop_index + 1]
            target_pos = self.get_router_position(next_hop[0], next_hop[1])

            # Move towards target
            dx = target_pos[0] - packet.current_x
            dy = target_pos[1] - packet.current_y
            distance = math.sqrt(dx * dx + dy * dy)

            if distance < speed * dt:
                # Reached next hop
                packet.current_x = float(target_pos[0])
                packet.current_y = float(target_pos[1])
                packet.hop_index += 1
                self.update_router_stats(packet, forwarded=True)
            else:
                # Move towards target
                packet.current_x += (dx / distance) * speed * dt
                packet.current_y += (dy / distance) * speed * dt

        # Remove arrived packets
        for packet in packets_to_remove:
            self.packets.remove(packet)

    def update_router_stats(self, packet, arrived=False, forwarded=False):
        """Update router statistics based on packet events"""
        if forwarded and packet.hop_index < len(packet.path):
            hop = packet.path[packet.hop_index]
            node_id = hop[1] * self.mesh_width + hop[0]
            if 0 <= node_id < len(self.router_stats):
                self.router_stats[node_id].packets_received += 1

        if arrived:
            dst_node_id = packet.dst_y * self.mesh_width + packet.dst_x
            if 0 <= dst_node_id < len(self.router_stats):
                self.router_stats[dst_node_id].packets_sent += 1
                latency = (time.time() - packet.timestamp) * 1000  # ms
                stats = self.router_stats[dst_node_id]
                # Simple moving average for latency
                if stats.average_latency == 0:
                    stats.average_latency = latency
                else:
                    stats.average_latency = stats.average_latency * 0.9 + latency * 0.1

    def traffic_generation_thread(self):
        """Background thread for generating traffic"""
        while self.simulation_running:
            if not self.paused and random.random() < self.injection_rate:
                packet = self.generate_packet()
                if packet:
                    self.traffic_queue.put(packet)
            time.sleep(0.1)  # 100ms interval

    def start_simulation(self):
        """Start traffic simulation"""
        if not self.simulation_running:
            self.simulation_running = True
            self.traffic_thread = threading.Thread(
                target=self.traffic_generation_thread
            )
            self.traffic_thread.daemon = True
            self.traffic_thread.start()
            print(f"Started simulation with {self.current_pattern.value} pattern")

    def stop_simulation(self):
        """Stop traffic simulation"""
        self.simulation_running = False
        if self.traffic_thread:
            self.traffic_thread.join(timeout=1.0)
        print("Stopped simulation")

    def load_vcd_file(self, filepath):
        """Load and parse VCD file from Verilog simulation"""
        success = False

        # Try with our simple parser first
        if VCD_PARSER_AVAILABLE:
            try:
                self.vcd_parser = SimpleVCDParser(filepath)
                if self.vcd_parser.parse():
                    self.vcd_file = filepath
                    self.vcd_replay_active = False
                    self.vcd_replay_time = 0
                    print(f"✅ Loaded VCD file with simple parser: {filepath}")
                    print(f"   - {len(self.vcd_parser.signals)} signals")
                    print(f"   - {len(self.vcd_parser.packet_events)} packet events")
                    print(
                        f"   - {self.vcd_parser.get_simulation_duration()} time units"
                    )
                    success = True
                else:
                    print(f"❌ Failed to parse VCD file with simple parser")
            except Exception as e:
                print(f"Error with simple VCD parser: {e}")

        # Fallback to vcdvcd if available
        if not success and VCD_AVAILABLE:
            try:
                self.vcd_data = vcdvcd.VCDVCD(filepath)
                self.vcd_file = filepath
                print(f"✅ Loaded VCD file with vcdvcd: {filepath}")
                success = True
            except Exception as e:
                print(f"Error loading VCD file with vcdvcd: {e}")

        if not success:
            print("❌ VCD parsing not available or failed")

        return success

    def run_verilog_simulation(self, pattern_name="uniform_random"):
        """Run Verilog testbench to generate traffic data"""
        try:
            # Change to code directory
            code_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
            build_dir = os.path.join(code_dir, "build")

            # First check if executable exists, if not compile it
            executable_path = os.path.join(build_dir, "obj_dir", "Vtb_nebula_top")
            if not os.path.exists(executable_path):
                print("Compiling Verilog testbench...")
                compile_cmd = ["make", "tb_nebula_top"]
                compile_process = subprocess.Popen(
                    compile_cmd,
                    cwd=code_dir,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                )

                stdout, stderr = compile_process.communicate(
                    timeout=120
                )  # 2 minutes for compilation

                if compile_process.returncode != 0:
                    print(f"Compilation failed: {stderr}")
                    return False

            # Run the simulation directly
            print("Running Verilog simulation...")
            sim_cmd = ["./obj_dir/Vtb_nebula_top"]

            self.verilog_process = subprocess.Popen(
                sim_cmd,
                cwd=build_dir,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )

            stdout, stderr = self.verilog_process.communicate(
                timeout=60
            )  # 1 minute for simulation

            if self.verilog_process.returncode == 0:
                print("Verilog simulation completed successfully")
                # Look for generated VCD file in build directory
                vcd_path = os.path.join(build_dir, "tb_nebula_top.vcd")
                if os.path.exists(vcd_path):
                    self.load_vcd_file(vcd_path)
                    return True
                else:
                    print(f"VCD file not found at {vcd_path}")
                    return False
            else:
                print(f"Verilog simulation failed: {stderr}")
                return False

        except subprocess.TimeoutExpired:
            print("Verilog simulation timed out")
            if self.verilog_process:
                self.verilog_process.kill()
            return False
        except Exception as e:
            print(f"Error running Verilog simulation: {e}")
            return False

    def draw_mesh_topology(self):
        """Draw the mesh network topology"""
        # Draw panel background
        pygame.draw.rect(self.screen, COLORS["mesh_bg"], self.mesh_panel)
        pygame.draw.rect(self.screen, COLORS["router_border"], self.mesh_panel, 2)

        # Draw links between routers
        for y in range(self.mesh_height):
            for x in range(self.mesh_width):
                pos = self.get_router_position(x, y)

                # Horizontal links
                if x < self.mesh_width - 1:
                    next_pos = self.get_router_position(x + 1, y)
                    # Check if link is active (has packets)
                    link_active = any(
                        (
                            packet.hop_index < len(packet.path) - 1
                            and (
                                (
                                    packet.path[packet.hop_index] == (x, y)
                                    and packet.path[packet.hop_index + 1] == (x + 1, y)
                                )
                                or (
                                    packet.path[packet.hop_index] == (x + 1, y)
                                    and packet.path[packet.hop_index + 1] == (x, y)
                                )
                            )
                        )
                        for packet in self.packets
                    )
                    color = (
                        COLORS["link_active"] if link_active else COLORS["link_idle"]
                    )
                    pygame.draw.line(
                        self.screen,
                        color,
                        (
                            pos[0] + self.router_size // 2,
                            pos[1] + self.router_size // 2,
                        ),
                        (
                            next_pos[0] - self.router_size // 2,
                            next_pos[1] + self.router_size // 2,
                        ),
                        3,
                    )

                # Vertical links
                if y < self.mesh_height - 1:
                    next_pos = self.get_router_position(x, y + 1)
                    link_active = any(
                        (
                            packet.hop_index < len(packet.path) - 1
                            and (
                                (
                                    packet.path[packet.hop_index] == (x, y)
                                    and packet.path[packet.hop_index + 1] == (x, y + 1)
                                )
                                or (
                                    packet.path[packet.hop_index] == (x, y + 1)
                                    and packet.path[packet.hop_index + 1] == (x, y)
                                )
                            )
                        )
                        for packet in self.packets
                    )
                    color = (
                        COLORS["link_active"] if link_active else COLORS["link_idle"]
                    )
                    pygame.draw.line(
                        self.screen,
                        color,
                        (
                            pos[0] + self.router_size // 2,
                            pos[1] + self.router_size // 2,
                        ),
                        (
                            next_pos[0] + self.router_size // 2,
                            next_pos[1] - self.router_size // 2,
                        ),
                        3,
                    )

        # Draw routers
        for y in range(self.mesh_height):
            for x in range(self.mesh_width):
                node_id = y * self.mesh_width + x
                stats = self.router_stats[node_id]
                pos = self.get_router_position(x, y)

                # Determine router color based on activity
                if stats.congestion_level > 0.7:
                    color = COLORS["router_congested"]
                elif stats.packets_received > 0 or stats.packets_sent > 0:
                    color = COLORS["router_active"]
                else:
                    color = COLORS["router_idle"]

                # Draw router
                router_rect = pygame.Rect(
                    pos[0] - self.router_size // 2,
                    pos[1] - self.router_size // 2,
                    self.router_size,
                    self.router_size,
                )
                pygame.draw.rect(self.screen, color, router_rect)
                pygame.draw.rect(self.screen, COLORS["router_border"], router_rect, 2)

                # Draw router ID
                text = self.font_small.render(f"{node_id}", True, COLORS["text"])
                text_rect = text.get_rect(center=(pos[0], pos[1] - 8))
                self.screen.blit(text, text_rect)

                # Draw coordinates
                coord_text = self.font_small.render(
                    f"({x},{y})", True, COLORS["text_dim"]
                )
                coord_rect = coord_text.get_rect(center=(pos[0], pos[1] + 8))
                self.screen.blit(coord_text, coord_rect)

    def draw_packets(self):
        """Draw packets moving through the network"""
        for packet in self.packets:
            # Packet color based on type
            color_map = {
                PacketType.REQ: COLORS["packet_req"],
                PacketType.RSP: COLORS["packet_resp"],
                PacketType.SNP: COLORS["packet_snoop"],
                PacketType.DAT: COLORS["packet_data"],
                PacketType.AXI_AR: COLORS["packet_req"],
                PacketType.AXI_AW: COLORS["packet_req"],
                PacketType.AXI_W: COLORS["packet_data"],
                PacketType.AXI_R: COLORS["packet_data"],
                PacketType.AXI_B: COLORS["packet_resp"],
            }

            color = color_map.get(packet.packet_type, COLORS["text"])

            # Draw packet as circle with size based on flit count
            radius = 4 + packet.size_flits * 2
            pygame.draw.circle(
                self.screen,
                color,
                (int(packet.current_x), int(packet.current_y)),
                radius,
            )
            pygame.draw.circle(
                self.screen,
                COLORS["text"],
                (int(packet.current_x), int(packet.current_y)),
                radius,
                1,
            )

            # Draw packet ID
            if radius > 6:
                id_text = self.font_small.render(str(packet.id), True, COLORS["text"])
                id_rect = id_text.get_rect(
                    center=(int(packet.current_x), int(packet.current_y))
                )
                self.screen.blit(id_text, id_rect)

    def draw_controls(self):
        """Draw control panel"""
        pygame.draw.rect(self.screen, COLORS["panel_bg"], self.control_panel)
        pygame.draw.rect(self.screen, COLORS["router_border"], self.control_panel, 2)

        y_offset = self.control_panel.y + 10

        # Title
        title = self.font_medium.render("SIMULATION CONTROLS", True, COLORS["text"])
        self.screen.blit(title, (self.control_panel.x + 10, y_offset))
        y_offset += 35

        # Simulation status
        status_text = "RUNNING" if self.simulation_running else "STOPPED"
        status_color = (
            COLORS["performance_good"]
            if self.simulation_running
            else COLORS["performance_bad"]
        )
        status = self.font_small.render(f"Status: {status_text}", True, status_color)
        self.screen.blit(status, (self.control_panel.x + 10, y_offset))
        y_offset += 25

        # Pause status
        if self.simulation_running:
            pause_text = "PAUSED" if self.paused else "ACTIVE"
            pause_color = (
                COLORS["performance_medium"]
                if self.paused
                else COLORS["performance_good"]
            )
            pause = self.font_small.render(f"Mode: {pause_text}", True, pause_color)
            self.screen.blit(pause, (self.control_panel.x + 10, y_offset))
        y_offset += 25

        # Traffic pattern
        pattern_text = self.font_small.render(
            f"Pattern: {self.current_pattern.value}", True, COLORS["text"]
        )
        self.screen.blit(pattern_text, (self.control_panel.x + 10, y_offset))
        y_offset += 20

        # Injection rate
        rate_text = self.font_small.render(
            f"Injection Rate: {self.injection_rate:.2f}", True, COLORS["text"]
        )
        self.screen.blit(rate_text, (self.control_panel.x + 10, y_offset))
        y_offset += 30

        # Active packets
        active_packets = len(self.packets)
        packet_text = self.font_small.render(
            f"Active Packets: {active_packets}", True, COLORS["text"]
        )
        self.screen.blit(packet_text, (self.control_panel.x + 10, y_offset))
        y_offset += 20

        # Total packets generated
        total_text = self.font_small.render(
            f"Total Generated: {self.packet_counter}", True, COLORS["text"]
        )
        self.screen.blit(total_text, (self.control_panel.x + 10, y_offset))
        y_offset += 30

        # Control instructions
        instructions = [
            "SPACE - Start/Stop",
            "P - Pause/Resume",
            "1-4 - Traffic Patterns",
            "V - Run Verilog Sim",
            "R - Reset Stats",
            "+/- - Injection Rate",
        ]

        for instruction in instructions:
            inst_text = self.font_small.render(instruction, True, COLORS["text_dim"])
            self.screen.blit(inst_text, (self.control_panel.x + 10, y_offset))
            y_offset += 15

    def draw_statistics(self):
        """Draw router statistics panel"""
        pygame.draw.rect(self.screen, COLORS["panel_bg"], self.stats_panel)
        pygame.draw.rect(self.screen, COLORS["router_border"], self.stats_panel, 2)

        y_offset = self.stats_panel.y + 10

        # Title
        title = self.font_medium.render("ROUTER STATISTICS", True, COLORS["text"])
        self.screen.blit(title, (self.stats_panel.x + 10, y_offset))
        y_offset += 35

        # Calculate overall stats
        total_received = sum(stats.packets_received for stats in self.router_stats)
        total_sent = sum(stats.packets_sent for stats in self.router_stats)
        avg_latency = (
            np.mean(
                [
                    stats.average_latency
                    for stats in self.router_stats
                    if stats.average_latency > 0
                ]
            )
            if any(stats.average_latency > 0 for stats in self.router_stats)
            else 0
        )

        # Overall statistics
        stats_text = [
            f"Total Packets Received: {total_received}",
            f"Total Packets Sent: {total_sent}",
            f"Average Latency: {avg_latency:.1f}ms",
            "",
            "Per-Router Stats:",
        ]

        for text in stats_text:
            if text:
                stat_text = self.font_small.render(text, True, COLORS["text"])
                self.screen.blit(stat_text, (self.stats_panel.x + 10, y_offset))
            y_offset += 15

        # Individual router stats (show top 4 most active)
        active_routers = sorted(
            self.router_stats,
            key=lambda r: r.packets_received + r.packets_sent,
            reverse=True,
        )[:4]

        for router in active_routers:
            if router.packets_received + router.packets_sent > 0:
                router_text = f"R{router.node_id}: {router.packets_received}↓ {router.packets_sent}↑"
                if router.average_latency > 0:
                    router_text += f" {router.average_latency:.1f}ms"

                stat_text = self.font_small.render(
                    router_text, True, COLORS["text_dim"]
                )
                self.screen.blit(stat_text, (self.stats_panel.x + 10, y_offset))
                y_offset += 15

    def draw_performance_graphs(self):
        """Draw performance monitoring graphs"""
        pygame.draw.rect(self.screen, COLORS["panel_bg"], self.performance_panel)
        pygame.draw.rect(
            self.screen, COLORS["router_border"], self.performance_panel, 2
        )

        # Title
        title = self.font_medium.render("PERFORMANCE MONITORING", True, COLORS["text"])
        self.screen.blit(
            title, (self.performance_panel.x + 10, self.performance_panel.y + 10)
        )

        # Update performance history
        current_time = time.time()
        if current_time - self.last_stats_update > 1.0:  # Update every second
            total_packets = len(self.packets)
            avg_latency = (
                np.mean(
                    [
                        stats.average_latency
                        for stats in self.router_stats
                        if stats.average_latency > 0
                    ]
                )
                if any(stats.average_latency > 0 for stats in self.router_stats)
                else 0
            )

            self.performance_history.append(
                {
                    "time": current_time,
                    "active_packets": total_packets,
                    "avg_latency": avg_latency,
                    "injection_rate": self.injection_rate,
                }
            )

            if len(self.performance_history) > self.max_history_length:
                self.performance_history.pop(0)

            self.last_stats_update = current_time

        # Draw graphs if we have data
        if len(self.performance_history) > 1:
            graph_width = self.performance_panel.width - 40
            graph_height = 180
            graph_x = self.performance_panel.x + 20

            # Active packets graph
            graph_y = self.performance_panel.y + 50
            self.draw_line_graph(
                graph_x,
                graph_y,
                graph_width,
                graph_height,
                [p["active_packets"] for p in self.performance_history],
                "Active Packets",
                COLORS["packet_req"],
            )

            # Latency graph
            graph_y += graph_height + 30
            self.draw_line_graph(
                graph_x,
                graph_y,
                graph_width,
                graph_height,
                [p["avg_latency"] for p in self.performance_history],
                "Average Latency (ms)",
                COLORS["packet_resp"],
            )

            # Network utilization heatmap
            heatmap_y = graph_y + graph_height + 30
            self.draw_network_heatmap(graph_x, heatmap_y, 240, 120)

    def draw_line_graph(self, x, y, width, height, data, title, color):
        """Draw a line graph"""
        # Graph background
        graph_rect = pygame.Rect(x, y, width, height)
        pygame.draw.rect(self.screen, COLORS["mesh_bg"], graph_rect)
        pygame.draw.rect(self.screen, COLORS["grid_line"], graph_rect, 1)

        # Title
        title_text = self.font_small.render(title, True, COLORS["text"])
        self.screen.blit(title_text, (x, y - 15))

        if len(data) < 2:
            return

        # Scale data
        max_val = max(data) if max(data) > 0 else 1
        min_val = min(data)
        val_range = max_val - min_val if max_val != min_val else 1

        # Draw grid lines
        for i in range(5):
            grid_y = y + (height * i) // 4
            pygame.draw.line(
                self.screen, COLORS["grid_line"], (x, grid_y), (x + width, grid_y)
            )

        # Draw data points
        points = []
        for i, value in enumerate(data):
            point_x = x + (width * i) // (len(data) - 1)
            point_y = y + height - int((value - min_val) / val_range * height)
            points.append((point_x, point_y))

        if len(points) > 1:
            pygame.draw.lines(self.screen, color, False, points, 2)

        # Draw current value
        if data:
            current_val = data[-1]
            val_text = self.font_small.render(f"{current_val:.1f}", True, color)
            self.screen.blit(val_text, (x + width - 50, y + 5))

    def draw_network_heatmap(self, x, y, width, height):
        """Draw network utilization heatmap"""
        # Title
        title_text = self.font_small.render("Network Utilization", True, COLORS["text"])
        self.screen.blit(title_text, (x, y - 15))

        cell_width = width // self.mesh_width
        cell_height = height // self.mesh_height

        # Calculate max utilization for scaling
        max_util = max(
            stats.packets_received + stats.packets_sent for stats in self.router_stats
        )
        if max_util == 0:
            max_util = 1

        for router in self.router_stats:
            utilization = (router.packets_received + router.packets_sent) / max_util

            # Color based on utilization
            if utilization > 0.7:
                color = COLORS["performance_bad"]
            elif utilization > 0.3:
                color = COLORS["performance_medium"]
            elif utilization > 0:
                color = COLORS["performance_good"]
            else:
                color = COLORS["router_idle"]

            # Blend with background based on utilization level
            alpha = min(255, int(utilization * 255 + 50))

            cell_x = x + router.x * cell_width
            cell_y = y + router.y * cell_height
            cell_rect = pygame.Rect(cell_x, cell_y, cell_width - 1, cell_height - 1)

            # Create surface for alpha blending
            cell_surface = pygame.Surface((cell_width - 1, cell_height - 1))
            cell_surface.fill(color)
            cell_surface.set_alpha(alpha)

            self.screen.blit(cell_surface, (cell_x, cell_y))
            pygame.draw.rect(self.screen, COLORS["router_border"], cell_rect, 1)

            # Draw router ID
            id_text = self.font_small.render(str(router.node_id), True, COLORS["text"])
            id_rect = id_text.get_rect(
                center=(cell_x + cell_width // 2, cell_y + cell_height // 2)
            )
            self.screen.blit(id_text, id_rect)

    def handle_input(self, event):
        """Handle keyboard and mouse input"""
        if event.type == pygame.KEYDOWN:
            if event.key == pygame.K_SPACE:
                # Toggle simulation
                if self.simulation_running:
                    self.stop_simulation()
                else:
                    self.start_simulation()

            elif event.key == pygame.K_p:
                # Toggle pause
                self.paused = not self.paused
                print(f"Simulation {'paused' if self.paused else 'resumed'}")

            elif event.key == pygame.K_1:
                self.current_pattern = TrafficPattern.UNIFORM_RANDOM
                print(f"Switched to {self.current_pattern.value} pattern")

            elif event.key == pygame.K_2:
                self.current_pattern = TrafficPattern.HOTSPOT
                print(f"Switched to {self.current_pattern.value} pattern")

            elif event.key == pygame.K_3:
                self.current_pattern = TrafficPattern.TRANSPOSE
                print(f"Switched to {self.current_pattern.value} pattern")

            elif event.key == pygame.K_4:
                self.current_pattern = TrafficPattern.GPU_WORKLOAD
                print(f"Switched to {self.current_pattern.value} pattern")

            elif event.key == pygame.K_v:
                # Run Verilog simulation
                print("Running Verilog simulation...")
                if self.run_verilog_simulation():
                    print("Verilog simulation completed")
                else:
                    print("Verilog simulation failed")

            elif event.key == pygame.K_r:
                # Reset statistics
                for stats in self.router_stats:
                    stats.packets_received = 0
                    stats.packets_sent = 0
                    stats.average_latency = 0.0
                    stats.congestion_level = 0.0
                self.packets.clear()
                self.packet_counter = 0
                self.performance_history.clear()
                print("Statistics reset")

            elif event.key == pygame.K_PLUS or event.key == pygame.K_EQUALS:
                # Increase injection rate
                self.injection_rate = min(1.0, self.injection_rate + 0.05)
                print(f"Injection rate: {self.injection_rate:.2f}")

            elif event.key == pygame.K_MINUS:
                # Decrease injection rate
                self.injection_rate = max(0.0, self.injection_rate - 0.05)
                print(f"Injection rate: {self.injection_rate:.2f}")

            elif event.key == pygame.K_l:
                # Load VCD file (look for recent one)
                vcd_paths = [
                    "../build/tb_nebula_top.vcd",
                    "../build/obj_dir/tb_nebula_top.vcd",
                    "../build/nebula_mesh_integration_tb.vcd",
                    "../build/nebula_router_tb.vcd",
                ]

                loaded = False
                for vcd_path in vcd_paths:
                    if os.path.exists(vcd_path):
                        if self.load_vcd_file(vcd_path):
                            loaded = True
                            break

                if not loaded:
                    print("No VCD files found or loading failed")

            elif event.key == pygame.K_t:
                # Toggle VCD replay
                if self.vcd_parser:
                    self.vcd_replay_active = not self.vcd_replay_active
                    if self.vcd_replay_active:
                        print("VCD replay started")
                    else:
                        print("VCD replay paused")
                else:
                    print("No VCD file loaded")

            elif event.key == pygame.K_UP:
                # Increase VCD replay speed
                if self.vcd_parser:
                    self.vcd_replay_speed = min(10.0, self.vcd_replay_speed * 1.5)
                    print(f"VCD replay speed: {self.vcd_replay_speed:.1f}x")

            elif event.key == pygame.K_DOWN:
                # Decrease VCD replay speed
                if self.vcd_parser:
                    self.vcd_replay_speed = max(0.1, self.vcd_replay_speed / 1.5)
                    print(f"VCD replay speed: {self.vcd_replay_speed:.1f}x")

            elif event.key == pygame.K_0:
                # Reset VCD replay
                if self.vcd_parser:
                    self.vcd_replay_time = 0
                    print("VCD replay reset to start")

    def update(self, dt):
        """Main update loop"""
        # Process new packets from traffic generation thread
        try:
            while True:
                packet = self.traffic_queue.get_nowait()
                self.packets.append(packet)
        except queue.Empty:
            pass

        # Update VCD replay if active
        if self.vcd_replay_active and self.vcd_parser:
            self.update_vcd_replay(dt)

        # Update packet positions
        if not self.paused:
            self.update_packets(dt)

        # Update router congestion levels based on local packet density
        for stats in self.router_stats:
            local_packets = sum(
                1
                for packet in self.packets
                if abs(packet.current_x - self.get_router_position(stats.x, stats.y)[0])
                < 30
                and abs(
                    packet.current_y - self.get_router_position(stats.x, stats.y)[1]
                )
                < 30
            )
            stats.congestion_level = min(1.0, local_packets / 5.0)  # Normalize to 0-1

    def update_vcd_replay(self, dt):
        """Update VCD replay state and inject packets based on trace"""
        if not self.vcd_parser or not self.vcd_replay_active:
            return

        # Advance replay time
        time_increment = (
            dt * self.vcd_replay_speed * 1000
        )  # Convert to simulation time units
        self.vcd_replay_time += time_increment

        # Get packet events within current time window
        current_events = [
            event
            for event in self.vcd_parser.packet_events
            if event.timestamp <= self.vcd_replay_time
            and event.timestamp > (self.vcd_replay_time - time_increment)
        ]

        # Process events and create visualization packets
        for event in current_events:
            if event.event_type == "inject":
                # Create a new packet for visualization
                router_x = event.router_id % self.mesh_width
                router_y = event.router_id // self.mesh_width

                # Generate destination for visualization (random if not in trace)
                dst_x = random.randint(0, self.mesh_width - 1)
                dst_y = random.randint(0, self.mesh_height - 1)

                # Get router position for initial packet placement
                router_pos = self.get_router_position(router_x, router_y)

                packet = Packet(
                    id=event.packet_id,
                    src_x=router_x,
                    src_y=router_y,
                    dst_x=dst_x,
                    dst_y=dst_y,
                    packet_type=random.choice(list(PacketType)),
                    current_x=router_pos[0],
                    current_y=router_pos[1],
                    path=[],
                    hop_index=0,
                    timestamp=time.time(),
                    size_flits=1,
                )

                self.packets.append(packet)

                # Update router stats
                self.update_router_stats(packet, arrived=False, forwarded=False)

        # Check if replay has reached the end
        max_time = self.vcd_parser.get_simulation_duration()
        if max_time > 0 and self.vcd_replay_time >= max_time:
            self.vcd_replay_time = 0  # Loop back to start
            print("VCD replay completed, restarting...")

    def get_vcd_status_text(self):
        """Get VCD status text for display"""
        if not self.vcd_parser:
            return "No VCD loaded (L to load)"

        status = "VCD: "
        if self.vcd_replay_active:
            progress = 0
            max_time = self.vcd_parser.get_simulation_duration()
            if max_time > 0:
                progress = (self.vcd_replay_time / max_time) * 100
            status += f"Playing {progress:.1f}% (Speed: {self.vcd_replay_speed:.1f}x)"
        else:
            status += (
                f"Loaded ({len(self.vcd_parser.packet_events)} events) - T to play"
            )

        return status

    def draw(self):
        """Main drawing function"""
        self.screen.fill(COLORS["background"])

        # Draw main title
        title = self.font_large.render(
            "Nebula GPU Interconnect System Dashboard", True, COLORS["text"]
        )
        title_rect = title.get_rect(center=(WINDOW_WIDTH // 2, 30))
        self.screen.blit(title, title_rect)

        # Draw subtitle with current status
        vcd_status = self.get_vcd_status_text()
        subtitle_text = f"Real-time NoC Visualization • Pattern: {self.current_pattern.value} • Rate: {self.injection_rate:.2f} • {vcd_status}"
        subtitle = self.font_small.render(subtitle_text, True, COLORS["text_dim"])
        subtitle_rect = subtitle.get_rect(center=(WINDOW_WIDTH // 2, 55))
        self.screen.blit(subtitle, subtitle_rect)

        # Draw all panels
        self.draw_mesh_topology()
        self.draw_packets()
        self.draw_controls()
        self.draw_statistics()
        self.draw_performance_graphs()

        # Draw legend
        self.draw_legend()

        pygame.display.flip()

    def draw_legend(self):
        """Draw packet type legend"""
        legend_x = 20
        legend_y = WINDOW_HEIGHT - 100

        legend_title = self.font_small.render("Packet Types:", True, COLORS["text"])
        self.screen.blit(legend_title, (legend_x, legend_y))

        legend_items = [
            ("REQ", COLORS["packet_req"]),
            ("RSP", COLORS["packet_resp"]),
            ("SNP", COLORS["packet_snoop"]),
            ("DAT", COLORS["packet_data"]),
        ]

        for i, (name, color) in enumerate(legend_items):
            item_x = legend_x + i * 80
            item_y = legend_y + 20

            pygame.draw.circle(self.screen, color, (item_x + 8, item_y + 8), 6)
            pygame.draw.circle(
                self.screen, COLORS["text"], (item_x + 8, item_y + 8), 6, 1
            )

            name_text = self.font_small.render(name, True, COLORS["text_dim"])
            self.screen.blit(name_text, (item_x + 20, item_y))

    def run(self):
        """Main application loop"""
        print("Starting Nebula Dashboard...")
        print("Controls:")
        print("  SPACE - Start/Stop simulation")
        print("  P - Pause/Resume")
        print("  1-4 - Change traffic patterns")
        print("  V - Run Verilog simulation")
        print("  R - Reset statistics")
        print("  +/- - Adjust injection rate")
        print("  L - Load VCD file")
        print("  T - Toggle VCD replay")
        print("  UP/DOWN - VCD replay speed")
        print("  0 - Reset VCD replay")

        while self.running:
            dt = self.clock.tick(FPS) / 1000.0  # Delta time in seconds

            # Handle events
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.running = False
                else:
                    self.handle_input(event)

            # Update and draw
            self.update(dt)
            self.draw()

        # Cleanup
        self.stop_simulation()
        pygame.quit()


if __name__ == "__main__":
    dashboard = NebulaDashboard()
    dashboard.run()
