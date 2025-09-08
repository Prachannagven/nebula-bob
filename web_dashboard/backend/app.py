#!/usr/bin/env python3
"""
Nebula GPU Interconnect Dashboard - Flask Backend

A minimal Flask API backend for testing and visualizing
the Nebula NoC system using real Verilog simulations.
"""

import os
import sys
import time
import json
import threading
import subprocess
from dataclasses import dataclass, asdict
from typing import List, Dict, Tuple, Optional
import logging

from flask import Flask, jsonify, request, send_from_directory
from flask_cors import CORS
from flask_socketio import SocketIO, emit

# Add the project paths
project_root = os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
)
sys.path.insert(0, os.path.join(project_root, "code", "python"))

# Import our traffic generators
try:
    from nebula_traffic_generator import (
        NebulaTrafficGenerator,
        TrafficConfig,
        TrafficPattern,
    )
    from nebula_vcd_parser import SimpleVCDParser, PacketEvent

    TRAFFIC_AVAILABLE = True
except ImportError as e:
    print(f"Traffic modules not available: {e}")
    TRAFFIC_AVAILABLE = False

# Set up logging with minimal terminal output
log_dir = os.path.join(os.path.dirname(__file__), "logs")
os.makedirs(log_dir, exist_ok=True)

# Configure main logger - file only for detailed logs
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    handlers=[logging.FileHandler(os.path.join(log_dir, "dashboard.log"))],
)
logger = logging.getLogger(__name__)

# Configure Flask's werkzeug logger to be quiet
werkzeug_logger = logging.getLogger("werkzeug")
werkzeug_logger.setLevel(logging.ERROR)

# Create a separate logger for API calls
api_logger = logging.getLogger("api_calls")
api_logger.setLevel(logging.INFO)
api_handler = logging.FileHandler(os.path.join(log_dir, "api_calls.log"))
api_handler.setFormatter(logging.Formatter("%(asctime)s - %(message)s"))
api_logger.addHandler(api_handler)
api_logger.propagate = False

# Create a separate logger for Verilog compilation
verilog_logger = logging.getLogger("verilog_compilation")
verilog_logger.setLevel(logging.INFO)
verilog_handler = logging.FileHandler(os.path.join(log_dir, "verilog_compilation.log"))
verilog_handler.setFormatter(logging.Formatter("%(asctime)s - %(message)s"))
verilog_logger.addHandler(verilog_handler)
verilog_logger.propagate = False

app = Flask(__name__)
app.config["SECRET_KEY"] = "nebula-dashboard-secret"
CORS(app)
socketio = SocketIO(app, cors_allowed_origins="*", logger=False, engineio_logger=False)


# Dashboard state
class DashboardState:
    def __init__(self):
        self.mesh_width = 4
        self.mesh_height = 4
        self.simulation_running = False
        self.simulation_status = "idle"
        self.simulation_progress = 0
        self.simulation_start_time = None
        self.simulation_log = []
        self.vcd_events = []
        self.vcd_replay_index = 0
        self.last_vcd_file = None
        self.router_stats = {}
        self.packets = []
        self.performance_history = []
        self.verilog_process = None
        self.last_simulation_error = None
        # Initialize additional state variables
        self.simulation_time = 0
        self.workload_data = []
        self.vcd_replay_active = False
        self.vcd_replay_speed = 1.0  # Events per update
        self.next_packet_id = 0  # Ensure unique packet IDs
        # Performance tracking
        self.total_packets_generated = 0
        self.total_packets_completed = 0
        self.packet_latencies = []  # Store latency values for averaging
        # Initialize router statistics
        self._initialize_router_stats()

    def _initialize_router_stats(self):
        """Initialize router statistics for the mesh"""
        for i in range(self.mesh_width * self.mesh_height):
            self.router_stats[i] = {
                "id": i,
                "x": i % self.mesh_width,
                "y": i // self.mesh_width,
                "status": "idle",
                "packets_sent": 0,
                "packets_received": 0,
                "utilization": 0.0,
                "buffer_occupancy": 0.0,
                "congestion_level": 0.0,
                "temperature": 25.0,
                "bytes_processed": 0,
            }

    def convert_vcd_to_workload(self):
        """Convert VCD events to workload data format for visualization"""
        if not self.vcd_events:
            return

        self.workload_data = []
        for event in self.vcd_events:
            # Convert VCD event to workload event format
            workload_event = {
                "timestamp": int(event.timestamp // 10),  # Scale down time
                "src_x": event.src_x,
                "src_y": event.src_y,
                "dst_x": event.dst_x,
                "dst_y": event.dst_y,
                "packet_type": getattr(event, "packet_type", "DATA"),
                "size_bytes": getattr(event, "size_bytes", 64),
                "priority": getattr(event, "priority", 0),
            }
            self.workload_data.append(workload_event)

        logger.info(f"Converted {len(self.workload_data)} VCD events to workload data")

    def update_simulation_from_vcd(self):
        """Update simulation state from VCD data"""
        if not self.vcd_events or self.vcd_replay_index >= len(self.vcd_events):
            return

        # Process VCD events for current time step
        # Process a consistent number of events per logical simulation step
        # This ensures packet counts are accurate regardless of playback speed
        events_processed = 0
        max_events_per_update = 3  # Fixed number for consistent simulation state

        while (
            self.vcd_replay_index < len(self.vcd_events)
            and events_processed < max_events_per_update
        ):

            event = self.vcd_events[self.vcd_replay_index]

            # Extract source and destination coordinates
            # Check if we have router_id to convert to x,y coordinates
            if hasattr(event, "router_id") and (
                event.src_x == 0
                and event.src_y == 0
                and event.dst_x == 0
                and event.dst_y == 0
            ):
                # Convert router_id to x,y coordinates
                src_x = getattr(event, "router_id", 0) % self.mesh_width
                src_y = getattr(event, "router_id", 0) // self.mesh_width
                # For now, generate random destination within mesh bounds
                import random

                dst_x = random.randint(0, self.mesh_width - 1)
                dst_y = random.randint(0, self.mesh_height - 1)
            else:
                src_x = event.src_x
                src_y = event.src_y
                dst_x = event.dst_x
                dst_y = event.dst_y

            # Ensure coordinates are within mesh bounds
            src_x = max(0, min(src_x, self.mesh_width - 1))
            src_y = max(0, min(src_y, self.mesh_height - 1))
            dst_x = max(0, min(dst_x, self.mesh_width - 1))
            dst_y = max(0, min(dst_y, self.mesh_height - 1))

            # Debug: Log event details for first few events
            if self.vcd_replay_index < 5:
                logger.info(
                    f"Processing VCD event {self.vcd_replay_index}: src=({src_x},{src_y}) dst=({dst_x},{dst_y}) router_id={getattr(event, 'router_id', 'N/A')}"
                )

            # Skip if source and destination are the same (no movement needed)
            if src_x == dst_x and src_y == dst_y:
                self.vcd_replay_index += 1
                events_processed += 1
                continue

            # Convert VCD event to packet
            path = self._calculate_xy_route(src_x, src_y, dst_x, dst_y)
            # Convert path from list of tuples to list of dicts for frontend compatibility
            path_objects = [{"x": x, "y": y} for x, y in path]

            packet = {
                "id": self.next_packet_id,
                "src_x": src_x,
                "src_y": src_y,
                "dst_x": dst_x,
                "dst_y": dst_y,
                "current_x": float(src_x),
                "current_y": float(src_y),
                "path": path_objects,
                "hop_index": 0,
                "packet_type": getattr(event, "packet_type", "DATA"),
                "size_bytes": getattr(event, "size_bytes", 64),
                "timestamp": float(event.timestamp),
                "priority": getattr(event, "priority", 0),
                "status": "routing",
                "created_time": time.time(),  # For latency calculation
                "start_timestamp": float(event.timestamp),  # VCD start time
            }

            self.packets.append(packet)
            self.next_packet_id += 1
            self.total_packets_generated += 1
            self.vcd_replay_index += 1
            events_processed += 1

        # Update existing packets
        self._update_packet_positions()

        # Remove completed packets after a delay for visualization
        current_time = time.time()
        packets_to_remove = []
        for i, packet in enumerate(self.packets):
            if packet["status"] == "delivered":
                # Add delivery timestamp if not present
                if "delivered_time" not in packet:
                    packet["delivered_time"] = current_time
                # Remove after 2 seconds for user to see delivery
                elif current_time - packet["delivered_time"] > 2.0:
                    packets_to_remove.append(i)
            elif packet["hop_index"] >= len(packet["path"]):
                # Fallback: remove packets that completed their path
                packets_to_remove.append(i)

        # Remove packets in reverse order to maintain indices
        for i in reversed(packets_to_remove):
            self.packets.pop(i)

        # Limit number of packets for performance
        if len(self.packets) > 50:  # MAX_PACKETS
            self.packets = self.packets[-50:]

        # Update router statistics
        self._update_router_statistics()

        # Record performance metrics
        self._record_performance_metrics()

        self.simulation_time += 1

    def _calculate_xy_route(
        self, src_x: int, src_y: int, dst_x: int, dst_y: int
    ) -> List[Tuple[int, int]]:
        """Calculate XY routing path"""
        path = [(src_x, src_y)]

        # Move in X direction first
        current_x, current_y = src_x, src_y
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

    def _update_packet_positions(self):
        """Update positions of all packets"""
        for packet in self.packets:
            if packet["hop_index"] < len(packet["path"]) - 1:
                # Move towards next hop
                next_hop = packet["path"][packet["hop_index"] + 1]
                target_x, target_y = next_hop["x"], next_hop["y"]

                # Smooth movement
                speed = 0.3  # Increased speed for better animation
                dx = target_x - packet["current_x"]
                dy = target_y - packet["current_y"]

                if abs(dx) < speed and abs(dy) < speed:
                    # Reached next hop
                    packet["current_x"] = float(target_x)
                    packet["current_y"] = float(target_y)
                    packet["hop_index"] += 1

                    # Check if packet reached destination
                    if packet["hop_index"] >= len(packet["path"]) - 1:
                        packet["status"] = "delivered"
                        packet["completed_time"] = time.time()
                        self.total_packets_completed += 1

                        # Calculate latency (time from creation to completion)
                        if "created_time" in packet:
                            latency = packet["completed_time"] - packet["created_time"]
                            self.packet_latencies.append(latency)
                            # Keep only recent latencies for averaging
                            if len(self.packet_latencies) > 100:
                                self.packet_latencies = self.packet_latencies[-100:]

                        # Update destination router stats
                        router_id = packet["dst_y"] * self.mesh_width + packet["dst_x"]
                        if router_id in self.router_stats:
                            self.router_stats[router_id]["packets_received"] += 1
                else:
                    # Move towards target
                    packet["current_x"] += dx * speed
                    packet["current_y"] += dy * speed

    def _update_router_statistics(self):
        """Update router statistics based on current packets"""
        # Reset utilization
        for stats in self.router_stats.values():
            stats["utilization"] = 0.0
            stats["congestion_level"] = 0.0

        # Count packets at each router
        router_packet_count = {}
        for packet in self.packets:
            router_x = int(round(packet["current_x"]))
            router_y = int(round(packet["current_y"]))
            router_id = router_y * self.mesh_width + router_x

            if 0 <= router_id < len(self.router_stats):
                router_packet_count[router_id] = (
                    router_packet_count.get(router_id, 0) + 1
                )

        # Update statistics
        for router_id, count in router_packet_count.items():
            if router_id in self.router_stats:
                stats = self.router_stats[router_id]
                stats["utilization"] = min(1.0, count / 5.0)  # Normalize to 0-1
                stats["congestion_level"] = min(1.0, count / 3.0)
                stats["temperature"] = 25.0 + stats["utilization"] * 15.0  # 25-40°C
                stats["buffer_occupancy"] = stats["utilization"] * 0.8

    def _record_performance_metrics(self):
        """Record performance metrics for history"""
        active_packets = len(
            [p for p in self.packets if p.get("status", "routing") == "routing"]
        )

        if self.router_stats:
            avg_utilization = sum(
                [stats["utilization"] for stats in self.router_stats.values()]
            ) / len(self.router_stats)
            max_congestion = max(
                [stats["congestion_level"] for stats in self.router_stats.values()]
            )
        else:
            avg_utilization = 0.0
            max_congestion = 0.0

        # Calculate current throughput (packets per minute)
        current_throughput = 0.0
        if len(self.performance_history) > 0:
            # Calculate throughput based on change in completed packets
            time_diff = 1.0  # 1 second between updates
            prev_completed = self.performance_history[-1].get("completed_packets", 0)
            current_completed = self.total_packets_completed
            if time_diff > 0:
                current_throughput = (
                    (current_completed - prev_completed) / time_diff * 60
                )  # per minute

        self.performance_history.append(
            {
                "time": self.simulation_time,
                "total_packets": self.total_packets_generated,
                "active_packets": active_packets,
                "completed_packets": self.total_packets_completed,
                "avg_utilization": avg_utilization,
                "max_congestion": max_congestion,
                "throughput": current_throughput,
                "avg_latency": (
                    sum(self.packet_latencies) / len(self.packet_latencies) * 1000
                    if self.packet_latencies
                    else 0.0
                ),
                "timestamp": time.time(),
            }
        )

        # Keep only last 100 points for performance
        if len(self.performance_history) > 100:
            self.performance_history = self.performance_history[-100:]


state = DashboardState()


@dataclass
class Router:
    id: int
    x: int
    y: int
    status: str = "idle"
    packets_sent: int = 0
    packets_received: int = 0
    utilization: float = 0.0
    buffer_occupancy: float = 0.0


@dataclass
class Packet:
    id: int
    src_x: int
    src_y: int
    dst_x: int
    dst_y: int
    status: str = "routing"
    hop_count: int = 0
    timestamp: float = 0.0
    path: List[Tuple[int, int]] = None

    def __post_init__(self):
        if self.path is None:
            self.path = []


def get_status_data():
    """Generate status data for the dashboard"""
    return {
        "simulation_running": state.simulation_running,
        "simulation_status": state.simulation_status,
        "simulation_progress": state.simulation_progress,
        "simulation_start_time": state.simulation_start_time,
        "last_simulation_error": state.last_simulation_error,
        "mesh_width": state.mesh_width,
        "mesh_height": state.mesh_height,
        "total_packets": len(state.packets),
        "active_packets": len(
            [p for p in state.packets if p.get("status", "routing") == "routing"]
        ),
        "completed_packets": len(
            [p for p in state.packets if p.get("status") == "delivered"]
        ),
        "vcd_events_count": len(state.vcd_events),
        "vcd_replay_index": state.vcd_replay_index,
        "vcd_replay_active": state.vcd_replay_active,
        "vcd_replay_speed": state.vcd_replay_speed,
        "simulation_time": state.simulation_time,
        "last_vcd_file": state.last_vcd_file,
        "performance_history_length": len(state.performance_history),
    }


@app.route("/")
def serve_frontend():
    """Serve the frontend"""
    frontend_dir = os.path.join(os.path.dirname(__file__), "..", "frontend", "dist")
    return send_from_directory(frontend_dir, "index.html")


@app.route("/<path:path>")
def serve_static_files(path):
    """Serve static files from the frontend dist directory"""
    frontend_dir = os.path.join(os.path.dirname(__file__), "..", "frontend", "dist")
    return send_from_directory(frontend_dir, path)


@app.route("/api/status")
def get_status():
    """Get current dashboard status"""
    api_logger.info(f"Status request from {request.remote_addr}")
    return jsonify(get_status_data())


@app.route("/api/mesh")
def get_mesh_data():
    """Get current mesh topology and packet data"""
    api_logger.info(f"Mesh data request from {request.remote_addr}")
    return jsonify(
        {
            "routers": list(state.router_stats.values()),
            "packets": state.packets,  # Already in dict format now
            "mesh_width": state.mesh_width,
            "mesh_height": state.mesh_height,
            "simulation_time": state.simulation_time,
            "vcd_replay_active": state.vcd_replay_active,
        }
    )


@app.route("/api/performance")
def get_performance_data():
    """Get performance metrics"""
    api_logger.info(f"Performance data request from {request.remote_addr}")

    # Current active packets in the system
    active_packets = len(
        [p for p in state.packets if p.get("status", "routing") == "routing"]
    )
    # Delivered packets still visible in the system (with delivery delay)
    delivered_packets_visible = len(
        [p for p in state.packets if p.get("status") == "delivered"]
    )

    # Calculate average latency from recent measurements
    avg_latency = 0.0
    if state.packet_latencies:
        avg_latency = (
            sum(state.packet_latencies) / len(state.packet_latencies) * 1000
        )  # Convert to ms

    # Calculate throughput (packets completed per second)
    throughput = 0.0
    if state.simulation_start_time:
        elapsed = time.time() - state.simulation_start_time
        if elapsed > 0:
            throughput = state.total_packets_completed / elapsed

    mesh_utilization = 0.0
    if state.router_stats:
        mesh_utilization = sum(
            [r["utilization"] for r in state.router_stats.values()]
        ) / len(state.router_stats)

    # VCD replay progress
    vcd_progress = 0.0
    if state.vcd_events:
        vcd_progress = state.vcd_replay_index / len(state.vcd_events)

    # Add performance history for trending
    performance_data = {
        "total_packets": state.total_packets_generated,  # Total generated since start
        "active_packets": active_packets,  # Currently routing
        "completed_packets": state.total_packets_completed,  # Total completed
        "delivered_visible": delivered_packets_visible,  # Delivered but still visible
        "average_latency": avg_latency,  # Average latency in ms
        "throughput": throughput,  # Packets per second
        "mesh_utilization": mesh_utilization,
        "history": state.performance_history[-20:],  # Last 20 data points
        "simulation_time": state.simulation_time,
        "vcd_replay_progress": vcd_progress,
        "vcd_replay_active": state.vcd_replay_active,
        "vcd_replay_speed": state.vcd_replay_speed,
        "vcd_replay_index": state.vcd_replay_index,
        "vcd_total_events": len(state.vcd_events),
    }

    return jsonify(performance_data)


@app.route("/api/simulation/log")
def get_simulation_log():
    """Get simulation log entries"""
    return jsonify({"log": state.simulation_log})


@app.route("/api/simulation/vcd")
def get_vcd_events():
    """Get VCD packet events for visualization"""
    return jsonify(
        {
            "events": [asdict(event) for event in state.vcd_events],
            "event_count": len(state.vcd_events),
            "replay_index": state.vcd_replay_index,
        }
    )


@app.route("/api/simulation/vcd/replay", methods=["POST"])
def control_vcd_replay():
    """Control VCD event replay"""
    data = request.get_json()
    action = data.get("action", "play")

    if action == "reset":
        state.vcd_replay_index = 0
        state.packets = []
        state.simulation_time = 0
        state.performance_history = []
        state._initialize_router_stats()
        state.vcd_replay_active = True
    elif action == "step":
        if state.vcd_replay_index < len(state.vcd_events) - 1:
            state.update_simulation_from_vcd()
    elif action == "play":
        state.vcd_replay_active = True
    elif action == "pause":
        state.vcd_replay_active = False
    elif action == "jump":
        index = data.get("index", 0)
        if 0 <= index < len(state.vcd_events):
            state.vcd_replay_index = index
            # Reset simulation state to this point
            state.packets = []
            state.simulation_time = index
            state.performance_history = []
            state._initialize_router_stats()
            # Reset performance tracking for new position
            state.total_packets_generated = 0
            state.total_packets_completed = 0
            state.packet_latencies = []
    elif action == "speed":
        speed = data.get("speed", 1.0)
        state.vcd_replay_speed = max(
            0.1, min(10.0, speed)
        )  # Clamp between 0.1x and 10x
    elif action == "seek":
        # Seek to a specific percentage of the VCD file
        percentage = data.get("percentage", 0.0)
        if 0.0 <= percentage <= 1.0:
            target_index = int(percentage * len(state.vcd_events))
            state.vcd_replay_index = target_index
            # Reset simulation state
            state.packets = []
            state.simulation_time = target_index
            state.performance_history = []
            state._initialize_router_stats()
            # Reset performance tracking
            state.total_packets_generated = 0
            state.total_packets_completed = 0
            state.packet_latencies = []

    return jsonify(
        {
            "replay_index": state.vcd_replay_index,
            "total_events": len(state.vcd_events),
            "replay_active": state.vcd_replay_active,
            "replay_speed": state.vcd_replay_speed,
            "simulation_time": state.simulation_time,
        }
    )


@app.route("/api/simulation/vcd/speed", methods=["POST"])
def set_vcd_replay_speed():
    """Set VCD replay speed"""
    try:
        data = request.get_json()
        speed = data.get("speed", 1.0)
        state.vcd_replay_speed = max(
            0.1, min(10.0, float(speed))
        )  # Clamp between 0.1x and 10x

        return jsonify(
            {
                "replay_speed": state.vcd_replay_speed,
                "message": f"Replay speed set to {state.vcd_replay_speed}x",
            }
        )
    except Exception as e:
        logger.error(f"Error setting VCD replay speed: {e}")
        return jsonify({"error": str(e)}), 500


@app.route("/api/simulation/vcd/seek", methods=["POST"])
def seek_vcd_replay():
    """Seek to specific position in VCD replay"""
    try:
        data = request.get_json()
        percentage = data.get("percentage", 0.0)

        if not 0.0 <= percentage <= 1.0:
            return jsonify({"error": "Percentage must be between 0.0 and 1.0"}), 400

        if not state.vcd_events:
            return jsonify({"error": "No VCD events loaded"}), 400

        target_index = int(percentage * len(state.vcd_events))
        state.vcd_replay_index = target_index

        # Reset simulation state for new position
        state.packets = []
        state.simulation_time = target_index
        state.performance_history = []
        state._initialize_router_stats()
        # Reset performance tracking
        state.total_packets_generated = 0
        state.total_packets_completed = 0
        state.packet_latencies = []

        return jsonify(
            {
                "replay_index": state.vcd_replay_index,
                "total_events": len(state.vcd_events),
                "percentage": percentage,
                "message": f"Seeked to {percentage*100:.1f}% ({state.vcd_replay_index}/{len(state.vcd_events)})",
            }
        )
    except Exception as e:
        logger.error(f"Error seeking VCD replay: {e}")
        return jsonify({"error": str(e)}), 500
    """Get current VCD replay status"""
    return jsonify(
        {
            "replay_index": state.vcd_replay_index,
            "total_events": len(state.vcd_events),
            "replay_active": state.vcd_replay_active,
            "replay_speed": state.vcd_replay_speed,
            "simulation_time": state.simulation_time,
            "packets_count": len(state.packets),
            "progress": (
                (state.vcd_replay_index / len(state.vcd_events))
                if state.vcd_events
                else 0.0
            ),
        }
    )


@app.route("/api/vcd/files")
def list_vcd_files():
    """List all available VCD files"""
    try:
        vcd_files = []
        build_dir = os.path.join(project_root, "code", "build")

        if os.path.exists(build_dir):
            for file in os.listdir(build_dir):
                if file.endswith(".vcd"):
                    file_path = os.path.join(build_dir, file)
                    stat = os.stat(file_path)
                    vcd_files.append(
                        {
                            "name": file,
                            "path": file_path,
                            "size": stat.st_size,
                            "modified": stat.st_mtime,
                            "readable_size": format_file_size(stat.st_size),
                            "readable_time": time.strftime(
                                "%Y-%m-%d %H:%M:%S", time.localtime(stat.st_mtime)
                            ),
                        }
                    )

        # Sort by modification time (newest first)
        vcd_files.sort(key=lambda x: x["modified"], reverse=True)

        return jsonify({"vcd_files": vcd_files, "count": len(vcd_files)})

    except Exception as e:
        logger.error(f"Error listing VCD files: {e}")
        return jsonify({"error": str(e)}), 500


@app.route("/api/vcd/load", methods=["POST"])
def load_vcd_file():
    """Load and parse a specific VCD file"""
    try:
        data = request.get_json()
        vcd_file = data.get("file")

        if not vcd_file:
            return jsonify({"error": "No VCD file specified"}), 400

        # Validate the file path (security check)
        build_dir = os.path.join(project_root, "code", "build")
        vcd_path = os.path.join(build_dir, vcd_file)

        if not os.path.exists(vcd_path) or not vcd_path.startswith(build_dir):
            return jsonify({"error": "VCD file not found or invalid path"}), 404

        if not TRAFFIC_AVAILABLE:
            return jsonify({"error": "VCD parser not available"}), 500

        # Parse the VCD file
        logger.info(f"Loading VCD file: {vcd_file}")
        parser = SimpleVCDParser(vcd_path)
        success = parser.parse()

        if not success:
            return jsonify({"error": "Failed to parse VCD file"}), 500

        events = parser.packet_events

        # Update state with loaded events
        state.vcd_events = events
        state.vcd_replay_index = 0
        state.last_vcd_file = vcd_file

        # Convert VCD to workload data for simulation
        state.convert_vcd_to_workload()

        # Reset simulation state for new VCD data
        state.packets = []
        state.simulation_time = 0
        state.performance_history = []
        state.vcd_replay_active = True
        # Reset performance tracking
        state.total_packets_generated = 0
        state.total_packets_completed = 0
        state.packet_latencies = []
        state.next_packet_id = 0

        # Initialize router stats
        state._initialize_router_stats()

        logger.info(f"Loaded {len(events)} events from {vcd_file}")

        return jsonify(
            {
                "message": f"Loaded {len(events)} events from {vcd_file}",
                "event_count": len(events),
                "file": vcd_file,
                "replay_active": state.vcd_replay_active,
            }
        )

    except Exception as e:
        logger.error(f"Error loading VCD file: {e}")
        return jsonify({"error": str(e)}), 500


def format_file_size(size_bytes):
    """Format file size in human readable format"""
    if size_bytes == 0:
        return "0 B"

    size_names = ["B", "KB", "MB", "GB"]
    import math

    i = int(math.floor(math.log(size_bytes, 1024)))
    p = math.pow(1024, i)
    s = round(size_bytes / p, 2)
    return f"{s} {size_names[i]}"


def run_verilog_simulation(mesh_width, mesh_height, pattern, injection_rate):
    """Run Verilog simulation with proper logging"""
    try:
        state.simulation_running = True
        state.simulation_status = "initializing"
        state.simulation_start_time = time.time()
        state.simulation_log = []
        state.last_simulation_error = None

        logger.info(
            f"Starting simulation: {mesh_width}x{mesh_height}, pattern={pattern}, rate={injection_rate}"
        )

        if not TRAFFIC_AVAILABLE:
            raise Exception("Traffic generation modules not available")

        # Initialize traffic generator
        config = TrafficConfig(
            mesh_width=mesh_width,
            mesh_height=mesh_height,
            pattern=TrafficPattern(pattern),
            injection_rate=injection_rate,
            duration_cycles=50,  # Reduced from default 1000 to limit VCD file size
        )

        generator = NebulaTrafficGenerator(config)
        logger.info(f"Initialized Nebula Traffic Generator")
        logger.info(
            f"Mesh: {mesh_width}x{mesh_height} ({mesh_width * mesh_height} nodes)"
        )
        logger.info(f"Pattern: {pattern}")
        logger.info(f"Injection rate: {injection_rate}")

        state.simulation_status = "generating_traffic"
        socketio.emit("simulation_status_update", {"status": state.simulation_status})

        # Generate traffic using the correct method
        traces = generator.generate_pattern_traces(TrafficPattern(pattern))
        logger.info(f"Generated {len(traces)} {pattern} packets")

        # Generate testbench and stimulus files
        testbench_file, _ = generator.generate_and_run_simulation(
            pattern=TrafficPattern(pattern),
            output_dir=os.path.join(project_root, "code", "tb", "generated"),
        )

        logger.info(f"Generated testbench: {testbench_file}")
        logger.info(f"Generated {len(traces)} stimulus entries")

        state.simulation_status = "compiling"
        socketio.emit("simulation_status_update", {"status": state.simulation_status})

        # Run Verilog compilation and simulation
        code_dir = os.path.join(project_root, "code")

        # Use make with timeout and capture all output
        cmd = ["make", "tb_nebula_traffic"]

        logger.info(f"Running Verilog compilation in {code_dir}")
        verilog_logger.info(f"Starting Verilog compilation: {' '.join(cmd)}")

        process = subprocess.Popen(
            cmd,
            cwd=code_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
            universal_newlines=True,
        )

        state.verilog_process = process

        # Stream output to logs and WebSocket
        compilation_complete = False
        simulation_started = False

        for line in iter(process.stdout.readline, ""):
            if not line:
                break

            line = line.strip()
            if line:
                # Log all output to file
                verilog_logger.info(f"Verilog compilation: {line}")

                # Show important stages in terminal
                if any(
                    keyword in line.lower()
                    for keyword in ["error", "failed", "warning"]
                ):
                    print(f"🔧 {line}")

                # Update WebSocket with compilation progress
                if "Compiling" in line or "Building" in line:
                    socketio.emit(
                        "simulation_log_update",
                        {"message": f"Compilation: {line}", "type": "info"},
                    )
                elif "simulation started" in line.lower():
                    simulation_started = True
                    state.simulation_status = "running"
                    print("▶️ Simulation started")
                    socketio.emit(
                        "simulation_status_update", {"status": state.simulation_status}
                    )
                elif "simulation complete" in line.lower() or "finish" in line.lower():
                    print("✅ Simulation completed")
                    socketio.emit(
                        "simulation_log_update",
                        {"message": "Simulation completed", "type": "success"},
                    )

        # Wait for process completion with timeout
        try:
            exit_code = process.wait(timeout=300)  # 5 minute timeout

            if exit_code == 0:
                state.simulation_status = "completed"
                logger.info("Verilog simulation completed successfully")
                print("✅ Verilog simulation completed")

                # Process VCD file if it exists
                vcd_path = os.path.join(code_dir, "build", "tb_nebula_traffic.vcd")
                if os.path.exists(vcd_path):
                    print("📊 Processing VCD file...")
                    state.simulation_status = "processing_vcd"
                    socketio.emit(
                        "simulation_status_update", {"status": state.simulation_status}
                    )

                    try:
                        if TRAFFIC_AVAILABLE:
                            parser = SimpleVCDParser(vcd_path)
                            parser.parse()
                            state.vcd_events = parser.packet_events

                            # Process VCD data for simulation
                            state.convert_vcd_to_workload()

                            # Reset and initialize simulation state
                            state.packets = []
                            state.simulation_time = 0
                            state.performance_history = []
                            state.vcd_replay_index = 0
                            state.vcd_replay_active = True
                            state._initialize_router_stats()

                            logger.info(
                                f"Loaded {len(state.vcd_events)} packet events from VCD"
                            )
                            print(f"📈 Loaded {len(state.vcd_events)} packet events")
                            print("🔄 VCD replay started automatically")
                        else:
                            logger.warning("VCD parser not available")
                            print("⚠️ VCD parser not available")
                    except Exception as vcd_error:
                        logger.error(f"VCD processing error: {vcd_error}")
                        print(f"❌ VCD processing error: {vcd_error}")

                    state.simulation_status = "completed"
                else:
                    logger.warning("VCD file not found")
                    print("⚠️ VCD file not found")
            else:
                state.simulation_status = "failed"
                error_msg = f"Verilog simulation failed with exit code {exit_code}"
                state.last_simulation_error = error_msg
                logger.error(error_msg)
                print(f"❌ {error_msg}")

        except subprocess.TimeoutExpired:
            process.kill()
            state.simulation_status = "timeout"
            error_msg = "Verilog simulation timed out after 5 minutes"
            state.last_simulation_error = error_msg
            logger.error(error_msg)
            print(f"⏰ {error_msg}")

    except Exception as e:
        state.simulation_status = "error"
        state.last_simulation_error = str(e)
        logger.error(f"Simulation error: {e}")
        print(f"❌ Simulation error: {e}")
        socketio.emit(
            "simulation_log_update", {"message": f"Error: {e}", "type": "error"}
        )

    finally:
        state.simulation_running = False
        state.verilog_process = None
        socketio.emit("simulation_status_update", {"status": state.simulation_status})


@app.route("/api/simulation/start", methods=["POST"])
def start_simulation():
    """Start a new simulation"""
    if state.simulation_running:
        return jsonify({"error": "Simulation already running"}), 400

    data = request.get_json()
    mesh_width = data.get("mesh_width", 4)
    mesh_height = data.get("mesh_height", 4)
    pattern = data.get("pattern", "uniform_random")
    injection_rate = data.get("injection_rate", 0.1)

    # Start simulation in background thread
    thread = threading.Thread(
        target=run_verilog_simulation,
        args=(mesh_width, mesh_height, pattern, injection_rate),
        daemon=True,
    )
    thread.start()

    return jsonify({"message": "Simulation started"})


@app.route("/api/simulation/cancel", methods=["POST"])
def cancel_simulation():
    """Cancel the running simulation"""
    if not state.simulation_running:
        return jsonify({"error": "No simulation running"}), 400

    if state.verilog_process:
        state.verilog_process.terminate()
        logger.info("Simulation cancelled by user")
        print("🛑 Simulation cancelled")

    state.simulation_running = False
    state.simulation_status = "cancelled"
    state.verilog_process = None

    return jsonify({"message": "Simulation cancelled"})


@socketio.on("connect")
def handle_connect():
    logger.info(f"Client connected from {request.remote_addr}")
    emit("status_update", get_status_data())


@socketio.on("disconnect")
def handle_disconnect():
    logger.info(f"Client disconnected from {request.remote_addr}")


def background_thread():
    """Background thread for periodic updates and VCD replay"""
    while True:
        try:
            # Update VCD replay if active
            if (
                state.vcd_replay_active
                and state.vcd_events
                and state.vcd_replay_index < len(state.vcd_events)
            ):
                state.update_simulation_from_vcd()

                # Emit real-time updates via WebSocket
                if socketio:
                    socketio.emit(
                        "mesh_update",
                        {
                            "routers": list(state.router_stats.values()),
                            "packets": state.packets,
                            "mesh_width": state.mesh_width,
                            "mesh_height": state.mesh_height,
                        },
                    )

                    socketio.emit(
                        "performance_update",
                        {
                            "history": state.performance_history[
                                -10:
                            ],  # Last 10 points
                            "current": (
                                state.performance_history[-1]
                                if state.performance_history
                                else None
                            ),
                            "simulation_time": state.simulation_time,
                            "vcd_progress": (
                                (state.vcd_replay_index / len(state.vcd_events))
                                if state.vcd_events
                                else 0.0
                            ),
                        },
                    )

            # Always emit status updates
            if socketio:
                socketio.emit("status_update", get_status_data())

        except Exception as e:
            logger.error(f"Background thread error: {e}")

        # Update frequency: faster when replaying VCD, slower when idle
        if state.vcd_replay_active and state.vcd_events:
            # Dynamic sleep time based on replay speed
            # Base frequency is 10 Hz (0.1s), adjusted by speed multiplier
            base_sleep = 0.1
            sleep_time = base_sleep / max(
                0.1, state.vcd_replay_speed
            )  # Prevent division by very small numbers
            time.sleep(sleep_time)
        else:
            time.sleep(1.0)  # 1 Hz for status updates only


# Start background thread
thread = threading.Thread(target=background_thread, daemon=True)
thread.start()

if __name__ == "__main__":
    print("🚀 Nebula Dashboard starting at http://localhost:5000")
    print(f"📂 Logs: {log_dir}")

    # Log detailed startup info to file
    logger.info("Starting Nebula Dashboard Flask Backend")
    logger.info(f"Project root: {project_root}")
    logger.info("Backend available at: http://localhost:5000")
    logger.info(f"Logs stored in: {log_dir}")
    logger.info("- dashboard.log: Main application logs")
    logger.info("- api_calls.log: API request logs")
    logger.info("- verilog_compilation.log: Verilog compilation output")

    socketio.run(
        app, debug=False, host="0.0.0.0", port=5000, allow_unsafe_werkzeug=True
    )
