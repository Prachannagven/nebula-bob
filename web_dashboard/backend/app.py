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
        "active_packets": len([p for p in state.packets if p.status == "routing"]),
        "completed_packets": len([p for p in state.packets if p.status == "delivered"]),
        "vcd_events_count": len(state.vcd_events),
        "vcd_replay_index": state.vcd_replay_index,
        "last_vcd_file": state.last_vcd_file,
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
            "packets": [
                asdict(packet) if hasattr(packet, "__dict__") else packet
                for packet in state.packets
            ],
            "mesh_width": state.mesh_width,
            "mesh_height": state.mesh_height,
        }
    )


@app.route("/api/performance")
def get_performance_data():
    """Get performance metrics"""
    api_logger.info(f"Performance data request from {request.remote_addr}")

    total_packets = len(state.packets)
    active_packets = len([p for p in state.packets if p.status == "routing"])
    completed_packets = len([p for p in state.packets if p.status == "delivered"])

    avg_latency = 0.0
    if completed_packets > 0:
        total_latency = sum(
            [p.timestamp for p in state.packets if p.status == "delivered"]
        )
        avg_latency = total_latency / completed_packets

    throughput = 0.0
    if state.simulation_start_time:
        elapsed = time.time() - state.simulation_start_time
        if elapsed > 0:
            throughput = completed_packets / elapsed

    return jsonify(
        {
            "total_packets": total_packets,
            "active_packets": active_packets,
            "completed_packets": completed_packets,
            "average_latency": avg_latency,
            "throughput": throughput,
            "mesh_utilization": (
                sum([r.utilization for r in state.router_stats.values()])
                / len(state.router_stats)
                if state.router_stats
                else 0.0
            ),
        }
    )


@app.route("/api/simulation/log")
def get_simulation_log():
    """Get simulation log entries"""
    return jsonify({"log": state.simulation_log})


@app.route("/api/simulation/vcd")
def get_vcd_events():
    """Get VCD packet events for visualization"""
    return jsonify({
        "events": [asdict(event) for event in state.vcd_events],
        "event_count": len(state.vcd_events),
        "replay_index": state.vcd_replay_index
    })


@app.route("/api/simulation/vcd/replay", methods=["POST"])
def control_vcd_replay():
    """Control VCD event replay"""
    data = request.get_json()
    action = data.get("action", "play")
    
    if action == "reset":
        state.vcd_replay_index = 0
    elif action == "step":
        if state.vcd_replay_index < len(state.vcd_events) - 1:
            state.vcd_replay_index += 1
    elif action == "jump":
        index = data.get("index", 0)
        if 0 <= index < len(state.vcd_events):
            state.vcd_replay_index = index
    
    return jsonify({
        "replay_index": state.vcd_replay_index,
        "total_events": len(state.vcd_events)
    })


@app.route("/api/vcd/files")
def list_vcd_files():
    """List all available VCD files"""
    try:
        vcd_files = []
        build_dir = os.path.join(project_root, "code", "build")
        
        if os.path.exists(build_dir):
            for file in os.listdir(build_dir):
                if file.endswith('.vcd'):
                    file_path = os.path.join(build_dir, file)
                    stat = os.stat(file_path)
                    vcd_files.append({
                        "name": file,
                        "path": file_path,
                        "size": stat.st_size,
                        "modified": stat.st_mtime,
                        "readable_size": format_file_size(stat.st_size),
                        "readable_time": time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(stat.st_mtime))
                    })
        
        # Sort by modification time (newest first)
        vcd_files.sort(key=lambda x: x["modified"], reverse=True)
        
        return jsonify({
            "vcd_files": vcd_files,
            "count": len(vcd_files)
        })
        
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
        
        logger.info(f"Loaded {len(events)} events from {vcd_file}")
        
        return jsonify({
            "message": f"Loaded {len(events)} events from {vcd_file}",
            "event_count": len(events),
            "file": vcd_file
        })
        
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
                    socketio.emit("simulation_status_update", {"status": state.simulation_status})
                    
                    try:
                        if TRAFFIC_AVAILABLE:
                            parser = SimpleVCDParser(vcd_path)
                            parser.parse()
                            state.vcd_events = parser.packet_events
                            logger.info(f"Loaded {len(state.vcd_events)} packet events from VCD")
                            print(f"📈 Loaded {len(state.vcd_events)} packet events")
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
    """Background thread for periodic updates"""
    while True:
        time.sleep(5)  # Update every 5 seconds
        if socketio:
            socketio.emit("status_update", get_status_data())


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
