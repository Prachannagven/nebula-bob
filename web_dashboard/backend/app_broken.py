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
prif __name__ == "__main__":
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

    socketio.run(app, debug=False, host="0.0.0.0", port=5000, allow_unsafe_werkzeug=True)= os.path.dirname(
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

# Set up logging
log_dir = os.path.join(os.path.dirname(__file__), 'logs')
os.makedirs(log_dir, exist_ok=True)

# Configure main logger - only file output for detailed logs
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(os.path.join(log_dir, 'dashboard.log'))
    ]
)
logger = logging.getLogger(__name__)

# Create a separate console logger for important messages only
console_logger = logging.getLogger('console')
console_handler = logging.StreamHandler()
console_handler.setLevel(logging.WARNING)  # Only show warnings and errors in terminal
console_handler.setFormatter(logging.Formatter('%(levelname)s: %(message)s'))
console_logger.addHandler(console_handler)
console_logger.propagate = False

# Configure Flask's werkzeug logger to reduce noise
werkzeug_logger = logging.getLogger('werkzeug')
werkzeug_logger.setLevel(logging.ERROR)  # Only show errors

# Create a separate logger for API calls
api_logger = logging.getLogger('api_calls')
api_logger.setLevel(logging.INFO)
api_handler = logging.FileHandler(os.path.join(log_dir, 'api_calls.log'))
api_handler.setFormatter(logging.Formatter('%(asctime)s - %(message)s'))
api_logger.addHandler(api_handler)
api_logger.propagate = False  # Don't propagate to root logger

# Create a separate logger for Verilog compilation
verilog_logger = logging.getLogger('verilog_compilation')
verilog_logger.setLevel(logging.INFO)
verilog_handler = logging.FileHandler(os.path.join(log_dir, 'verilog_compilation.log'))
verilog_handler.setFormatter(logging.Formatter('%(asctime)s - %(message)s'))
verilog_logger.addHandler(verilog_handler)
verilog_logger.propagate = False  # Don't propagate to root logger

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
        self.router_stats = {}
        self.packets = []
        self.performance_history = []
        self.verilog_process = None
        self.last_simulation_error = None

        # Initialize router stats
        for i in range(self.mesh_width * self.mesh_height):
            self.router_stats[i] = {
                "node_id": i,
                "x": i % self.mesh_width,
                "y": i // self.mesh_width,
                "packets_received": 0,
                "packets_sent": 0,
                "bytes_processed": 0,
                "congestion_level": 0.0,
                "temperature": 25.0,
                "utilization": 0.0,
            }


state = DashboardState()


@app.route("/")
def index():
    """Serve the frontend"""
    return send_from_directory("../frontend/dist", "index.html")


@app.route("/<path:path>")
def serve_static(path):
    """Serve static files"""
    return send_from_directory("../frontend/dist", path)


def get_status_data():
    """Get current dashboard status as dict"""
    return {
        "simulation_running": state.simulation_running,
        "simulation_status": state.simulation_status,
        "simulation_progress": state.simulation_progress,
        "traffic_available": TRAFFIC_AVAILABLE,
        "mesh_size": {"width": state.mesh_width, "height": state.mesh_height},
        "elapsed_time": get_elapsed_time() if state.simulation_start_time else "0s",
    }


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
    return jsonify(
        {
            "history": state.performance_history[-100:],  # Last 100 points
            "router_utilization": [
                stats["utilization"] for stats in state.router_stats.values()
            ],
        }
    )


@app.route("/api/simulation/start", methods=["POST"])
def start_simulation():
    """Start a Verilog simulation"""
    if state.simulation_running:
        return jsonify({"error": "Simulation already running"}), 400

    if not TRAFFIC_AVAILABLE:
        return jsonify({"error": "Traffic generator not available"}), 400

    data = request.get_json()
    pattern = data.get("pattern", "uniform_random")
    duration = data.get("duration", 1000)

    # Start simulation in background thread
    thread = threading.Thread(
        target=run_simulation_thread, args=(pattern, duration), daemon=True
    )
    thread.start()

    return jsonify(
        {"message": "Simulation started", "pattern": pattern, "duration": duration}
    )


@app.route("/api/simulation/cancel", methods=["POST"])
def cancel_simulation():
    """Cancel running simulation"""
    if not state.simulation_running:
        return jsonify({"error": "No simulation running"}), 400

    cancel_simulation_process()
    return jsonify({"message": "Simulation cancelled"})


@app.route("/api/simulation/log")
def get_simulation_log():
    """Get simulation log"""
    api_logger.info(f"Simulation log request from {request.remote_addr}")
    return jsonify({"log": state.simulation_log[-50:]})  # Last 50 entries


def run_simulation_thread(pattern: str, duration: int):
    """Run simulation in background thread"""
    try:
        state.simulation_running = True
        state.simulation_status = "running"
        state.simulation_progress = 0
        state.simulation_start_time = time.time()
        state.simulation_log = [f"🚀 Starting simulation with {pattern} pattern..."]

        # Emit status update
        socketio.emit(
            "simulation_status",
            {
                "status": state.simulation_status,
                "progress": state.simulation_progress,
                "message": f"Starting {pattern} simulation...",
            },
        )

        # Generate traffic pattern
        state.simulation_log.append(f"⚙️ Generating {pattern} traffic pattern...")
        state.simulation_progress = 20
        socketio.emit("simulation_progress", {"progress": state.simulation_progress})

        testbench_path, traces = generate_traffic_pattern(pattern, duration)
        if not testbench_path:
            state.simulation_status = "failed"
            state.simulation_log.append("❌ Failed to generate traffic pattern")
            socketio.emit(
                "simulation_status",
                {"status": "failed", "message": "Failed to generate traffic pattern"},
            )
            return

        state.simulation_progress = 50
        state.simulation_log.append(
            f"✅ Traffic pattern generated: {len(traces)} traces"
        )
        state.simulation_log.append(f"🔨 Running Verilog simulation...")
        socketio.emit("simulation_progress", {"progress": state.simulation_progress})

        # Run Verilog simulation
        success = run_verilog_simulation(testbench_path)

        if success:
            state.simulation_progress = 90
            state.simulation_log.append("🔄 Processing VCD data...")
            socketio.emit(
                "simulation_progress", {"progress": state.simulation_progress}
            )

            # Load VCD data
            load_vcd_data()

            state.simulation_progress = 100
            state.simulation_status = "completed"
            state.simulation_log.append("✅ Simulation completed successfully!")
            socketio.emit(
                "simulation_status",
                {"status": "completed", "message": "Simulation completed!"},
            )
        else:
            state.simulation_status = "failed"
            state.simulation_log.append("❌ Verilog simulation failed")
            socketio.emit(
                "simulation_status",
                {"status": "failed", "message": "Verilog simulation failed"},
            )

    except Exception as e:
        state.simulation_status = "failed"
        state.simulation_log.append(f"❌ Error: {str(e)}")
        socketio.emit(
            "simulation_status", {"status": "failed", "message": f"Error: {str(e)}"}
        )
    finally:
        state.simulation_running = False


def generate_traffic_pattern(pattern: str, duration: int):
    """Generate traffic pattern"""
    try:
        pattern_enum = TrafficPattern(pattern)

        config = TrafficConfig(
            mesh_width=state.mesh_width,
            mesh_height=state.mesh_height,
            pattern=pattern_enum,
            injection_rate=0.1,
            duration_cycles=duration,
            packet_size_bytes=64,
            enable_axi=True,
            enable_chi=False,
        )

        generator = NebulaTrafficGenerator(config)

        output_dir = os.path.join(project_root, "code", "tb", "generated")
        os.makedirs(output_dir, exist_ok=True)

        testbench_path, traces = generator.generate_and_run_simulation(
            pattern_enum, output_dir
        )
        return testbench_path, traces

    except Exception as e:
        logger.error(f"Error generating traffic pattern: {e}")
        return None, []


def run_verilog_simulation(testbench_path: str) -> bool:
    """Run Verilog simulation with real-time logging"""
    if not os.path.exists(testbench_path):
        logger.error(f"Testbench file not found: {testbench_path}")
        return False

    try:
        code_dir = os.path.join(project_root, "code")
        cmd = ["make", "tb_nebula_traffic"]
        
        state.simulation_log.append(f"🔨 Starting make command: {' '.join(cmd)}")
        state.simulation_log.append(f"📁 Working directory: {code_dir}")
        socketio.emit('simulation_log_update', {'log': state.simulation_log[-2:]})

        state.verilog_process = subprocess.Popen(
            cmd,
            cwd=code_dir,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,  # Combine stderr into stdout for easier handling
            text=True,
            bufsize=1,  # Line buffered
            universal_newlines=True
        )

        # Read output in real-time with longer timeout
        timeout = 300  # 5 minutes instead of 2 minutes
        start_time = time.time()
        output_lines = []
        
        while True:
            # Check if process has finished
            if state.verilog_process.poll() is not None:
                # Process finished, read any remaining output
                remaining_output = state.verilog_process.stdout.read()
                if remaining_output:
                    output_lines.append(remaining_output)
                    state.simulation_log.append(f"📄 {remaining_output.strip()}")
                    socketio.emit('simulation_log_update', {'log': [f"📄 {remaining_output.strip()}"]})
                break
            
            # Check for timeout
            if time.time() - start_time > timeout:
                logger.error(f"Verilog simulation timed out after {timeout} seconds")
                state.simulation_log.append(f"⏰ Simulation timed out after {timeout} seconds")
                socketio.emit('simulation_log_update', {'log': [f"⏰ Simulation timed out after {timeout} seconds"]})
                state.verilog_process.kill()
                state.verilog_process.wait()
                return False
            
            # Try to read a line with a short timeout
            try:
                line = state.verilog_process.stdout.readline()
                if line:
                    line = line.strip()
                    output_lines.append(line)
                    
                    # Log important compilation stages
                    if any(keyword in line.lower() for keyword in ['verilating', 'compiling', 'linking', 'error', 'warning']):
                        state.simulation_log.append(f"🔧 {line}")
                        socketio.emit('simulation_log_update', {'log': [f"🔧 {line}"]})
                        verilog_logger.info(f"Compilation stage: {line}")
                    else:
                        # Log all output to file but not to console
                        verilog_logger.info(line)
                    
                    # Update progress based on compilation stages
                    if 'verilating' in line.lower():
                        state.simulation_progress = 60
                        socketio.emit('simulation_progress', {'progress': state.simulation_progress})
                    elif 'compiling' in line.lower():
                        state.simulation_progress = 70
                        socketio.emit('simulation_progress', {'progress': state.simulation_progress})
                    elif 'linking' in line.lower():
                        state.simulation_progress = 80
                        socketio.emit('simulation_progress', {'progress': state.simulation_progress})
                        
            except Exception as read_error:
                # Non-blocking read failed, continue
                time.sleep(0.1)
                continue

        # Check return code
        return_code = state.verilog_process.returncode
        if return_code == 0:
            logger.info("Verilog simulation completed successfully")
            state.simulation_log.append("✅ Verilog compilation completed successfully")
            socketio.emit('simulation_log_update', {'log': ["✅ Verilog compilation completed successfully"]})
            return True
        else:
            full_output = '\n'.join(output_lines)
            logger.error(f"Verilog simulation failed with return code {return_code}")
            state.simulation_log.append(f"❌ Verilog compilation failed (code {return_code})")
            
            # Show last few lines of output for debugging
            last_lines = output_lines[-10:] if len(output_lines) > 10 else output_lines
            for line in last_lines:
                if line.strip():
                    state.simulation_log.append(f"📄 {line}")
            
            socketio.emit('simulation_log_update', {'log': state.simulation_log[-11:]})
            
            state.last_simulation_error = {
                "return_code": return_code,
                "output": full_output,
                "last_lines": last_lines
            }
            return False

    except subprocess.TimeoutExpired:
        logger.error("Verilog simulation timed out")
        state.simulation_log.append("⏰ Verilog simulation timed out")
        socketio.emit('simulation_log_update', {'log': ["⏰ Verilog simulation timed out"]})
        if state.verilog_process:
            state.verilog_process.kill()
        return False
    except Exception as e:
        logger.error(f"Error running Verilog simulation: {e}")
        state.simulation_log.append(f"❌ Error: {str(e)}")
        socketio.emit('simulation_log_update', {'log': [f"❌ Error: {str(e)}"]})
        return False


def load_vcd_data():
    """Load VCD data for visualization"""
    try:
        build_dir = os.path.join(project_root, "code", "build")
        vcd_path = os.path.join(build_dir, "tb_nebula_top.vcd")

        if os.path.exists(vcd_path):
            parser = SimpleVCDParser(vcd_path)
            state.vcd_events = parser.parse_packets()
            state.vcd_replay_index = 0
            logger.info(f"Loaded {len(state.vcd_events)} events from VCD file")
            return True
        else:
            logger.error(f"VCD file not found at {vcd_path}")
            return False

    except Exception as e:
        logger.error(f"Error loading VCD data: {e}")
        return False


def cancel_simulation_process():
    """Cancel running simulation"""
    if state.verilog_process:
        try:
            state.verilog_process.terminate()
            state.verilog_process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            state.verilog_process.kill()
        except Exception as e:
            logger.error(f"Error cancelling simulation: {e}")

    state.simulation_running = False
    state.simulation_status = "cancelled"
    state.simulation_log.append("🛑 Simulation cancelled by user")


def get_elapsed_time():
    """Get formatted elapsed time"""
    if not state.simulation_start_time:
        return "0s"
    elapsed = time.time() - state.simulation_start_time
    return f"{elapsed:.1f}s"


# WebSocket events for real-time updates
@socketio.on('connect')
def handle_connect(auth):
    """Handle client connection"""
    logger.info("WebSocket client connected")
    emit("status", get_status_data())


@socketio.on("disconnect")
def handle_disconnect():
    logger.info("WebSocket client disconnected")


# Periodic updates
def background_thread():
    """Send periodic updates to connected clients"""
    while True:
        socketio.sleep(1)  # Update every second
        if socketio:
            socketio.emit(
                "mesh_update",
                {
                    "routers": list(state.router_stats.values()),
                    "packets": state.packets,
                    "timestamp": time.time(),
                },
            )


# Start background thread
thread = threading.Thread(target=background_thread, daemon=True)
thread.start()

if __name__ == "__main__":
    print("🚀 Starting Nebula Dashboard Flask Backend")
    print(f"📍 Project root: {project_root}")
    print("🌐 Backend available at: http://localhost:5000")
    print(f"� Logs stored in: {log_dir}")
    print("   - dashboard.log: Main application logs")
    print("   - api_calls.log: API request logs")
    print("   - verilog_compilation.log: Verilog compilation output")
    print()

    socketio.run(app, debug=False, host="0.0.0.0", port=5000, allow_unsafe_werkzeug=True)
