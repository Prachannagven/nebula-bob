#!/usr/bin/env python3
"""
Nebula GPU Interconnect Dashboard - Verilog Testing Interface

A comprehensive web-based dashboard for testing and visualizing
the Nebula NoC system using real Verilog simulations with realistic GPU workloads.

Features:
- Verilog-only simulation interface
- Real traffic pattern generation for SystemVerilog testbenches
- VCD-based visualization of actual NoC behavior
- Realistic CNN training and GPU workload patterns
- Interactive 3D mesh topology visualization
- Real-time performance analysis from actual hardware simulation
"""

import dash
from dash import dcc, html, Input, Output, State, callback_context
import dash_bootstrap_components as dbc
from flask import Flask
import plotly.graph_objects as go
import plotly.express as px
from plotly.subplots import make_subplots
import numpy as np
import pandas as pd
import time
import json
import threading
import queue
import subprocess
import os
from dataclasses import dataclass, asdict
from typing import List, Dict, Tuple, Optional
from enum import Enum
import logging

# Set up logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Reduce Flask/Werkzeug noise
logging.getLogger('werkzeug').setLevel(logging.ERROR)
logging.getLogger('dash.dash').setLevel(logging.ERROR)

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
    logger.warning(f"Traffic modules not available: {e}")
    TRAFFIC_AVAILABLE = False

# Dashboard Configuration
MESH_WIDTH = 4
MESH_HEIGHT = 4
UPDATE_INTERVAL = 100  # milliseconds
MAX_PACKETS = 50  # Maximum packets to show simultaneously


@dataclass
class Packet:
    """Packet representation for visualization"""

    id: int
    src_x: int
    src_y: int
    dst_x: int
    dst_y: int
    current_x: float
    current_y: float
    path: List[Tuple[int, int]]
    hop_index: int
    packet_type: str
    size_bytes: int
    timestamp: float
    priority: int = 0


@dataclass
class RouterStats:
    """Router statistics"""

    def __init__(self, node_id):
        self.node_id = node_id
        self.x = node_id % 4
        self.y = node_id // 4
        self.packets_received = 0
        self.packets_sent = 0
        self.bytes_processed = 0
        self.congestion_level = 0.0
        self.temperature = 25.0  # Celsius
        self.utilization = 0.0


class NebulaDashboardApp:
    """Modern Nebula GPU Interconnect Dashboard with enhanced visualization."""
    
    # Class variable to prevent duplicate callback registration
    _callbacks_registered = False

    def __init__(self):
        """Initialize the dashboard application."""
        print("🚀 Starting Nebula GPU Interconnect Dashboard...")
        print("📍 Project root:", os.path.dirname(os.path.dirname(os.path.dirname(__file__))))
        print("🔧 Dashboard will be available at: http://localhost:8050")
        print("💡 Dashboard features:")
        print("   - Verilog-only simulation interface")
        print("   - Real traffic pattern generation")
        print("   - VCD-based visualization") 
        print("   - Interactive mesh topology")
        print()

        # Initialize Flask and Dash apps
        self.flask_app = Flask(__name__)
        self.app = dash.Dash(__name__, server=self.flask_app, external_stylesheets=[dbc.themes.BOOTSTRAP])
        
        # Enhanced simulation state tracking
        self.simulation_running = False
        self.simulation_status = "idle"
        self.simulation_progress = 0
        self.simulation_start_time = None
        self.simulation_log = []
        self.simulation_cancelled = False
        
        # VCD visualization state
        self.vcd_events = []
        self.vcd_replay_index = 0
        self.current_mesh_data = None
        self.current_perf_data = None
        
        # Mesh topology configuration
        self.mesh_width = 4
        self.mesh_height = 4
        self.num_routers = self.mesh_width * self.mesh_height
        
        # Router state and statistics
        self.router_stats = {
            i: RouterStats(i) for i in range(self.num_routers)
        }
        
        # Packet simulation state
        self.packets = []
        
        # Performance tracking
        self.performance_history = []
        
        # Simulation error tracking
        self.last_simulation_error = None
        
        # Initialize dashboard components
        self.setup_layout()
        self.setup_callbacks()
        
        print("✅ Dashboard initialized successfully!")
        print("🌐 Starting web server...")

    def setup_layout(self):
        """Setup the dashboard layout"""

        # Header
        header = dbc.NavbarSimple(
            brand="🚀 Nebula GPU Interconnect Dashboard",
            brand_href="#",
            color="primary",
            dark=True,
            className="mb-4",
        )

        # Control panel - Verilog simulation only
        control_panel = dbc.Card(
            [
                dbc.CardHeader("🚀 Traffic Pattern Selection"),
                dbc.CardBody(
                    [
                        dbc.Row(
                            [
                                dbc.Col(
                                    [
                                        dbc.Label("Traffic Pattern"),
                                        dcc.Dropdown(
                                            id="verilog-pattern",
                                            options=[
                                                {
                                                    "label": "🎲 Uniform Random",
                                                    "value": "uniform_random",
                                                },
                                                {
                                                    "label": "� Hotspot",
                                                    "value": "hotspot",
                                                },
                                                {
                                                    "label": "↔️ Transpose",
                                                    "value": "transpose",
                                                },
                                                {
                                                    "label": "🧠 CNN Training",
                                                    "value": "cnn_training",
                                                },
                                                {
                                                    "label": "🔢 Matrix Multiply",
                                                    "value": "matrix_multiply",
                                                },
                                                {
                                                    "label": "🤖 Transformer",
                                                    "value": "transformer",
                                                },
                                                {
                                                    "label": "🌪️ Tornado",
                                                    "value": "tornado",
                                                },
                                                {
                                                    "label": "📈 Bit Complement",
                                                    "value": "bit_complement",
                                                },
                                            ],
                                            value="uniform_random",
                                            className="mb-2",
                                        ),
                                    ],
                                    width=12,
                                ),
                            ]
                        ),
                        dbc.Row(
                            [
                                dbc.Col(
                                    [
                                        dbc.Label("Duration (cycles)"),
                                        dbc.Input(
                                            id="verilog-duration",
                                            type="number",
                                            value=1000,
                                            min=100,
                                            max=10000,
                                            step=100,
                                            className="mb-2",
                                        ),
                                    ],
                                    width=12,
                                ),
                            ]
                        ),
                        dbc.Row(
                            [
                                dbc.Col(
                                    [
                                        dbc.Button(
                                            "🚀 Run Verilog Simulation",
                                            id="run-verilog-btn",
                                            color="primary",
                                            className="w-100",
                                        )
                                    ]
                                )
                            ],
                            className="mt-2",
                        ),
                        dbc.Row(
                            [
                                dbc.Col([
                                    html.Div(id="verilog-status", className="mt-2"),
                                    html.Div(id="simulation-progress", className="mt-2"),
                                    dbc.Collapse(
                                        dbc.Card([
                                            dbc.CardHeader([
                                                html.H6("📊 Simulation Progress", className="mb-0"),
                                                dbc.Button(
                                                    "❌ Cancel",
                                                    id="cancel-simulation-btn",
                                                    color="danger",
                                                    size="sm",
                                                    className="float-end"
                                                )
                                            ]),
                                            dbc.CardBody([
                                                dbc.Progress(id="progress-bar", value=0, className="mb-2"),
                                                html.Div([
                                                    html.Small("⏱️ Elapsed: "),
                                                    html.Small(id="elapsed-time", children="0s"),
                                                    html.Small(" | Status: "),
                                                    html.Small(id="status-text", children="Initializing...")
                                                ]),
                                                dbc.Collapse(
                                                    [
                                                        html.Hr(),
                                                        html.H6("📝 Simulation Log", className="mt-2"),
                                                        html.Div(
                                                            id="simulation-log",
                                                            style={
                                                                "height": "200px",
                                                                "overflow-y": "auto",
                                                                "background-color": "#f8f9fa",
                                                                "padding": "10px",
                                                                "border-radius": "5px",
                                                                "font-family": "monospace",
                                                                "font-size": "12px"
                                                            }
                                                        )
                                                    ],
                                                    id="log-collapse",
                                                    is_open=False
                                                ),
                                                dbc.Button(
                                                    "📝 Show/Hide Log",
                                                    id="toggle-log-btn",
                                                    color="secondary",
                                                    size="sm",
                                                    className="mt-2"
                                                )
                                            ])
                                        ]),
                                        id="progress-collapse",
                                        is_open=False
                                    )
                                ])
                            ]
                        ),
                    ]
                ),
            ],
            className="mb-3",
        )

        # Mesh visualization
        mesh_panel = dbc.Card(
            [
                dbc.CardHeader(
                    [
                        html.H5("🕸️ NoC Mesh Topology", className="mb-0"),
                        dbc.Badge("Real-time", color="success", className="ms-2"),
                    ]
                ),
                dbc.CardBody(
                    [
                        dcc.Graph(
                            id="mesh-graph",
                            config={"displayModeBar": False},
                            style={"height": "500px"},
                        )
                    ]
                ),
            ]
        )

        # Statistics panel (expandable)
        stats_panel = dbc.Card(
            [
                dbc.CardHeader(
                    [
                        dbc.Button(
                            [
                                html.I(className="fas fa-chart-bar me-2"),
                                "📊 Performance Statistics",
                            ],
                            id="stats-collapse-btn",
                            color="link",
                            className="text-decoration-none p-0",
                        )
                    ]
                ),
                dbc.Collapse(
                    [
                        dbc.CardBody(
                            [
                                dcc.Graph(
                                    id="performance-graphs",
                                    config={"displayModeBar": False},
                                    style={"height": "300px"},
                                )
                            ]
                        )
                    ],
                    id="stats-collapse",
                    is_open=True,
                ),
            ],
            className="mb-3",
        )

        # Router details panel (expandable)
        router_panel = dbc.Card(
            [
                dbc.CardHeader(
                    [
                        dbc.Button(
                            [
                                html.I(className="fas fa-microchip me-2"),
                                "🔧 Router Details",
                            ],
                            id="router-collapse-btn",
                            color="link",
                            className="text-decoration-none p-0",
                        )
                    ]
                ),
                dbc.Collapse(
                    [dbc.CardBody([html.Div(id="router-details")])],
                    id="router-collapse",
                    is_open=True,
                ),
            ]
        )

        # Main layout
        self.app.layout = dbc.Container(
            [
                header,
                dcc.Interval(
                    id="interval-component", interval=UPDATE_INTERVAL, n_intervals=0
                ),
                dcc.Store(id="simulation-store"),
                dbc.Row(
                    [
                        dbc.Col(
                            [control_panel, stats_panel, router_panel],
                            width=4,
                        ),
                        dbc.Col([mesh_panel], width=8),
                    ]
                ),
            ],
            fluid=True,
        )

    def setup_callbacks(self):
        """Setup Dash callbacks with duplicate registration protection"""
        
        # Prevent duplicate callback registration
        if NebulaDashboardApp._callbacks_registered:
            print("⚠️  Callbacks already registered, skipping duplicate setup")
            return
        
        print("🔧 Setting up dashboard callbacks...")
        NebulaDashboardApp._callbacks_registered = True

        # Main visualization update callback
        @self.app.callback(
            [
                Output("mesh-graph", "figure"),
                Output("performance-graphs", "figure"),
                Output("router-details", "children"),
            ],
            [Input("interval-component", "n_intervals")],
        )
        def update_visualizations(n_intervals):
            # Update simulation if VCD data is loaded
            if self.vcd_events and self.vcd_replay_index < len(self.vcd_events):
                self.update_simulation_from_vcd()

            # Create visualizations
            mesh_fig = self.create_mesh_figure()
            perf_fig = self.create_performance_figure()
            router_details = self.create_router_details()

            return mesh_fig, perf_fig, router_details

        # Comprehensive simulation management callback
        @self.app.callback(
            [
                Output("verilog-status", "children"),
                Output("progress-collapse", "is_open"),
                Output("run-verilog-btn", "disabled"),
                Output("progress-bar", "value"),
                Output("elapsed-time", "children"),
                Output("status-text", "children"),
                Output("simulation-log", "children"),
            ],
            [
                Input("run-verilog-btn", "n_clicks"),
                Input("cancel-simulation-btn", "n_clicks"),
                Input("interval-component", "n_intervals"),
            ],
            [
                State("verilog-pattern", "value"),
                State("verilog-duration", "value"),
            ],
            prevent_initial_call=True,
        )
        def manage_verilog_simulation(run_clicks, cancel_clicks, n_intervals, pattern, duration):
            ctx = callback_context
            
            if not ctx.triggered:
                return "", False, False, 0, "0s", "Idle", ""
                
            trigger_id = ctx.triggered[0]["prop_id"].split(".")[0]
            
            # Handle run button click
            if trigger_id == "run-verilog-btn" and run_clicks:
                if self.simulation_running:
                    return (
                        dbc.Alert(
                            "⏳ Simulation already running! Please wait...",
                            color="warning",
                            className="mt-2",
                        ), 
                        True, True, self.simulation_progress, 
                        self._get_elapsed_time(), 
                        self.simulation_status.replace("_", " ").title(),
                        self._format_log_content()
                    )
                
                if not TRAFFIC_AVAILABLE:
                    return (
                        dbc.Alert(
                            "❌ Traffic generator not available. Install required dependencies.",
                            color="danger",
                            className="mt-2",
                        ), 
                        False, False, 0, "0s", "Error", ""
                    )
                
                # Start simulation
                self.simulation_status = "running"
                self.simulation_progress = 0
                self.simulation_start_time = time.time()
                self.simulation_log = [f"🚀 Starting simulation with {pattern} pattern..."]
                
                # Start simulation in background thread
                threading.Thread(
                    target=self._run_simulation_thread,
                    args=(pattern, duration),
                    daemon=True
                ).start()
                
                return (
                    dbc.Alert(
                        [
                            dbc.Spinner(size="sm"),
                            f"🚀 Starting {pattern} simulation ({duration} cycles)..."
                        ],
                        color="info",
                        className="mt-2",
                    ), 
                    True, True, 0, "0s", "Starting", 
                    self._format_log_content()
                )
            
            # Handle cancel button click
            elif trigger_id == "cancel-simulation-btn" and cancel_clicks:
                if self.simulation_running:
                    self._cancel_simulation()
                    return (
                        dbc.Alert(
                            "🛑 Simulation cancelled by user",
                            color="warning",
                            className="mt-2",
                        ), 
                        False, False, 0, "0s", "Cancelled", ""
                    )
            
            # Handle interval updates (for status monitoring)
            elif trigger_id == "interval-component":
                status_msg, progress_open, btn_disabled = self._get_current_status()
                progress_val = self.simulation_progress if self.simulation_running else 0
                elapsed = self._get_elapsed_time()
                status_text = self.simulation_status.replace("_", " ").title()
                log_content = self._format_log_content()
                
                return status_msg, progress_open, btn_disabled, progress_val, elapsed, status_text, log_content
            
            return "", False, False, 0, "0s", "Idle", ""
        
        # Log toggle callback
        @self.app.callback(
            Output("log-collapse", "is_open"),
            [Input("toggle-log-btn", "n_clicks")],
            [State("log-collapse", "is_open")],
        )
        def toggle_log_display(n_clicks, is_open):
            if n_clicks:
                return not is_open
            return is_open

        # Collapse callbacks
        @self.app.callback(
            Output("stats-collapse", "is_open"),
            [Input("stats-collapse-btn", "n_clicks")],
            [State("stats-collapse", "is_open")],
        )
        def toggle_stats_collapse(n_clicks, is_open):
            if n_clicks:
                return not is_open
            return is_open

        @self.app.callback(
            Output("router-collapse", "is_open"),
            [Input("router-collapse-btn", "n_clicks")],
            [State("router-collapse", "is_open")],
        )
        def toggle_router_collapse(n_clicks, is_open):
            if n_clicks:
                return not is_open
            return is_open

    def load_vcd_file(self, vcd_path: str) -> bool:
        """Load and parse VCD file for visualization"""
        try:
            self.vcd_parser = SimpleVCDParser(vcd_path)
            self.vcd_events = self.vcd_parser.parse_packets()
            self.vcd_replay_index = 0
            logger.info(f"Loaded {len(self.vcd_events)} events from VCD file")
            return True
        except Exception as e:
            logger.error(f"Error loading VCD file: {e}")
            return False

    def run_custom_verilog_simulation(self, testbench_path: str) -> bool:
        """Run Verilog simulation with custom testbench"""
        if not os.path.exists(testbench_path):
            logger.error(f"Testbench file not found: {testbench_path}")
            return False

        try:
            # Change to the code directory to run simulation
            code_dir = os.path.join(
                os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
            )
            build_dir = os.path.join(code_dir, "build")

            # The testbench is already generated in tb/generated/, just run make target
            logger.info(f"Running traffic testbench from {testbench_path}")

            # Run Verilator simulation using the traffic target
            cmd = ["make", "tb_nebula_traffic"]
            logger.info(f"Running: {' '.join(cmd)} in {code_dir}")

            self.verilog_process = subprocess.Popen(
                cmd,
                cwd=code_dir,
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
            )

            stdout, stderr = self.verilog_process.communicate(timeout=120)  # Longer timeout for traffic sim

            if self.verilog_process.returncode == 0:
                logger.info("Verilog simulation completed successfully")
                logger.info(f"Simulation stdout: {stdout}")
                
                # Look for generated VCD file in build directory
                vcd_path = os.path.join(build_dir, "tb_nebula_top.vcd")
                if os.path.exists(vcd_path):
                    return self.load_vcd_file(vcd_path)
                else:
                    logger.error(f"VCD file not found at {vcd_path}")
                    logger.error(f"Build directory contents: {os.listdir(build_dir) if os.path.exists(build_dir) else 'Directory not found'}")
                    return False
            else:
                error_msg = f"Verilog simulation failed with return code {self.verilog_process.returncode}"
                logger.error(error_msg)
                logger.error(f"Simulation stderr: {stderr}")
                logger.error(f"Simulation stdout: {stdout}")
                
                # Store error details for dashboard display
                self.last_simulation_error = {
                    "return_code": self.verilog_process.returncode,
                    "stderr": stderr,
                    "stdout": stdout,
                    "timestamp": time.time()
                }
                return False

        except subprocess.TimeoutExpired:
            logger.error("Verilog simulation timed out")
            if self.verilog_process:
                self.verilog_process.kill()
            return False
        except Exception as e:
            logger.error(f"Error running Verilog simulation: {e}")
            return False

    def generate_traffic_pattern(self) -> Tuple[Optional[str], List]:
        """Generate traffic pattern using the enhanced Python traffic generator"""
        if not TRAFFIC_AVAILABLE:
            logger.error(
                "Traffic generator not available. Install required dependencies."
            )
            return None, []

        try:
            # Convert pattern name to enum
            pattern_name = self.traffic_config["pattern"]
            pattern_enum = TrafficPattern(pattern_name)

            # Create configuration
            config = TrafficConfig(
                mesh_width=self.mesh_width,
                mesh_height=self.mesh_height,
                pattern=pattern_enum,
                injection_rate=self.traffic_config["injection_rate"],
                duration_cycles=self.traffic_config["duration_cycles"],
                packet_size_bytes=self.traffic_config["packet_size"],
                enable_axi=self.traffic_config["enable_axi"],
                enable_chi=self.traffic_config["enable_chi"],
                hotspot_nodes=self.traffic_config.get("hotspot_nodes"),
                hotspot_probability=self.traffic_config.get("hotspot_probability", 0.3),
            )

            # Generate traffic and testbench
            generator = NebulaTrafficGenerator(config)
            
            # Create output directory
            output_dir = os.path.join(
                os.path.dirname(os.path.dirname(os.path.abspath(__file__))),
                "tb", "generated"
            )
            os.makedirs(output_dir, exist_ok=True)

            # Generate testbench and traces
            testbench_path, traces = generator.generate_and_run_simulation(
                pattern_enum, 
                output_dir
            )

            logger.info(f"Generated {len(traces)} traffic traces for pattern: {pattern_name}")
            logger.info(f"Generated testbench: {testbench_path}")
            
            return testbench_path, traces

        except Exception as e:
            logger.error(f"Error generating traffic pattern: {e}")
            return None, []

    def _run_simulation_thread(self, pattern: str, duration: int):
        """Run simulation in background thread with progress updates"""
        try:
            self.simulation_running = True
            self.simulation_status = "running"
            self.simulation_log.append(f"📋 Configuring simulation parameters...")
            
            # Update traffic configuration
            self.traffic_config["pattern"] = pattern
            self.traffic_config["duration_cycles"] = duration
            self.simulation_progress = 10
            
            self.simulation_log.append(f"⚙️ Generating {pattern} traffic pattern...")
            
            # Generate traffic pattern
            testbench_path, traces = self.generate_traffic_pattern()
            if not testbench_path:
                self.simulation_status = "failed"
                self.simulation_log.append("❌ Failed to generate traffic pattern")
                return
            
            self.simulation_progress = 30
            self.simulation_log.append(f"✅ Traffic pattern generated: {len(traces)} traces")
            self.simulation_log.append(f"🔨 Compiling Verilog testbench...")
            
            # Run Verilog simulation
            self.simulation_progress = 50
            success = self.run_custom_verilog_simulation(testbench_path)
            
            if success:
                self.simulation_progress = 90
                self.simulation_log.append("🔄 Converting VCD data...")
                self.convert_vcd_to_workload()
                
                self.simulation_progress = 100
                self.simulation_status = "completed"
                self.simulation_log.append("✅ Simulation completed successfully!")
            else:
                self.simulation_status = "failed"
                self.simulation_log.append("❌ Verilog simulation failed")
                
        except Exception as e:
            self.simulation_status = "failed"
            self.simulation_log.append(f"❌ Error: {str(e)}")
        finally:
            self.simulation_running = False
    
    def _get_elapsed_time(self):
        """Get formatted elapsed time since simulation start."""
        if not self.simulation_start_time:
            return "0s"
        
        elapsed = time.time() - self.simulation_start_time
        return f"{elapsed:.1f}s"
    
    def _format_log_content(self):
        """Format simulation log messages for display."""
        if not self.simulation_log:
            return ""
        
        log_content = []
        for i, msg in enumerate(self.simulation_log[-20:]):  # Show last 20 messages
            log_content.append(html.Div(msg, style={"margin-bottom": "2px"}))
        
        return log_content
    
    def _cancel_simulation(self):
        """Cancel running simulation"""
        if self.verilog_process:
            try:
                self.verilog_process.terminate()
                self.verilog_process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.verilog_process.kill()
            except Exception as e:
                logger.error(f"Error cancelling simulation: {e}")
        
        self.simulation_running = False
        self.simulation_status = "cancelled"
        self.simulation_log.append("🛑 Simulation cancelled by user")
    
    def _get_current_status(self):
        """Get current simulation status for display"""
        if not self.simulation_running and self.simulation_status == "idle":
            return "", False, False
        
        # Create status message based on current state
        if self.simulation_status == "running":
            status_msg = dbc.Alert(
                [
                    dbc.Spinner(size="sm"),
                    f"⚙️ Simulation running... ({self.simulation_progress}% complete)"
                ],
                color="info",
                className="mt-2",
            )
            return status_msg, True, True
            
        elif self.simulation_status == "completed":
            status_msg = dbc.Alert(
                f"✅ Simulation completed successfully! Check the visualization above.",
                color="success",
                className="mt-2",
            )
            # Reset status after showing completion
            if not self.simulation_running:
                self.simulation_status = "idle"
            return status_msg, False, False
            
        elif self.simulation_status == "failed":
            error_details = ""
            if self.last_simulation_error:
                error_details = f" Return code: {self.last_simulation_error['return_code']}"
                if self.last_simulation_error['stderr']:
                    # Show first line of stderr for quick diagnosis
                    first_error_line = self.last_simulation_error['stderr'].split('\n')[0]
                    error_details += f" - {first_error_line[:100]}"
                    
            status_msg = dbc.Alert(
                [
                    "❌ Simulation failed.",
                    html.Br(),
                    html.Small(error_details, className="text-muted") if error_details else "",
                    html.Br(),
                    html.Small("Check the log below for full details.", className="text-muted")
                ],
                color="danger",
                className="mt-2",
            )
            # Reset status after showing failure
            if not self.simulation_running:
                self.simulation_status = "idle"
            return status_msg, False, False
            
        elif self.simulation_status == "cancelled":
            status_msg = dbc.Alert(
                "🛑 Simulation was cancelled",
                color="warning",
                className="mt-2",
            )
            # Reset status after showing cancellation
            self.simulation_status = "idle"
            return status_msg, False, False
        
        return "", False, False

    def run_verilog_simulation_with_traffic(self) -> bool:
        """Generate traffic pattern and run Verilog simulation"""
        if self.simulation_running:
            logger.warning("Simulation already running!")
            return False

        logger.info(
            f"Starting Verilog simulation with {self.traffic_config['pattern']} traffic pattern..."
        )
        self.simulation_running = True

        try:
            # Generate traffic pattern
            testbench_path, traces = self.generate_traffic_pattern()
            if not testbench_path:
                self.simulation_running = False
                return False

            # Run Verilog simulation with custom traffic
            success = self.run_custom_verilog_simulation(testbench_path)

            if success:
                logger.info(
                    "Verilog simulation completed successfully! VCD data loaded."
                )
                # Convert VCD events to workload data for visualization
                self.convert_vcd_to_workload()
                return True
            else:
                logger.error("Verilog simulation failed!")
                return False

        except Exception as e:
            logger.error(f"Error in Verilog simulation: {e}")
            return False
        finally:
            self.simulation_running = False

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
                "packet_type": event.packet_type,
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
        current_time = self.simulation_time
        while (self.vcd_replay_index < len(self.vcd_events) and 
               self.vcd_events[self.vcd_replay_index].timestamp <= current_time):
            
            event = self.vcd_events[self.vcd_replay_index]
            
            # Convert VCD event to packet
            path = self.calculate_xy_route(event.src_x, event.src_y, event.dst_x, event.dst_y)
            
            packet = Packet(
                id=len(self.packets),
                src_x=event.src_x,
                src_y=event.src_y,
                dst_x=event.dst_x,
                dst_y=event.dst_y,
                current_x=float(event.src_x),
                current_y=float(event.src_y),
                path=path,
                hop_index=0,
                packet_type=event.packet_type,
                size_bytes=event.size_bytes,
                timestamp=event.timestamp,
                priority=getattr(event, 'priority', 0)
            )
            
            self.packets.append(packet)
            self.vcd_replay_index += 1

        # Update existing packets
        self.update_packet_positions()

        # Remove completed packets
        self.packets = [p for p in self.packets if p.hop_index < len(p.path)]

        # Limit number of packets for performance
        if len(self.packets) > MAX_PACKETS:
            self.packets = self.packets[-MAX_PACKETS:]

        # Update router statistics
        self.update_router_statistics()

        # Record performance metrics
        self.record_performance_metrics()

        self.simulation_time += 1

    def update_simulation(self, injection_rate: float):
        """Update simulation state"""
        self.simulation_time += 1

        # Inject new packets based on workload (either synthetic or VCD-based)
        new_packets = self.inject_packets_from_workload(injection_rate)
        self.packets.extend(new_packets)

        # Update existing packets
        self.update_packet_positions()

        # Remove completed packets
        self.packets = [p for p in self.packets if p.hop_index < len(p.path)]

        # Limit number of packets for performance
        if len(self.packets) > MAX_PACKETS:
            self.packets = self.packets[-MAX_PACKETS:]

        # Update router statistics
        self.update_router_statistics()

        # Record performance metrics
        self.record_performance_metrics()

    def inject_packets_from_workload(self, injection_rate: float) -> List[Packet]:
        """Inject packets based on current workload"""
        new_packets = []

        # Find workload events for current time
        current_events = [
            event
            for event in self.workload_data
            if event["timestamp"] == self.simulation_time
        ]

        for event in current_events:
            if np.random.random() < injection_rate:
                path = self.calculate_xy_route(
                    event["src_x"], event["src_y"], event["dst_x"], event["dst_y"]
                )

                packet = Packet(
                    id=len(self.packets) + len(new_packets),
                    src_x=event["src_x"],
                    src_y=event["src_y"],
                    dst_x=event["dst_x"],
                    dst_y=event["dst_y"],
                    current_x=float(event["src_x"]),
                    current_y=float(event["src_y"]),
                    path=path,
                    hop_index=0,
                    packet_type=event["packet_type"],
                    size_bytes=event["size_bytes"],
                    timestamp=time.time(),
                    priority=event.get("priority", 0),
                )

                new_packets.append(packet)

        return new_packets

    def calculate_xy_route(
        self, src_x: int, src_y: int, dst_x: int, dst_y: int
    ) -> List[Tuple[int, int]]:
        """Calculate XY routing path"""
        path = [(src_x, src_y)]

        # Move in X direction first
        current_x, current_y = src_x, src_y
        while current_x != dst_x:
            current_x += 1 if dst_x > current_x else -1
            path.append((current_x, current_y))

        # Then move in Y direction
        while current_y != dst_y:
            current_y += 1 if dst_y > current_y else -1
            path.append((current_x, current_y))

        return path

    def update_packet_positions(self):
        """Update positions of all packets"""
        for packet in self.packets:
            if packet.hop_index < len(packet.path) - 1:
                # Move towards next hop
                next_hop = packet.path[packet.hop_index + 1]
                target_x, target_y = next_hop

                # Smooth movement
                speed = 0.2  # Adjust for animation speed
                dx = target_x - packet.current_x
                dy = target_y - packet.current_y

                if abs(dx) < speed and abs(dy) < speed:
                    # Reached next hop
                    packet.current_x = float(target_x)
                    packet.current_y = float(target_y)
                    packet.hop_index += 1
                else:
                    # Move towards target
                    packet.current_x += dx * speed
                    packet.current_y += dy * speed

    def update_router_statistics(self):
        """Update router statistics based on current packets"""
        # Reset utilization
        for stats in self.router_stats.values():
            stats.utilization = 0.0
            stats.congestion_level = 0.0

        # Count packets at each router
        router_packet_count = {}
        for packet in self.packets:
            router_x = int(round(packet.current_x))
            router_y = int(round(packet.current_y))
            router_id = router_y * self.mesh_width + router_x

            if 0 <= router_id < len(self.router_stats):
                router_packet_count[router_id] = (
                    router_packet_count.get(router_id, 0) + 1
                )

        # Update statistics
        for router_id, count in router_packet_count.items():
            if router_id < len(self.router_stats):
                stats = self.router_stats[router_id]
                stats.utilization = min(1.0, count / 5.0)  # Normalize to 0-1
                stats.congestion_level = min(1.0, count / 3.0)
                stats.temperature = 25.0 + stats.utilization * 15.0  # 25-40°C

    def record_performance_metrics(self):
        """Record performance metrics for history"""
        total_packets = len(self.packets)
        avg_utilization = np.mean([stats.utilization for stats in self.router_stats.values()])
        max_congestion = max([stats.congestion_level for stats in self.router_stats.values()])

        self.performance_history.append(
            {
                "time": self.simulation_time,
                "total_packets": total_packets,
                "avg_utilization": avg_utilization,
                "max_congestion": max_congestion,
            }
        )

        # Keep only last 100 points for performance
        if len(self.performance_history) > 100:
            self.performance_history = self.performance_history[-100:]

    def create_mesh_figure(self):
        """Create mesh topology visualization with packets"""
        fig = go.Figure()

        # Add mesh grid
        for x in range(self.mesh_width):
            for y in range(self.mesh_height):
                # Router nodes
                stats = self.router_stats[y * self.mesh_width + x]

                # Color based on utilization
                color_intensity = stats.utilization
                color = f"rgba(255, {int(255 * (1 - color_intensity))}, {int(255 * (1 - color_intensity))}, 0.8)"

                fig.add_trace(
                    go.Scatter(
                        x=[x],
                        y=[y],
                        mode="markers+text",
                        marker=dict(
                            size=40, color=color, line=dict(width=2, color="black")
                        ),
                        text=f"R{stats.node_id}",
                        textposition="middle center",
                        name=f"Router {stats.node_id}",
                        showlegend=False,
                        hovertemplate=f"<b>Router {stats.node_id}</b><br>"
                        + f"Position: ({x}, {y})<br>"
                        + f"Utilization: {stats.utilization:.2f}<br>"
                        + f"Temperature: {stats.temperature:.1f}°C<br>"
                        + f"Packets: {stats.packets_received + stats.packets_sent}<extra></extra>",
                    )
                )

        # Add mesh connections
        for x in range(self.mesh_width):
            for y in range(self.mesh_height):
                # Horizontal connections
                if x < self.mesh_width - 1:
                    fig.add_trace(
                        go.Scatter(
                            x=[x, x + 1],
                            y=[y, y],
                            mode="lines",
                            line=dict(width=2, color="gray"),
                            showlegend=False,
                            hoverinfo="skip",
                        )
                    )

                # Vertical connections
                if y < self.mesh_height - 1:
                    fig.add_trace(
                        go.Scatter(
                            x=[x, x],
                            y=[y, y + 1],
                            mode="lines",
                            line=dict(width=2, color="gray"),
                            showlegend=False,
                            hoverinfo="skip",
                        )
                    )

        # Add packets with translucent paths
        packet_colors = {
            "CONV_DATA": "rgba(0, 100, 255, 0.6)",
            "GRADIENT": "rgba(255, 50, 50, 0.6)",
            "WEIGHT_UPDATE": "rgba(50, 200, 50, 0.6)",
            "default": "rgba(150, 50, 200, 0.6)",
        }

        for packet in self.packets:
            # Draw translucent path
            if len(packet.path) > 1:
                path_x = [p[0] for p in packet.path]
                path_y = [p[1] for p in packet.path]

                color = packet_colors.get(packet.packet_type, packet_colors["default"])

                fig.add_trace(
                    go.Scatter(
                        x=path_x,
                        y=path_y,
                        mode="lines",
                        line=dict(width=3, color=color),
                        showlegend=False,
                        hoverinfo="skip",
                    )
                )

            # Draw packet
            packet_marker_colors = {
                "CONV_DATA": "blue",
                "GRADIENT": "red",
                "WEIGHT_UPDATE": "green",
                "default": "purple",
            }

            fig.add_trace(
                go.Scatter(
                    x=[packet.current_x],
                    y=[packet.current_y],
                    mode="markers",
                    marker=dict(
                        size=12,
                        color=packet_marker_colors.get(
                            packet.packet_type, packet_marker_colors["default"]
                        ),
                        symbol="diamond",
                    ),
                    name=packet.packet_type,
                    showlegend=False,
                    hovertemplate=f"<b>Packet {packet.id}</b><br>"
                    + f"Type: {packet.packet_type}<br>"
                    + f"Source: ({packet.src_x}, {packet.src_y})<br>"
                    + f"Destination: ({packet.dst_x}, {packet.dst_y})<br>"
                    + f"Size: {packet.size_bytes} bytes<extra></extra>",
                )
            )

        # Update layout
        fig.update_layout(
            title="NoC Mesh with Real-time Packet Flow",
            xaxis=dict(
                title="X Position",
                range=[-0.5, self.mesh_width - 0.5],
                showgrid=True,
                gridcolor="lightgray",
            ),
            yaxis=dict(
                title="Y Position",
                range=[-0.5, self.mesh_height - 0.5],
                showgrid=True,
                gridcolor="lightgray",
            ),
            plot_bgcolor="white",
            height=500,
            margin=dict(l=50, r=50, t=50, b=50),
        )

        return fig

    def create_performance_figure(self):
        """Create performance monitoring graphs"""
        if not self.performance_history:
            return go.Figure()

        df = pd.DataFrame(self.performance_history)

        fig = make_subplots(
            rows=2,
            cols=2,
            subplot_titles=(
                "Packet Count",
                "Average Utilization",
                "Max Congestion",
                "Throughput",
            ),
            specs=[
                [{"type": "scatter"}, {"type": "scatter"}],
                [{"type": "scatter"}, {"type": "bar"}],
            ],
        )

        # Packet count over time
        fig.add_trace(
            go.Scatter(
                x=df["time"],
                y=df["total_packets"],
                mode="lines+markers",
                name="Packets",
                line=dict(color="blue"),
            ),
            row=1,
            col=1,
        )

        # Average utilization
        fig.add_trace(
            go.Scatter(
                x=df["time"],
                y=df["avg_utilization"],
                mode="lines+markers",
                name="Utilization",
                line=dict(color="green"),
            ),
            row=1,
            col=2,
        )

        # Max congestion
        fig.add_trace(
            go.Scatter(
                x=df["time"],
                y=df["max_congestion"],
                mode="lines+markers",
                name="Congestion",
                line=dict(color="red"),
            ),
            row=2,
            col=1,
        )

        # Router utilization bar chart
        router_utils = [stats.utilization for stats in self.router_stats.values()]
        router_ids = [f"R{i}" for i in range(len(self.router_stats))]

        fig.add_trace(
            go.Bar(
                x=router_ids,
                y=router_utils,
                name="Router Utilization",
                marker_color="orange",
            ),
            row=2,
            col=2,
        )

        fig.update_layout(
            height=300, showlegend=False, margin=dict(l=20, r=20, t=40, b=20)
        )

        return fig

    def create_router_details(self):
        """Create detailed router information table"""
        table_data = []

        for stats in self.router_stats.values():
            table_data.append(
                {
                    "Router": f"R{stats.node_id}",
                    "Position": f"({stats.x}, {stats.y})",
                    "Utilization": f"{stats.utilization:.2f}",
                    "Temperature": f"{stats.temperature:.1f}°C",
                    "Packets RX": stats.packets_received,
                    "Packets TX": stats.packets_sent,
                    "Bytes": f"{stats.bytes_processed:,}",
                }
            )

        if not table_data:
            return html.P("No router data available")

        df = pd.DataFrame(table_data)

        return dbc.Table.from_dataframe(
            df, striped=True, bordered=True, hover=True, responsive=True, size="sm"
        )

    def run(self, debug=False, port=8050):
        """Run the dashboard"""
        logger.info(f"Starting Nebula Dashboard on http://localhost:{port}")
        
        # Suppress Flask development server warnings
        import sys
        if not debug:
            import logging
            log = logging.getLogger('werkzeug')
            log.disabled = True
            
        # Also disable Flask's click echo
        os.environ['WERKZEUG_RUN_MAIN'] = 'true'
        
        self.app.run(debug=debug, port=port, host="0.0.0.0")


def main():
    """Main entry point"""
    print("🚀 Starting Nebula GPU Interconnect Dashboard")
    print("=" * 50)

    if not TRAFFIC_AVAILABLE:
        print("⚠️  Warning: Traffic generation features may be limited")
        print("   Install missing packages: pip install matplotlib seaborn pandas")

    dashboard = NebulaDashboardApp()

    print("🌐 Dashboard will be available at:")
    print("   http://localhost:8050")
    print("   http://0.0.0.0:8050 (network accessible)")
    print("")
    print("Features:")
    print("✅ Modern web-based interface")
    print("✅ Real-time mesh visualization")
    print("✅ Translucent packet paths")
    print("✅ CNN training workload simulation")
    print("✅ Expandable information panels")
    print("✅ High-performance animation")

    dashboard.run(debug=False)


if __name__ == "__main__":
    main()
