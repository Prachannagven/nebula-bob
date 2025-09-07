#!/usr/bin/env python3
"""
Nebula VCD Parser

Simple VCD file parser for the Nebula dashboard that extracts
router and packet information from Verilog simulation traces.
"""

import re
import os
from typing import Dict, List, Tuple, Optional
from dataclasses import dataclass


@dataclass
class VCDSignal:
    """VCD signal information"""

    identifier: str
    name: str
    size: int
    value: str = "x"
    timestamp: int = 0


@dataclass
class PacketEvent:
    """Packet event extracted from VCD"""

    timestamp: int
    router_id: int
    event_type: str  # "inject", "forward", "arrive"
    src_x: int = 0
    src_y: int = 0
    dst_x: int = 0
    dst_y: int = 0
    packet_id: int = 0


class SimpleVCDParser:
    """Simple VCD parser focused on Nebula router signals"""

    def __init__(self, filepath: str):
        self.filepath = filepath
        self.signals = {}
        self.time_events = []
        self.packet_events = []
        self.current_time = 0
        self.scope_stack = []
        self.signal_hierarchy = {}

    def parse(self) -> bool:
        """Parse VCD file and extract relevant signals"""
        try:
            with open(self.filepath, "r") as f:
                content = f.read()

            # Parse header section
            self._parse_header(content)

            # Parse value changes
            self._parse_values(content)

            # Extract packet events
            self._extract_packet_events()

            return True

        except Exception as e:
            print(f"Error parsing VCD file: {e}")
            return False

    def _parse_header(self, content: str):
        """Parse VCD header to extract signal definitions with scope hierarchy"""
        lines = content.split("\n")
        in_header = True

        for line in lines:
            line = line.strip()

            if line == "$enddefinitions $end":
                in_header = False
                continue

            if not in_header:
                break

            # Track scope hierarchy
            if line.startswith("$scope"):
                parts = line.split()
                if len(parts) >= 3:
                    scope_name = parts[2]
                    self.scope_stack.append(scope_name)

            elif line.startswith("$upscope"):
                if self.scope_stack:
                    self.scope_stack.pop()

            # Parse variable definitions
            elif line.startswith("$var"):
                parts = line.split()
                if len(parts) >= 5:
                    var_type = parts[1]
                    size = int(parts[2])
                    identifier = parts[3]
                    name = parts[4]

                    # Create full hierarchical name
                    full_name = ".".join(self.scope_stack + [name])

                    self.signals[identifier] = VCDSignal(
                        identifier=identifier, name=name, size=size
                    )

                    # Store hierarchical mapping
                    self.signal_hierarchy[identifier] = full_name

    def _parse_values(self, content: str):
        """Parse value change section"""
        lines = content.split("\n")
        in_values = False

        for line in lines:
            line = line.strip()

            if line == "$enddefinitions $end":
                in_values = True
                continue

            if not in_values or not line:
                continue

            # Parse timestamp
            if line.startswith("#"):
                try:
                    self.current_time = int(line[1:])
                except ValueError:
                    continue

            # Parse value changes
            elif line and line[0] in "01xz":
                # Single bit value
                value = line[0]
                identifier = line[1:]
                if identifier in self.signals:
                    self.time_events.append((self.current_time, identifier, value))
                    self.signals[identifier].value = value
                    self.signals[identifier].timestamp = self.current_time

            elif line.startswith("b"):
                # Multi-bit value
                parts = line.split()
                if len(parts) >= 2:
                    value = parts[0][1:]  # Remove 'b' prefix
                    identifier = parts[1]
                    if identifier in self.signals:
                        self.time_events.append((self.current_time, identifier, value))
                        self.signals[identifier].value = value
                        self.signals[identifier].timestamp = self.current_time

    def _extract_packet_events(self):
        """Extract packet injection/forwarding events from signal changes"""
        # Look for router-related signals using hierarchical names
        router_signals = {}

        for sig_id, signal in self.signals.items():
            # Get full hierarchical name
            full_name = self.signal_hierarchy.get(sig_id, signal.name).lower()

            # Extract router information from hierarchical names
            # Look for patterns like: router_flit_in[0], router_flit_out[0], etc.
            router_match = re.search(r"router_flit_(?:in|out)\[(\d+)\]", full_name)
            if router_match:
                router_id = int(router_match.group(1))
                
                if router_id not in router_signals:
                    router_signals[router_id] = {}

                # Look for flit valid and data signals
                if "router_flit_in_valid" in full_name:
                    router_signals[router_id]["input_valid"] = sig_id
                elif "router_flit_out_valid" in full_name:
                    router_signals[router_id]["output_valid"] = sig_id
                elif "router_flit_in[" in full_name and "valid" not in full_name:
                    router_signals[router_id]["input_flit"] = sig_id
                elif "router_flit_out[" in full_name and "valid" not in full_name:
                    router_signals[router_id]["output_flit"] = sig_id
                continue

            # Also look for the old pattern in case it exists
            # Look for patterns like: tb_nebula_top.dut.gen_nodes[0].router_inst.flit_out_valid
            router_match = re.search(r"gen_(?:mesh_)?nodes?\[(\d+)\].*router", full_name)
            if not router_match:
                continue

            router_id = int(router_match.group(1))

            if router_id not in router_signals:
                router_signals[router_id] = {}

            # Look for flit valid and data signals
            if "flit_in_valid" in full_name:
                router_signals[router_id]["input_valid"] = sig_id
            elif "flit_out_valid" in full_name:
                router_signals[router_id]["output_valid"] = sig_id
            elif (
                "flit_in" in full_name
                and "valid" not in full_name
                and "ready" not in full_name
            ):
                router_signals[router_id]["input_flit"] = sig_id
            elif (
                "flit_out" in full_name
                and "valid" not in full_name
                and "ready" not in full_name
            ):
                router_signals[router_id]["output_flit"] = sig_id
            elif "vc_state" in full_name:
                router_signals[router_id]["vc_state"] = sig_id

        print(f"Found router signals for routers: {list(router_signals.keys())}")

        # Analyze signal changes to identify packet events
        for timestamp, sig_id, value in self.time_events:
            signal = self.signals[sig_id]

            # Find which router this signal belongs to
            for router_id, signals in router_signals.items():
                if sig_id in signals.values():
                    # Check for packet injection (input_valid going high)
                    if (
                        sig_id == signals.get("input_valid") and "1" in value
                    ):  # Handle multi-bit signals

                        event = PacketEvent(
                            timestamp=timestamp,
                            router_id=router_id,
                            event_type="inject",
                            packet_id=len(self.packet_events),
                        )
                        self.packet_events.append(event)

                    # Check for packet forwarding (output_valid going high)
                    elif (
                        sig_id == signals.get("output_valid") and "1" in value
                    ):  # Handle multi-bit signals

                        event = PacketEvent(
                            timestamp=timestamp,
                            router_id=router_id,
                            event_type="forward",
                            packet_id=len(self.packet_events),
                        )
                        self.packet_events.append(event)

    def get_router_activity(self) -> Dict[int, List[Tuple[int, str]]]:
        """Get activity timeline for each router"""
        activity = {}

        for event in self.packet_events:
            if event.router_id not in activity:
                activity[event.router_id] = []

            activity[event.router_id].append((event.timestamp, event.event_type))

        return activity

    def get_packet_count(self) -> int:
        """Get total number of packet events"""
        return len(self.packet_events)

    def get_simulation_duration(self) -> int:
        """Get total simulation time"""
        if self.time_events:
            return max(event[0] for event in self.time_events)
        return 0

    def get_router_utilization(self, router_id: int) -> float:
        """Calculate utilization for a specific router"""
        if not self.packet_events:
            return 0.0

        router_events = [e for e in self.packet_events if e.router_id == router_id]
        total_events = len(self.packet_events)

        if total_events == 0:
            return 0.0

        return len(router_events) / total_events


def test_vcd_parser():
    """Test the VCD parser with a sample file"""
    print("Testing VCD parser...")

    # Create a simple test VCD file
    test_vcd = """$version Generated by Verilator $end
$date Sat Sep  6 21:23:45 2025 $end
$comment
 Traced by Verilator
$end
$timescale 1ps $end

$scope module tb_nebula_top $end
$scope module dut $end
$scope module gen_mesh_nodes[0] $end
$scope module router_inst $end
$var wire 1 ! clk $end
$var wire 1 " rst_n $end
$var wire 1 # flit_in_valid[0] $end
$var wire 1 $ flit_out_valid[0] $end
$var wire 256 % flit_in[0] $end
$var wire 256 & flit_out[0] $end
$upscope $end
$upscope $end
$scope module gen_mesh_nodes[1] $end
$scope module router_inst $end
$var wire 1 ' flit_in_valid[0] $end
$var wire 1 ( flit_out_valid[0] $end
$upscope $end
$upscope $end
$upscope $end
$upscope $end
$enddefinitions $end

#0
0!
0"
0#
0$
0'
0(
b0 %
b0 &

#1000
1!

#2000
0!
1"

#3000
1!
1#
b10101010 %

#4000
0!
1$
b11110000 &

#5000
1!
0#
1'

#6000
0!
1(

#7000
1!
"""

    # Write test file
    test_file = "test_trace.vcd"
    with open(test_file, "w") as f:
        f.write(test_vcd)

    # Parse it
    parser = SimpleVCDParser(test_file)
    if parser.parse():
        print(f"✅ Parsed {len(parser.signals)} signals")
        print(f"✅ Found {len(parser.time_events)} time events")
        print(f"✅ Extracted {len(parser.packet_events)} packet events")
        print(f"✅ Simulation duration: {parser.get_simulation_duration()} ps")

        # Show router activity
        activity = parser.get_router_activity()
        for router_id, events in activity.items():
            print(f"Router {router_id}: {len(events)} events")

    # Cleanup
    os.remove(test_file)


if __name__ == "__main__":
    test_vcd_parser()
