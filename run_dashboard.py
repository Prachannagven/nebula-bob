#!/usr/bin/env python3
"""
Nebula Dashboard Runner

Run this script to start the new Flask-based dashboard.
"""

import sys
import os
import subprocess

# Add the project root to Python path
project_root = os.path.dirname(os.path.abspath(__file__))
web_dashboard_dir = os.path.join(project_root, "web_dashboard")


def main():
    print("🚀 Starting Nebula GPU Interconnect Dashboard (Flask Version)")
    print("📍 Project root:", project_root)
    print("🔧 New Flask dashboard will be available at: http://localhost:5000")
    print("💡 Dashboard features:")
    print("   - Minimal Flask + Vite frontend")
    print("   - Real-time WebSocket updates")
    print("   - SVG-based mesh visualization")
    print("   - Verilog simulation interface")
    print()

    # Check if web dashboard exists
    if not os.path.exists(web_dashboard_dir):
        print("❌ Web dashboard directory not found!")
        print(f"Expected: {web_dashboard_dir}")
        print("💡 The new Flask dashboard should be in the web_dashboard/ directory")
        sys.exit(1)

    # Check if setup was run
    backend_dir = os.path.join(web_dashboard_dir, "backend")
    venv_dir = os.path.join(backend_dir, "venv")

    if not os.path.exists(venv_dir):
        print("⚠️  Flask dashboard not set up yet!")
        print("🔧 Running setup...")

        setup_script = os.path.join(web_dashboard_dir, "setup.sh")
        try:
            result = subprocess.run(
                ["/bin/bash", setup_script],
                cwd=web_dashboard_dir,
                check=True,
                capture_output=True,
                text=True,
            )
            print("✅ Setup completed successfully!")
        except subprocess.CalledProcessError as e:
            print(f"❌ Setup failed: {e}")
            print("stdout:", e.stdout)
            print("stderr:", e.stderr)
            sys.exit(1)

    # Start the Flask dashboard
    print("🚀 Starting Flask dashboard...")
    start_script = os.path.join(web_dashboard_dir, "start.sh")

    try:
        # Run the start script
        subprocess.run(["/bin/bash", start_script], cwd=web_dashboard_dir, check=True)
    except subprocess.CalledProcessError as e:
        print(f"❌ Error starting dashboard: {e}")
        print("💡 You can also manually start the dashboard:")
        print(f"   cd {web_dashboard_dir}")
        print("   ./start.sh")
        sys.exit(1)
    except KeyboardInterrupt:
        print("\n🛑 Dashboard stopped by user")
        sys.exit(0)


if __name__ == "__main__":
    main()
