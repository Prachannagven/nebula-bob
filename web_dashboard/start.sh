#!/bin/bash

echo "🚀 Starting Nebula Dashboard"
echo "============================"

# Function to check if port is in use
check_port() {
    local port=$1
    if lsof -Pi :$port -sTCP:LISTEN -t >/dev/null ; then
        echo "⚠️  Port $port is already in use"
        return 1
    fi
    return 0
}

# Kill any existing dashboard processes
echo "🧹 Cleaning up existing processes..."
pkill -f "python.*app.py" 2>/dev/null || true
pkill -f "npm.*run.*dev" 2>/dev/null || true

# Check ports
if ! check_port 5000; then
    echo "Please stop the service using port 5000 and try again"
    exit 1
fi

# Start backend
echo "🔧 Starting Flask backend..."
cd backend

if [ ! -d "venv" ]; then
    echo "❌ Virtual environment not found. Please run setup.sh first"
    exit 1
fi

source venv/bin/activate
python app.py &
BACKEND_PID=$!

cd ..

echo "⏳ Waiting for backend to start..."
sleep 3

# Check if backend is running
if ! curl -s http://localhost:5000/api/status > /dev/null; then
    echo "❌ Backend failed to start"
    kill $BACKEND_PID 2>/dev/null || true
    exit 1
fi

echo "✅ Backend started successfully (PID: $BACKEND_PID)"
echo ""
echo "🌐 Dashboard is now available at:"
echo "   http://localhost:5000"
echo ""
echo "💡 Features:"
echo "   - Real-time mesh visualization"
echo "   - Verilog simulation interface"
echo "   - Performance monitoring"
echo "   - Traffic pattern generation"
echo ""
echo "Press Ctrl+C to stop the dashboard"

# Function to cleanup on exit
cleanup() {
    echo ""
    echo "🛑 Stopping dashboard..."
    kill $BACKEND_PID 2>/dev/null || true
    echo "✅ Dashboard stopped"
    exit 0
}

# Set trap to cleanup on exit
trap cleanup SIGINT SIGTERM

# Wait for backend process
wait $BACKEND_PID
