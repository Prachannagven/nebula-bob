# Nebula Dashboard - Flask + Vite

A minimal web-based dashboard for the Nebula GPU Interconnect NoC system, replacing the previous Dash implementation.

## Architecture

- **Backend**: Flask with Socket.IO for real-time updates
- **Frontend**: Vanilla JavaScript with Vite build system and Tailwind CSS
- **Visualization**: SVG-based mesh topology rendering
- **Simulation**: Integration with existing Verilog simulation pipeline

## Features

- 🚀 **Real-time NoC mesh visualization** - Interactive SVG-based topology view
- 🔧 **Verilog simulation interface** - Direct integration with existing testbenches
- 📊 **Performance monitoring** - Router utilization, congestion, temperature tracking
- 🎯 **Traffic pattern generation** - Support for various GPU workload patterns
- 🌐 **WebSocket updates** - Real-time data streaming
- 📱 **Responsive design** - Works on desktop and mobile devices

## Quick Start

```bash
# Setup (run once)
chmod +x setup.sh start.sh
./setup.sh

# Start dashboard
./start.sh
```

Dashboard will be available at: http://localhost:5000

## Development

### Backend Development
```bash
cd backend
source venv/bin/activate
python app.py
```

### Frontend Development
```bash
cd frontend
npm run dev  # Development server at http://localhost:3000
```

## API Endpoints

- `GET /api/status` - Dashboard and simulation status
- `GET /api/mesh` - Current mesh topology and packet data
- `GET /api/performance` - Performance metrics and history
- `POST /api/simulation/start` - Start Verilog simulation
- `POST /api/simulation/cancel` - Cancel running simulation
- `GET /api/simulation/log` - Get simulation log entries

## WebSocket Events

- `simulation_status` - Simulation state changes
- `simulation_progress` - Progress updates during simulation
- `mesh_update` - Real-time mesh data updates

## Traffic Patterns

The dashboard supports various traffic patterns for GPU workload simulation:

- 🎲 **Uniform Random** - Random source-destination pairs
- 🔥 **Hotspot** - Concentrated traffic to specific nodes
- ↔️ **Transpose** - Bit-reverse addressing pattern
- 🧠 **CNN Training** - Convolutional neural network training patterns
- 🔢 **Matrix Multiply** - Dense matrix computation patterns
- 🤖 **Transformer** - Attention mechanism communication patterns
- 🌪️ **Tornado** - Permutation-based traffic pattern
- 📈 **Bit Complement** - Complement-based addressing

## Directory Structure

```
web_dashboard/
├── backend/
│   ├── app.py              # Flask application
│   ├── requirements.txt    # Python dependencies
│   └── venv/              # Python virtual environment
├── frontend/
│   ├── src/
│   │   ├── main.js        # Main JavaScript application
│   │   └── style.css      # Tailwind CSS styles
│   ├── index.html         # Main HTML template
│   ├── package.json       # Node.js dependencies
│   ├── vite.config.js     # Vite configuration
│   ├── tailwind.config.js # Tailwind configuration
│   └── dist/              # Built frontend files
├── setup.sh              # Setup script
├── start.sh               # Start script
└── README.md             # This file
```

## Integration with Existing System

The dashboard integrates with the existing Nebula NoC system:

- Uses existing traffic generators from `code/python/nebula_traffic_generator.py`
- Runs Verilog simulations using existing Makefiles in `code/`
- Parses VCD files using existing `code/python/nebula_vcd_parser.py`
- Generates testbenches in `code/tb/generated/`

## Dependencies

### Backend
- Flask 2.3.3
- Flask-CORS 4.0.0
- Flask-SocketIO 5.3.6
- Python 3.7+

### Frontend
- Vite 4.4.5
- Tailwind CSS 3.3.0
- Socket.IO Client 4.7.2
- Node.js 16+

## Troubleshooting

### Port Already in Use
```bash
# Kill existing processes
pkill -f "python.*app.py"
lsof -ti:5000 | xargs kill
```

### Virtual Environment Issues
```bash
cd backend
rm -rf venv
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt
```

### Frontend Build Issues
```bash
cd frontend
rm -rf node_modules package-lock.json
npm install
npm run build
```

## Performance

- Minimal UI footprint with vanilla JavaScript
- Efficient SVG rendering for mesh visualization
- WebSocket-based real-time updates
- Optimized for low-latency simulation monitoring

## License

Same as the main Nebula project.
