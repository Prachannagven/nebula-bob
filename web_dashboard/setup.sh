#!/bin/bash

echo "🚀 Setting up Nebula Dashboard"
echo "=============================="

# Create virtual environment for backend if it doesn't exist
if [ ! -d "backend/venv" ]; then
    echo "📦 Creating Python virtual environment..."
    cd backend
    python3 -m venv venv
    source venv/bin/activate
    pip install -r requirements.txt
    cd ..
fi

# Install frontend dependencies
echo "📦 Installing frontend dependencies..."
if command -v npm &> /dev/null; then
    cd frontend
    npm install
    echo "🏗️  Building frontend..."
    npm run build
    cd ..
else
    echo "❌ npm not found. Please install Node.js first:"
    echo "   curl -fsSL https://deb.nodesource.com/setup_20.x | sudo -E bash -"
    echo "   sudo apt-get install nodejs -y"
    exit 1
fi

echo ""
echo "✅ Setup complete!"
echo ""
echo "To start the dashboard:"
echo "1. Backend:  cd backend && source venv/bin/activate && python app.py"
echo "2. Frontend: cd frontend && npm run dev (for development)"
echo ""
echo "🌐 Dashboard will be available at:"
echo "   - Production: http://localhost:5000"
echo "   - Development: http://localhost:3000"
