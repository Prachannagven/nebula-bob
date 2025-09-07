import { io } from "socket.io-client";

// Dashboard state
const state = {
  socket: null,
  meshData: { routers: [], packets: [], mesh_width: 4, mesh_height: 4 },
  simulationRunning: false,
  meshSvg: null,
  vcdEvents: [],
  vcdReplayIndex: 0,
  vcdReplayActive: false,
  vcdReplayTime: 0,
  vcdReplaySpeed: 1.0,
  animatedPackets: [],
  performanceHistory: {
    utilization: [],
    congestion: [],
    temperature: [],
    throughput: []
  },
  lastUpdateTime: Date.now(),
};

// Initialize the dashboard
document.addEventListener("DOMContentLoaded", () => {
  initializeWebSocket();
  setupEventListeners();
  initializeMeshVisualization();
  fetchInitialData();
  startAnimationLoop();
});

// WebSocket connection
function initializeWebSocket() {
  state.socket = io();

  state.socket.on("connect", () => {
    console.log("Connected to server");
    updateConnectionStatus(true);
  });

  state.socket.on("disconnect", () => {
    console.log("Disconnected from server");
    updateConnectionStatus(false);
  });

  state.socket.on("simulation_status", (data) => {
    updateSimulationStatus(data);
  });

  state.socket.on("simulation_progress", (data) => {
    updateProgress(data.progress);
  });

  state.socket.on("simulation_log_update", (data) => {
    appendToSimulationLog(data.log);
  });

  state.socket.on("mesh_update", (data) => {
    state.meshData = data;
    updateMeshVisualization();
    updatePerformanceMetrics();
  });
}

// Event listeners
function setupEventListeners() {
  const startBtn = document.getElementById("startSimBtn");
  const cancelBtn = document.getElementById("cancelSimBtn");
  const refreshVcdBtn = document.getElementById("refreshVcdBtn");
  const loadVcdBtn = document.getElementById("loadVcdBtn");
  const vcdFileSelect = document.getElementById("vcdFileSelect");

  startBtn.addEventListener("click", startSimulation);
  cancelBtn.addEventListener("click", cancelSimulation);
  refreshVcdBtn.addEventListener("click", refreshVcdFiles);
  loadVcdBtn.addEventListener("click", loadSelectedVcdFile);
  vcdFileSelect.addEventListener("change", () => {
    const selected = vcdFileSelect.value;
    loadVcdBtn.disabled = !selected;
  });
}

// Fetch initial data
async function fetchInitialData() {
  try {
    const response = await fetch("/api/status");
    const data = await response.json();
    updateDashboardStatus(data);

    const meshResponse = await fetch("/api/mesh");
    const meshData = await meshResponse.json();
    state.meshData = meshData;
    updateMeshVisualization();
    
    // Load available VCD files
    refreshVcdFiles();
  } catch (error) {
    console.error("Error fetching initial data:", error);
  }
}

// Simulation controls
async function startSimulation() {
  const pattern = document.getElementById("patternSelect").value;
  const duration = parseInt(document.getElementById("durationInput").value);

  try {
    const response = await fetch("/api/simulation/start", {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ pattern, duration }),
    });

    if (response.ok) {
      state.simulationRunning = true;
      updateSimulationUI(true);
      showStatus("Simulation started...", "info");
    } else {
      const error = await response.json();
      showStatus(`Error: ${error.error}`, "error");
    }
  } catch (error) {
    console.error("Error starting simulation:", error);
    showStatus("Failed to start simulation", "error");
  }
}

async function cancelSimulation() {
  try {
    const response = await fetch("/api/simulation/cancel", { method: "POST" });
    if (response.ok) {
      state.simulationRunning = false;
      updateSimulationUI(false);
      showStatus("Simulation cancelled", "warning");
    }
  } catch (error) {
    console.error("Error cancelling simulation:", error);
  }
}

// VCD File Management
async function refreshVcdFiles() {
  try {
    const response = await fetch("/api/vcd/files");
    if (response.ok) {
      const data = await response.json();
      populateVcdFileSelect(data.vcd_files);
      showVcdStatus(`Found ${data.count} VCD files`, "info");
    } else {
      showVcdStatus("Error loading VCD files", "error");
    }
  } catch (error) {
    console.error("Error fetching VCD files:", error);
    showVcdStatus("Failed to load VCD files", "error");
  }
}

function populateVcdFileSelect(vcdFiles) {
  const select = document.getElementById("vcdFileSelect");
  const loadBtn = document.getElementById("loadVcdBtn");
  
  // Clear existing options
  select.innerHTML = '<option value="">Select a VCD file...</option>';
  
  // Add VCD files
  vcdFiles.forEach(file => {
    const option = document.createElement("option");
    option.value = file.name;
    option.textContent = `${file.name} (${file.readable_size}, ${file.readable_time})`;
    select.appendChild(option);
  });
  
  // Disable load button until selection is made
  loadBtn.disabled = true;
}

async function loadSelectedVcdFile() {
  const select = document.getElementById("vcdFileSelect");
  const selectedFile = select.value;
  
  if (!selectedFile) {
    showVcdStatus("Please select a VCD file", "warning");
    return;
  }
  
  try {
    showVcdStatus("Loading VCD file...", "info");
    const response = await fetch("/api/vcd/load", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
      },
      body: JSON.stringify({ file: selectedFile }),
    });
    
    if (response.ok) {
      const data = await response.json();
      showVcdStatus(`✅ ${data.message}`, "success");
      
      // Fetch and display VCD events
      await fetchVcdEvents();
      
      // Show VCD replay controls
      showVcdReplayControls();
      
      // Refresh mesh visualization with VCD data
      updateMeshVisualization();
      updatePerformanceMetrics();
    } else {
      const error = await response.json();
      showVcdStatus(`Error: ${error.error}`, "error");
    }
  } catch (error) {
    console.error("Error loading VCD file:", error);
    showVcdStatus("Failed to load VCD file", "error");
  }
}

function showVcdStatus(message, type) {
  const statusDiv = document.getElementById("vcdStatus");
  statusDiv.textContent = message;
  statusDiv.classList.remove("hidden");
  
  // Remove previous type classes
  statusDiv.classList.remove("text-green-600", "text-red-600", "text-yellow-600", "text-blue-600");
  
  // Add appropriate color based on type
  switch (type) {
    case "success":
      statusDiv.classList.add("text-green-600");
      break;
    case "error":
      statusDiv.classList.add("text-red-600");
      break;
    case "warning":
      statusDiv.classList.add("text-yellow-600");
      break;
    case "info":
    default:
      statusDiv.classList.add("text-blue-600");
      break;
  }
  
  // Auto-hide after 5 seconds for non-error messages
  if (type !== "error") {
    setTimeout(() => {
      statusDiv.classList.add("hidden");
    }, 5000);
  }
}

// VCD event management
async function fetchVcdEvents() {
  try {
    const response = await fetch("/api/simulation/vcd");
    if (response.ok) {
      const data = await response.json();
      state.vcdEvents = data.events || [];
      state.vcdReplayIndex = data.replay_index || 0;
      
      console.log(`Loaded ${state.vcdEvents.length} VCD events`);
      
      // Create default mesh topology if needed for VCD visualization
      ensureMeshTopology();
      
      updateVcdEventDisplay();
    }
  } catch (error) {
    console.error("Error fetching VCD events:", error);
  }
}

function ensureMeshTopology() {
  // If no routers exist, create a default 4x4 mesh for VCD visualization
  if (!state.meshData.routers || state.meshData.routers.length === 0) {
    const routers = [];
    for (let i = 0; i < 16; i++) {
      routers.push({
        node_id: i,
        x: i % 4,
        y: Math.floor(i / 4),
        utilization: 0,
        congestion_level: 0,
        temperature: 25,
      });
    }
    state.meshData.routers = routers;
    state.meshData.mesh_width = 4;
    state.meshData.mesh_height = 4;
  }
}

function showVcdReplayControls() {
  const controlsDiv = document.getElementById("vcdReplayControls");
  if (controlsDiv) {
    controlsDiv.classList.remove("hidden");
  }
}

function updateVcdEventDisplay() {
  const eventCountDiv = document.getElementById("vcdEventCount");
  const replayIndexDiv = document.getElementById("vcdReplayIndex");
  
  if (eventCountDiv) {
    eventCountDiv.textContent = `${state.vcdEvents?.length || 0} events loaded`;
  }
  
  if (replayIndexDiv) {
    replayIndexDiv.textContent = `Event ${state.vcdReplayIndex + 1} of ${state.vcdEvents?.length || 0}`;
  }
}

async function controlVcdReplay(action, index = null) {
  try {
    // Handle client-side animations for some actions
    if (action === "play") {
      startVcdReplay();
      return;
    } else if (action === "pause") {
      stopVcdReplay();
      return;
    } else if (action === "reset") {
      resetVcdReplay();
      // Also notify backend
    }
    
    const payload = { action };
    if (index !== null) {
      payload.index = index;
    }
    
    const response = await fetch("/api/simulation/vcd/replay", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
      },
      body: JSON.stringify(payload),
    });
    
    if (response.ok) {
      const data = await response.json();
      state.vcdReplayIndex = data.replay_index;
      
      // Update animation state
      if (action === "jump" || action === "step") {
        if (state.vcdEvents && state.vcdEvents[state.vcdReplayIndex]) {
          state.vcdReplayTime = state.vcdEvents[state.vcdReplayIndex].timestamp;
        }
      }
      
      updateVcdEventDisplay();
      updateMeshVisualization();
    }
  } catch (error) {
    console.error("Error controlling VCD replay:", error);
  }
}

function jumpToEventIndex() {
  const input = document.getElementById("jumpToEvent");
  const index = parseInt(input.value);
  
  if (!isNaN(index) && index >= 0 && index < (state.vcdEvents?.length || 0)) {
    controlVcdReplay('jump', index);
  } else {
    alert(`Please enter a valid event index between 0 and ${(state.vcdEvents?.length || 1) - 1}`);
  }
}

function toggleVcdReplay() {
  const btn = document.getElementById("playPauseBtn");
  if (state.vcdReplayActive) {
    stopVcdReplay();
    btn.textContent = "▶️";
    btn.title = "Play animation";
  } else {
    startVcdReplay();
    btn.textContent = "⏸️";
    btn.title = "Pause animation";
  }
}

function jumpToEnd() {
  if (state.vcdEvents && state.vcdEvents.length > 0) {
    controlVcdReplay('jump', state.vcdEvents.length - 1);
  }
}

function updateReplaySpeed(speed) {
  state.vcdReplaySpeed = parseFloat(speed);
  document.getElementById("speedDisplay").textContent = `${speed}x`;
}

// Make functions globally available
window.controlVcdReplay = controlVcdReplay;
window.jumpToEventIndex = jumpToEventIndex;
window.toggleVcdReplay = toggleVcdReplay;
window.jumpToEnd = jumpToEnd;
window.updateReplaySpeed = updateReplaySpeed;

// Animation and VCD Replay System
function startAnimationLoop() {
  function animate() {
    const currentTime = Date.now();
    const dt = (currentTime - state.lastUpdateTime) / 1000; // Convert to seconds
    state.lastUpdateTime = currentTime;
    
    updateVcdReplay(dt);
    updateAnimatedPackets(dt);
    updateMeshVisualization();
    updatePerformanceMetrics();
    
    requestAnimationFrame(animate);
  }
  animate();
}

function updateVcdReplay(dt) {
  if (!state.vcdReplayActive || !state.vcdEvents || state.vcdEvents.length === 0) {
    return;
  }
  
  // Advance replay time
  const timeIncrement = dt * state.vcdReplaySpeed * 1000; // Convert to simulation time units
  const oldTime = state.vcdReplayTime;
  state.vcdReplayTime += timeIncrement;
  
  // Find events within current time window
  const currentEvents = state.vcdEvents.filter(event => 
    event.timestamp <= state.vcdReplayTime && event.timestamp > oldTime
  );
  
  // Process events and create animated packets
  currentEvents.forEach(event => {
    if (event.event_type === "inject") {
      createAnimatedPacket(event);
    }
  });
  
  // Update replay index for UI
  const currentEventIndex = state.vcdEvents.findIndex(event => 
    event.timestamp > state.vcdReplayTime
  );
  if (currentEventIndex !== -1) {
    state.vcdReplayIndex = currentEventIndex - 1;
  } else {
    state.vcdReplayIndex = state.vcdEvents.length - 1;
  }
  
  updateVcdEventDisplay();
}

function createAnimatedPacket(event) {
  const meshWidth = state.meshData.mesh_width || 4;
  const meshHeight = state.meshData.mesh_height || 4;
  
  // Calculate router position
  const srcX = event.router_id % meshWidth;
  const srcY = Math.floor(event.router_id / meshWidth);
  
  // Generate random destination for visualization
  const dstX = Math.floor(Math.random() * meshWidth);
  const dstY = Math.floor(Math.random() * meshHeight);
  
  if (srcX === dstX && srcY === dstY) return; // Skip self-routing
  
  // Calculate XY routing path
  const path = calculateXYRoutingPath(srcX, srcY, dstX, dstY, meshWidth, meshHeight);
  
  const packet = {
    id: `vcd_${event.timestamp}_${event.router_id}`,
    srcX, srcY, dstX, dstY,
    currentX: srcX, currentY: srcY,
    path,
    hopIndex: 0,
    timestamp: event.timestamp,
    event_type: event.packet_type || 'unknown',
    size_flits: event.size_flits || 1,
    progress: 0,
    speed: 2.0 // hops per second
  };
  
  state.animatedPackets.push(packet);
}

function calculateXYRoutingPath(srcX, srcY, dstX, dstY, meshWidth, meshHeight) {
  const path = [{x: srcX, y: srcY}];
  let currentX = srcX;
  let currentY = srcY;
  
  // Move in X direction first
  while (currentX !== dstX) {
    currentX += currentX < dstX ? 1 : -1;
    path.push({x: currentX, y: currentY});
  }
  
  // Then move in Y direction
  while (currentY !== dstY) {
    currentY += currentY < dstY ? 1 : -1;
    path.push({x: currentX, y: currentY});
  }
  
  return path;
}

function updateAnimatedPackets(dt) {
  const packetsToRemove = [];
  
  state.animatedPackets.forEach(packet => {
    if (packet.hopIndex >= packet.path.length - 1) {
      // Packet reached destination
      packetsToRemove.push(packet);
      return;
    }
    
    // Move packet towards next hop
    packet.progress += packet.speed * dt;
    
    if (packet.progress >= 1.0) {
      // Reached next hop
      packet.hopIndex++;
      packet.progress = 0;
      
      if (packet.hopIndex < packet.path.length) {
        const currentHop = packet.path[packet.hopIndex];
        packet.currentX = currentHop.x;
        packet.currentY = currentHop.y;
      }
    } else {
      // Interpolate position between current and next hop
      const currentHop = packet.path[packet.hopIndex];
      const nextHop = packet.path[packet.hopIndex + 1];
      
      packet.currentX = currentHop.x + (nextHop.x - currentHop.x) * packet.progress;
      packet.currentY = currentHop.y + (nextHop.y - currentHop.y) * packet.progress;
    }
  });
  
  // Remove completed packets
  packetsToRemove.forEach(packet => {
    const index = state.animatedPackets.indexOf(packet);
    if (index !== -1) {
      state.animatedPackets.splice(index, 1);
    }
  });
}

function startVcdReplay() {
  if (state.vcdEvents && state.vcdEvents.length > 0) {
    state.vcdReplayActive = true;
    state.vcdReplayTime = state.vcdEvents[0]?.timestamp || 0;
    state.animatedPackets = [];
    console.log("Started VCD replay animation");
  }
}

function stopVcdReplay() {
  state.vcdReplayActive = false;
  state.animatedPackets = [];
  console.log("Stopped VCD replay animation");
}

function resetVcdReplay() {
  state.vcdReplayTime = state.vcdEvents[0]?.timestamp || 0;
  state.vcdReplayIndex = 0;
  state.animatedPackets = [];
  updateVcdEventDisplay();
}

// UI updates
function updateConnectionStatus(connected) {
  const status = document.getElementById("connectionStatus");
  if (connected) {
    status.textContent = "🟢 Connected";
    status.className =
      "fixed bottom-4 right-4 bg-green-500 text-white px-3 py-1 rounded-full text-sm";
    status.classList.remove("hidden");
  } else {
    status.textContent = "🔴 Disconnected";
    status.className =
      "fixed bottom-4 right-4 bg-red-500 text-white px-3 py-1 rounded-full text-sm";
    status.classList.remove("hidden");
  }
}

function updateSimulationStatus(data) {
  const statusText = document.getElementById("statusText");
  statusText.textContent = data.message || data.status;

  if (
    data.status === "completed" ||
    data.status === "failed" ||
    data.status === "cancelled"
  ) {
    state.simulationRunning = false;
    updateSimulationUI(false);
  }
}

function updateProgress(progress) {
  const progressBar = document.getElementById("progressBar");
  progressBar.style.width = `${progress}%`;
}

function updateSimulationUI(running) {
  const startBtn = document.getElementById("startSimBtn");
  const cancelBtn = document.getElementById("cancelSimBtn");
  const statusDisplay = document.getElementById("statusDisplay");

  if (running) {
    startBtn.disabled = true;
    startBtn.classList.add("hidden");
    cancelBtn.classList.remove("hidden");
    statusDisplay.classList.remove("hidden");
  } else {
    startBtn.disabled = false;
    startBtn.classList.remove("hidden");
    cancelBtn.classList.add("hidden");
    setTimeout(() => {
      statusDisplay.classList.add("hidden");
    }, 3000);
  }
}

function updateDashboardStatus(data) {
  state.simulationRunning = data.simulation_running;
  updateSimulationUI(data.simulation_running);
}

function showStatus(message, type) {
  const statusText = document.getElementById("statusText");
  statusText.textContent = message;

  const statusDisplay = document.getElementById("statusDisplay");
  statusDisplay.classList.remove("hidden");

  // Auto-hide after 3 seconds for non-running states
  if (!state.simulationRunning) {
    setTimeout(() => {
      statusDisplay.classList.add("hidden");
    }, 3000);
  }
}

// Mesh visualization
function initializeMeshVisualization() {
  const container = document.getElementById("meshVisualization");
  const svg = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  svg.setAttribute("width", "100%");
  svg.setAttribute("height", "400");
  svg.setAttribute("viewBox", "0 0 400 400");
  svg.style.background = "#f9fafb";

  container.appendChild(svg);
  state.meshSvg = svg;

  updateMeshVisualization();
}

function updateMeshVisualization() {
  if (!state.meshSvg || !state.meshData.routers) return;

  // Clear existing content
  state.meshSvg.innerHTML = "";

  const { mesh_width, mesh_height, routers, packets } = state.meshData;
  const cellWidth = 380 / mesh_width;
  const cellHeight = 380 / mesh_height;
  const offsetX = 10;
  const offsetY = 10;

  // Draw connections
  for (let x = 0; x < mesh_width; x++) {
    for (let y = 0; y < mesh_height; y++) {
      const centerX = offsetX + x * cellWidth + cellWidth / 2;
      const centerY = offsetY + y * cellHeight + cellHeight / 2;

      // Horizontal connections
      if (x < mesh_width - 1) {
        const line = document.createElementNS(
          "http://www.w3.org/2000/svg",
          "line"
        );
        line.setAttribute("x1", centerX);
        line.setAttribute("y1", centerY);
        line.setAttribute("x2", centerX + cellWidth);
        line.setAttribute("y2", centerY);
        line.setAttribute("class", "connection-line");
        line.setAttribute("stroke", "#9ca3af");
        line.setAttribute("stroke-width", "2");
        state.meshSvg.appendChild(line);
      }

      // Vertical connections
      if (y < mesh_height - 1) {
        const line = document.createElementNS(
          "http://www.w3.org/2000/svg",
          "line"
        );
        line.setAttribute("x1", centerX);
        line.setAttribute("y1", centerY);
        line.setAttribute("x2", centerX);
        line.setAttribute("y2", centerY + cellHeight);
        line.setAttribute("class", "connection-line");
        line.setAttribute("stroke", "#9ca3af");
        line.setAttribute("stroke-width", "2");
        state.meshSvg.appendChild(line);
      }
    }
  }

  // Draw routers
  routers.forEach((router) => {
    const centerX = offsetX + router.x * cellWidth + cellWidth / 2;
    const centerY = offsetY + router.y * cellHeight + cellHeight / 2;

    // Router circle
    const circle = document.createElementNS(
      "http://www.w3.org/2000/svg",
      "circle"
    );
    circle.setAttribute("cx", centerX);
    circle.setAttribute("cy", centerY);
    circle.setAttribute("r", "20");

    // Color based on utilization
    const utilization = router.utilization || 0;
    const red = Math.floor(255 * utilization);
    const green = Math.floor(255 * (1 - utilization));
    circle.setAttribute("fill", `rgb(${red}, ${green}, 100)`);
    circle.setAttribute("stroke", "#374151");
    circle.setAttribute("stroke-width", "2");
    circle.setAttribute("class", "router-node");

    // Add hover tooltip
    const title = document.createElementNS(
      "http://www.w3.org/2000/svg",
      "title"
    );
    title.textContent = `Router ${router.node_id}\nPosition: (${router.x}, ${
      router.y
    })\nUtilization: ${(utilization * 100).toFixed(
      1
    )}%\nTemperature: ${router.temperature.toFixed(1)}°C`;
    circle.appendChild(title);

    state.meshSvg.appendChild(circle);

    // Router label
    const text = document.createElementNS("http://www.w3.org/2000/svg", "text");
    text.setAttribute("x", centerX);
    text.setAttribute("y", centerY + 5);
    text.setAttribute("text-anchor", "middle");
    text.setAttribute("font-size", "12");
    text.setAttribute("font-weight", "bold");
    text.setAttribute("fill", "#ffffff");
    text.textContent = `R${router.node_id}`;
    state.meshSvg.appendChild(text);
  });

  // Draw packets from current data or VCD events
  const packetsToShow = getActivePackets();
  if (packetsToShow && packetsToShow.length > 0) {
    packetsToShow.forEach((packet) => {
      const packetX = offsetX + packet.current_x * cellWidth + cellWidth / 2;
      const packetY = offsetY + packet.current_y * cellHeight + cellHeight / 2;

      const packetEl = document.createElementNS(
        "http://www.w3.org/2000/svg",
        "circle"
      );
      packetEl.setAttribute("cx", packetX);
      packetEl.setAttribute("cy", packetY);
      packetEl.setAttribute("r", "4");

      // Color based on packet type or event type
      const colors = {
        CONV_DATA: "#3b82f6",
        GRADIENT: "#ef4444", 
        WEIGHT_UPDATE: "#10b981",
        inject: "#22c55e",
        forward: "#3b82f6",
        arrive: "#ef4444",
        default: "#8b5cf6",
      };
      const color = colors[packet.packet_type || packet.event_type] || colors.default;
      packetEl.setAttribute("fill", color);
      packetEl.setAttribute("class", "packet-animation");

      const title = document.createElementNS(
        "http://www.w3.org/2000/svg",
        "title"
      );
      
      // Different tooltip for VCD events vs regular packets
      if (packet.event_type) {
        title.textContent = `VCD Event ${packet.packet_id}\nType: ${packet.event_type}\nRouter: ${packet.router_id}\nSrc: (${packet.src_x}, ${packet.src_y})\nDst: (${packet.dst_x}, ${packet.dst_y})\nTime: ${packet.timestamp}`;
      } else {
        title.textContent = `Packet ${packet.id}\nType: ${packet.packet_type}\nSrc: (${packet.src_x}, ${packet.src_y})\nDst: (${packet.dst_x}, ${packet.dst_y})`;
      }
      packetEl.appendChild(title);

      state.meshSvg.appendChild(packetEl);
    });
  }
}

// Get active packets from VCD events or simulation data
function getActivePackets() {
  // If VCD replay is active, show animated packets
  if (state.vcdReplayActive && state.animatedPackets.length > 0) {
    return state.animatedPackets.map(packet => ({
      id: packet.id,
      event_type: packet.event_type,
      packet_id: packet.id,
      router_id: Math.floor(packet.currentY) * 4 + Math.floor(packet.currentX),
      timestamp: packet.timestamp,
      src_x: packet.srcX,
      src_y: packet.srcY,
      dst_x: packet.dstX,
      dst_y: packet.dstY,
      current_x: packet.currentX,
      current_y: packet.currentY,
      size_flits: packet.size_flits,
    }));
  }
  
  // If VCD events are loaded but not animating, show current event
  if (state.vcdEvents && state.vcdEvents.length > 0 && !state.vcdReplayActive) {
    const currentEvent = state.vcdEvents[state.vcdReplayIndex];
    if (currentEvent) {
      return [{
        id: currentEvent.packet_id,
        event_type: currentEvent.event_type,
        packet_id: currentEvent.packet_id,
        router_id: currentEvent.router_id,
        timestamp: currentEvent.timestamp,
        src_x: currentEvent.src_x,
        src_y: currentEvent.src_y,
        dst_x: currentEvent.dst_x,
        dst_y: currentEvent.dst_y,
        current_x: currentEvent.router_id % 4,
        current_y: Math.floor(currentEvent.router_id / 4),
      }];
    }
  }
  
  // Otherwise show simulation packets
  return state.meshData.packets || [];
}

// Performance metrics
function updatePerformanceMetrics() {
  // Get active packets (VCD or simulation)
  const activePackets = getActivePackets();
  const routers = state.meshData.routers || [];

  // Update packet count (use VCD if available, otherwise simulation packets)
  document.getElementById("packetCount").textContent = activePackets.length;

  // Calculate metrics only if routers exist
  if (routers.length > 0) {
    // Calculate average utilization
    const avgUtil = routers.reduce((sum, r) => sum + (r.utilization || 0), 0) / routers.length;
    document.getElementById("avgUtilization").textContent = isNaN(avgUtil) ? "0%" : `${(avgUtil * 100).toFixed(1)}%`;

    // Calculate max congestion
    const congestionLevels = routers.map((r) => r.congestion_level || 0);
    const maxCongestion = congestionLevels.length > 0 ? Math.max(...congestionLevels) : 0;
    document.getElementById("maxCongestion").textContent = isFinite(maxCongestion) ? `${(maxCongestion * 100).toFixed(1)}%` : "0%";

    // Calculate average temperature
    const avgTemp = routers.reduce((sum, r) => sum + (r.temperature || 25), 0) / routers.length;
    document.getElementById("avgTemperature").textContent = isNaN(avgTemp) ? "25°C" : `${avgTemp.toFixed(1)}°C`;
  } else {
    // Default values when no routers
    document.getElementById("avgUtilization").textContent = "0%";
    document.getElementById("maxCongestion").textContent = "0%";
    document.getElementById("avgTemperature").textContent = "25°C";
  }

  // Update VCD metrics if VCD data is loaded
  updateVcdMetrics();

  // Update router stats
  updateRouterStats(routers);
}

function updateVcdMetrics() {
  // Update VCD event count in performance metrics
  const vcdEventCountEl = document.getElementById("vcdEventsTotal");
  if (vcdEventCountEl) {
    vcdEventCountEl.textContent = state.vcdEvents?.length || 0;
  }
  
  // Update current VCD replay position
  const vcdProgressEl = document.getElementById("vcdProgress");
  if (vcdProgressEl) {
    if (state.vcdEvents?.length > 0) {
      const progress = ((state.vcdReplayIndex + 1) / state.vcdEvents.length * 100).toFixed(1);
      vcdProgressEl.textContent = `${progress}%`;
    } else {
      vcdProgressEl.textContent = "0%";
    }
  }
  
  // Update max event index input
  const jumpInput = document.getElementById("jumpToEvent");
  if (jumpInput && state.vcdEvents?.length > 0) {
    jumpInput.max = state.vcdEvents.length - 1;
    jumpInput.placeholder = `0-${state.vcdEvents.length - 1}`;
  }
  
  // Update performance history and charts
  updatePerformanceCharts();
}

function updatePerformanceCharts() {
  const routers = state.meshData.routers || [];
  const activePackets = getActivePackets();
  
  if (routers.length === 0) return;
  
  // Calculate current metrics
  const avgUtilization = routers.reduce((sum, r) => sum + (r.utilization || 0), 0) / routers.length;
  const maxCongestion = Math.max(...routers.map(r => r.congestion_level || 0));
  const packetCount = activePackets.length;
  
  // Add to history (keep last 50 points)
  const maxHistory = 50;
  state.performanceHistory.utilization.push(avgUtilization);
  state.performanceHistory.congestion.push(maxCongestion);
  state.performanceHistory.throughput.push(packetCount);
  
  if (state.performanceHistory.utilization.length > maxHistory) {
    state.performanceHistory.utilization.shift();
    state.performanceHistory.congestion.shift();
    state.performanceHistory.throughput.shift();
  }
  
  // Draw charts
  drawChart("utilizationChart", state.performanceHistory.utilization, "#10b981", "Utilization");
  drawChart("congestionChart", state.performanceHistory.congestion, "#ef4444", "Congestion");
  drawChart("packetChart", state.performanceHistory.throughput, "#3b82f6", "Packets");
}

function drawChart(canvasId, data, color, label) {
  const canvas = document.getElementById(canvasId);
  if (!canvas || data.length === 0) return;
  
  const ctx = canvas.getContext("2d");
  const width = canvas.width;
  const height = canvas.height;
  
  // Clear canvas
  ctx.clearRect(0, 0, width, height);
  
  // Set up drawing
  ctx.strokeStyle = color;
  ctx.fillStyle = color + "20"; // Semi-transparent fill
  ctx.lineWidth = 2;
  
  // Find min/max for scaling
  const min = Math.min(...data);
  const max = Math.max(...data, min + 0.1); // Ensure some range
  const range = max - min;
  
  // Draw background grid
  ctx.strokeStyle = "#e5e7eb";
  ctx.lineWidth = 1;
  for (let i = 0; i <= 4; i++) {
    const y = (height * i) / 4;
    ctx.beginPath();
    ctx.moveTo(0, y);
    ctx.lineTo(width, y);
    ctx.stroke();
  }
  
  // Draw data line
  ctx.strokeStyle = color;
  ctx.lineWidth = 2;
  ctx.beginPath();
  
  const stepX = width / (data.length - 1 || 1);
  
  data.forEach((value, index) => {
    const x = index * stepX;
    const y = height - ((value - min) / range) * height;
    
    if (index === 0) {
      ctx.moveTo(x, y);
    } else {
      ctx.lineTo(x, y);
    }
  });
  
  ctx.stroke();
  
  // Fill area under curve
  if (data.length > 1) {
    ctx.fillStyle = color + "20";
    ctx.lineTo(width, height);
    ctx.lineTo(0, height);
    ctx.closePath();
    ctx.fill();
  }
  
  // Draw current value
  ctx.fillStyle = color;
  ctx.font = "12px sans-serif";
  ctx.textAlign = "right";
  const currentValue = data[data.length - 1] || 0;
  ctx.fillText(`${currentValue.toFixed(2)}`, width - 5, 15);
}

function updateRouterStats(routers) {
  const container = document.getElementById("routerStats");
  container.innerHTML = "";

  routers.slice(0, 8).forEach((router) => {
    // Show first 8 routers
    const statDiv = document.createElement("div");
    statDiv.className = "flex justify-between items-center text-sm";
    statDiv.innerHTML = `
            <span class="font-medium">R${router.node_id}</span>
            <span class="text-gray-600">${(router.utilization * 100).toFixed(
              0
            )}%</span>
        `;
    container.appendChild(statDiv);
  });
}

// Simulation log updates
async function updateSimulationLog() {
  try {
    const response = await fetch("/api/simulation/log");
    const data = await response.json();

    const logContainer = document.getElementById("simulationLog");
    logContainer.innerHTML = "";

    data.log.forEach((entry) => {
      const logEntry = document.createElement("div");
      logEntry.textContent = entry;
      logEntry.className = "mb-1";
      logContainer.appendChild(logEntry);
    });

    logContainer.scrollTop = logContainer.scrollHeight;
  } catch (error) {
    console.error("Error fetching simulation log:", error);
  }
}

// Real-time log updates via WebSocket
function appendToSimulationLog(logEntries) {
  const logContainer = document.getElementById("simulationLog");

  logEntries.forEach((entry) => {
    const logEntry = document.createElement("div");
    logEntry.textContent = entry;
    logEntry.className = "mb-1";

    // Add color coding based on content
    if (
      entry.includes("❌") ||
      entry.includes("Error") ||
      entry.includes("failed")
    ) {
      logEntry.className += " text-red-600";
    } else if (
      entry.includes("✅") ||
      entry.includes("completed") ||
      entry.includes("success")
    ) {
      logEntry.className += " text-green-600";
    } else if (
      entry.includes("⚠️") ||
      entry.includes("Warning") ||
      entry.includes("timeout")
    ) {
      logEntry.className += " text-yellow-600";
    } else if (
      entry.includes("🔧") ||
      entry.includes("🔨") ||
      entry.includes("verilating") ||
      entry.includes("compiling")
    ) {
      logEntry.className += " text-blue-600";
    }

    logContainer.appendChild(logEntry);
  });

  // Auto-scroll to bottom
  logContainer.scrollTop = logContainer.scrollHeight;

  // Keep only last 100 entries for performance
  while (logContainer.children.length > 100) {
    logContainer.removeChild(logContainer.firstChild);
  }
}

// Periodic updates
setInterval(() => {
  if (state.simulationRunning) {
    updateSimulationLog();
  }
}, 2000);

setInterval(() => {
  fetchInitialData();
}, 5000);
