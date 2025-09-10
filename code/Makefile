RTL_DIR = rtl
TB_DIR = tb
BUILD_DIR = build
SIM_DIR = sim

VERILATOR = verilator
VERILATOR_FLAGS = -Wall -Wno-fatal --cc --exe --build --trace
VERILATOR_FLAGS += -I$(RTL_DIR) -I$(RTL_DIR)/common

TB_VERILATOR_FLAGS = -Wall -Wno-fatal --cc --exe --build --trace --timing
TB_VERILATOR_FLAGS += -I../$(RTL_DIR) -I../$(RTL_DIR)/common

SYSTEMC_HOME = /usr/local/systemc-3.0.1
VERILATOR_FLAGS += -CFLAGS "-I$(SYSTEMC_HOME)/include"
VERILATOR_FLAGS += -LDFLAGS "-L$(SYSTEMC_HOME)/lib-linux64 -lsystemc"
TB_VERILATOR_FLAGS += -CFLAGS "-I$(SYSTEMC_HOME)/include"
TB_VERILATOR_FLAGS += -LDFLAGS "-L$(SYSTEMC_HOME)/lib-linux64 -lsystemc"

RTL_SOURCES = $(RTL_DIR)/nebula_pkg.sv \
              $(RTL_DIR)/common/nebula_fifo.sv \
              $(RTL_DIR)/common/nebula_credit_flow_ctrl.sv \
              $(RTL_DIR)/common/nebula_rr_arbiter.sv \
              $(RTL_DIR)/common/nebula_crc.sv \
              $(RTL_DIR)/common/nebula_packet_assembler.sv \
              $(RTL_DIR)/common/nebula_packet_disassembler.sv \
              $(RTL_DIR)/nebula_router.sv

TB_RTL_SOURCES = ../$(RTL_DIR)/nebula_pkg.sv \
                 ../$(RTL_DIR)/common/nebula_fifo.sv \
                 ../$(RTL_DIR)/common/nebula_credit_flow_ctrl.sv \
                 ../$(RTL_DIR)/common/nebula_rr_arbiter.sv \
                 ../$(RTL_DIR)/common/nebula_crc.sv \
                 ../$(RTL_DIR)/common/nebula_packet_assembler.sv \
                 ../$(RTL_DIR)/common/nebula_packet_disassembler.sv \
                 ../$(RTL_DIR)/nebula_router.sv \
                 ../$(RTL_DIR)/nebula_axi_if.sv \
                 ../$(RTL_DIR)/nebula_axi_noc_bridge.sv \
                 ../$(RTL_DIR)/nebula_axi_system.sv \
                 ../$(RTL_DIR)/nebula_chi_interface.sv \
                 ../$(RTL_DIR)/nebula_chi_directory.sv \
                 ../$(RTL_DIR)/nebula_chi_noc_bridge.sv

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(SIM_DIR):
	mkdir -p $(SIM_DIR)

clean:
	rm -rf $(BUILD_DIR) $(SIM_DIR)
	rm -rf obj_dir *.vcd *.fst


TB_STEP7_DIR = tb/step7

TB_RTL_SOURCES_STEP7 = ../$(RTL_DIR)/nebula_pkg.sv \
                       ../$(RTL_DIR)/common/nebula_fifo.sv \
                       ../$(RTL_DIR)/common/nebula_credit_flow_ctrl.sv \
                       ../$(RTL_DIR)/common/nebula_rr_arbiter.sv \
                       ../$(RTL_DIR)/common/nebula_crc.sv \
                       ../$(RTL_DIR)/common/nebula_packet_assembler.sv \
                       ../$(RTL_DIR)/common/nebula_packet_disassembler.sv \
                       ../$(RTL_DIR)/nebula_router.sv \
                       ../$(RTL_DIR)/nebula_axi_if.sv \
                       ../$(RTL_DIR)/nebula_axi_noc_bridge.sv \
                       ../$(RTL_DIR)/nebula_niu_axi.sv \
                       ../$(RTL_DIR)/nebula_mesh_top.sv \
                       ../$(RTL_DIR)/nebula_system_top.sv \
                       ../$(RTL_DIR)/nebula_top_simple.sv

TB_RTL_SOURCES_TRAFFIC = ../$(RTL_DIR)/nebula_pkg.sv \
                         ../$(RTL_DIR)/common/nebula_fifo.sv \
                         ../$(RTL_DIR)/common/nebula_credit_flow_ctrl.sv \
                         ../$(RTL_DIR)/common/nebula_rr_arbiter.sv \
                         ../$(RTL_DIR)/common/nebula_crc.sv \
                         ../$(RTL_DIR)/common/nebula_packet_assembler.sv \
                         ../$(RTL_DIR)/common/nebula_packet_disassembler.sv \
                         ../$(RTL_DIR)/nebula_router.sv \
                         ../$(RTL_DIR)/nebula_axi_if.sv \
                         ../$(RTL_DIR)/nebula_axi_noc_bridge.sv \
                         ../$(RTL_DIR)/nebula_niu_axi.sv \
                         ../$(RTL_DIR)/nebula_chi_interface.sv \
                         ../$(RTL_DIR)/nebula_chi_directory.sv \
                         ../$(RTL_DIR)/nebula_chi_noc_bridge.sv \
                         ../$(RTL_DIR)/nebula_mesh_top.sv \
                         ../$(RTL_DIR)/nebula_system_top.sv \
                         ../$(RTL_DIR)/nebula_top.sv


tb_nebula_top: $(BUILD_DIR)
	@echo "Running Nebula Top-Level System testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_top $(TB_RTL_SOURCES_STEP7) ../$(TB_STEP7_DIR)/tb_nebula_top_simple.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_top

tb_nebula_traffic: $(BUILD_DIR)
	@echo "Running Nebula Traffic Pattern testbench..."
	@if [ -f tb/generated/tb_nebula_current.sv ]; then \
		TESTBENCH_FILE="tb/generated/tb_nebula_current.sv"; \
		PATTERN_NAME=$$(readlink tb/generated/tb_nebula_current.sv 2>/dev/null | sed 's/tb_nebula_//' | sed 's/.sv//' || echo "current"); \
		echo "Using current testbench: $$TESTBENCH_FILE (pattern: $$PATTERN_NAME)"; \
	else \
		TESTBENCH_FILE=$$(find tb/generated -name "tb_nebula_*.sv" -type f | sort -r | head -1); \
		if [ -z "$$TESTBENCH_FILE" ]; then \
			echo "Error: No generated traffic testbench found in tb/generated/"; \
			echo "Please run the dashboard to generate a traffic pattern first."; \
			exit 1; \
		fi; \
		PATTERN_NAME=$$(basename "$$TESTBENCH_FILE" .sv | sed 's/tb_nebula_//'); \
		echo "Using latest testbench: $$TESTBENCH_FILE (pattern: $$PATTERN_NAME)"; \
	fi; \
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_top_traffic $(TB_RTL_SOURCES_TRAFFIC) ../$$TESTBENCH_FILE
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_top_traffic

run_traffic_gen: $(BUILD_DIR)
	@echo "Running Python traffic pattern generator..."
	cd $(BUILD_DIR) && python3 ../python/nebula_traffic_generator.py

dashboard: $(BUILD_DIR)
	@echo "Starting Nebula Dashboard..."
	@echo "Checking Python dependencies..."
	@python3 -c "import pygame" 2>/dev/null || (echo "Installing pygame..." && pip3 install pygame)
	@python3 -c "import numpy" 2>/dev/null || (echo "Installing numpy..." && pip3 install numpy)
	@echo "Launching dashboard..."
	cd python && python3 nebula_dashboard.py

webapp: $(BUILD_DIR)
	@echo "Starting Nebula Web Dashboard..."
	@echo "Checking web dashboard environment..."
	@if [ ! -d "../web_dashboard/backend/venv" ]; then \
		echo "Error: Virtual environment not found at ../web_dashboard/backend/venv"; \
		echo "Please run: make install_webapp_deps"; \
		exit 1; \
	fi
	@echo "Launching Flask web application..."
	cd ../web_dashboard/backend && bash -c "source venv/bin/activate && python app.py"



# Help with dashboard
help_dashboard:
	@echo "Nebula Dashboard Commands:"
	@echo "  dashboard     - Launch interactive pygame dashboard"
	@echo "  webapp        - Launch Flask web dashboard (browser-based)"
	@echo "  run_analysis  - Run Python traffic analysis"
	@echo "  test_vcd      - Test VCD integration functionality"
	@echo "  install_dashboard_deps - Install Python dependencies"
	@echo "  install_webapp_deps    - Install web dashboard dependencies"
	@echo ""
	@echo "Dashboard Controls:"
	@echo "  SPACE - Start/Stop simulation"
	@echo "  P - Pause/Resume"
	@echo "  1-4 - Change traffic patterns (uniform, hotspot, transpose, GPU)"
	@echo "  V - Run Verilog simulation"
	@echo "  L - Load VCD file for replay"
	@echo "  T - Toggle VCD replay"
	@echo "  UP/DOWN - Adjust VCD replay speed"
	@echo "  0 - Reset VCD replay to start"
	@echo "  R - Reset statistics"
	@echo "  +/- - Adjust injection rate"
	@echo ""

	@echo "  help          - Show this help message"
