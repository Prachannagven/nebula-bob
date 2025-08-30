# Nebula Project Makefile
# Handles compilation and simulation of the Nebula GPU interconnect

# Project directories
RTL_DIR = rtl
TB_DIR = tb
BUILD_DIR = build
SIM_DIR = sim

# Tools
VERILATOR = verilator
VERILATOR_FLAGS = -Wall -Wno-fatal --cc --exe --build --trace
VERILATOR_FLAGS += -I# Help target
help:
	@echo "Available targets:"
	@echo "  all           - Compile all RTL (default)"
	@echo "  compile       - Compile RTL with Verilator"
	@echo "  lint          - Run linting on RTL code"
	@echo "  lint_tb       - Run linting on testbench files"
	@echo "  format        - Format SystemVerilog code"
	@echo "  clean         - Clean build artifacts"
	@echo "  test_step1    - Run all Step 1 testbenches with results summary"
	@echo "  test_step2    - Run all Step 2 testbenches with results summary"
	@echo "  tb_fifo       - Run FIFO testbench (verbose)"
	@echo "  tb_credit     - Run credit flow control testbench (verbose)"
	@echo "  tb_arbiter    - Run round-robin arbiter testbench (verbose)"
	@echo "  tb_crc        - Run CRC testbench (verbose)"
	@echo "  tb_assembler  - Run packet assembler testbench (verbose)"
	@echo "  tb_disassembler - Run packet disassembler testbench (verbose)"
	@echo "  tb_integration - Run Step 1 integration testbench (verbose)"
	@echo "  tb_router     - Run router testbench (verbose)"
	@echo "  tb_step2_integration - Run Step 2 integration testbench (verbose)"
	@echo "  help          - Show this help message"

# =============================================================================
# STEP 2 TARGETS - Router Implementation
# =============================================================================

# Router testbench
tb_router: $(BUILD_DIR)
	@echo "Running router testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_router $(TB_RTL_SOURCES) ../tb/step2/tb_nebula_router.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_router

tb_router_quiet: $(BUILD_DIR)
	@echo "Compiling Router testbench..."
	@cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_router $(TB_RTL_SOURCES) ../tb/step2/tb_nebula_router.sv > /dev/null 2>&1
	@echo "--- ROUTER TESTBENCH RESULTS ---"
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_router

# Step 2 integration testbench  
tb_step2_integration: $(BUILD_DIR)
	@echo "Running Step 2 integration testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_step2_integration $(TB_RTL_SOURCES) ../tb/step2/tb_step2_integration.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_step2_integration

tb_step2_integration_quiet: $(BUILD_DIR)
	@echo "Compiling Step 2 Integration testbench..."
	@cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_step2_integration $(TB_RTL_SOURCES) ../tb/step2/tb_step2_integration.sv > /dev/null 2>&1
	@echo "--- STEP 2 INTEGRATION TESTBENCH RESULTS ---"
	cd $(BUILD_DIR) && ./obj_dir/Vtb_step2_integration

# Run all Step 2 tests
test_step2: $(BUILD_DIR)
	@echo "========================================="
	@echo "RUNNING ALL STEP 2 TESTBENCHES"
	@echo "========================================="
	@echo ""
	
	@# Initialize results tracking
	@results_file="$(BUILD_DIR)/step2_test_results.txt"; \
	echo "Step 2 Test Results - $$(date)" > $$results_file; \
	echo "=================================" >> $$results_file; \
	echo "" >> $$results_file; \
	failed_tests=0; \
	
	echo "Running Router testbench..."; \
	if $(MAKE) tb_router_quiet >> $$results_file 2>&1; then \
		echo "✅ Router testbench: PASSED"; \
		echo "✅ Router testbench: PASSED" >> $$results_file; \
	else \
		echo "❌ Router testbench: FAILED"; \
		echo "❌ Router testbench: FAILED" >> $$results_file; \
		failed_tests=$$((failed_tests + 1)); \
	fi; \
	echo "" >> $$results_file; \
	
	echo "Running Step 2 Integration testbench..."; \
	if $(MAKE) tb_step2_integration_quiet >> $$results_file 2>&1; then \
		echo "✅ Step 2 Integration testbench: PASSED"; \
		echo "✅ Step 2 Integration testbench: PASSED" >> $$results_file; \
	else \
		echo "❌ Step 2 Integration testbench: FAILED"; \
		echo "❌ Step 2 Integration testbench: FAILED" >> $$results_file; \
		failed_tests=$$((failed_tests + 1)); \
	fi; \
	echo "" >> $$results_file; \
	
	echo "=========================================" >> $$results_file; \
	if [ $$failed_tests -eq 0 ]; then \
		echo "🎉 ALL STEP 2 TESTS PASSED! 🎉"; \
		echo "🎉 ALL STEP 2 TESTS PASSED! 🎉" >> $$results_file; \
		echo "Step 2 router implementation is complete and verified."; \
		echo "Step 2 router implementation is complete and verified." >> $$results_file; \
		echo "Results saved to: $$results_file"; \
	else \
		echo "❌ STEP 2 TEST FAILURES: $$failed_tests test(s) failed"; \
		echo "❌ STEP 2 TEST FAILURES: $$failed_tests test(s) failed" >> $$results_file; \
		echo "Results saved to: $$results_file"; \
		echo "Check the log file for detailed failure information."; \
		exit 1; \
	fi_DIR)/common

# Testbench flags (for running from build directory)
TB_VERILATOR_FLAGS = -Wall -Wno-fatal --cc --exe --build --trace --timing
TB_VERILATOR_FLAGS += -I../$(RTL_DIR) -I../$(RTL_DIR)/common

# SystemC
SYSTEMC_HOME = /usr/local/systemc-3.0.1
VERILATOR_FLAGS += -CFLAGS "-I$(SYSTEMC_HOME)/include"
VERILATOR_FLAGS += -LDFLAGS "-L$(SYSTEMC_HOME)/lib-linux64 -lsystemc"
TB_VERILATOR_FLAGS += -CFLAGS "-I$(SYSTEMC_HOME)/include"
TB_VERILATOR_FLAGS += -LDFLAGS "-L$(SYSTEMC_HOME)/lib-linux64 -lsystemc"

# Source files
RTL_SOURCES = $(RTL_DIR)/nebula_pkg.sv \
              $(RTL_DIR)/common/nebula_fifo.sv \
              $(RTL_DIR)/common/nebula_credit_flow_ctrl.sv \
              $(RTL_DIR)/common/nebula_rr_arbiter.sv \
              $(RTL_DIR)/common/nebula_crc.sv \
              $(RTL_DIR)/common/nebula_packet_assembler.sv \
              $(RTL_DIR)/common/nebula_packet_disassembler.sv \
              $(RTL_DIR)/nebula_router.sv

# Test modules (to be added as we implement them)
TB_SOURCES = 

# Default target
all: compile

# Create build directories
$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(SIM_DIR):
	mkdir -p $(SIM_DIR)

# Compile RTL
compile: $(BUILD_DIR)
	@echo "Compiling Nebula RTL..."
	cd $(BUILD_DIR) && $(VERILATOR) $(VERILATOR_FLAGS) --top-module nebula_pkg $(RTL_SOURCES)

# Clean build artifacts
clean:
	rm -rf $(BUILD_DIR) $(SIM_DIR)
	rm -rf obj_dir *.vcd *.fst

# Lint RTL code
lint:
	@echo "Linting RTL code..."
	$(VERILATOR) --lint-only -Wall -Wno-fatal -I$(RTL_DIR) -I$(RTL_DIR)/common $(RTL_SOURCES)

# Format code (requires verible-verilog-format)
format:
	@if command -v verible-verilog-format >/dev/null 2>&1; then \
		find $(RTL_DIR) -name "*.sv" -exec verible-verilog-format --inplace {} \; ; \
		echo "Formatted SystemVerilog files"; \
	else \
		echo "verible-verilog-format not found, skipping format"; \
	fi

# Testbench files
TB_DIR = tb/step1
TB_FILES = $(TB_DIR)/tb_nebula_fifo.sv \
           $(TB_DIR)/tb_nebula_credit_flow_ctrl.sv \
           $(TB_DIR)/tb_nebula_rr_arbiter.sv \
           $(TB_DIR)/tb_nebula_crc.sv \
           $(TB_DIR)/tb_nebula_packet_assembler.sv \
           $(TB_DIR)/tb_nebula_packet_disassembler.sv \
           $(TB_DIR)/tb_step1_integration.sv

# RTL sources for testbenches (with correct relative paths from build dir)
TB_RTL_SOURCES = ../$(RTL_DIR)/nebula_pkg.sv \
                 ../$(RTL_DIR)/common/nebula_fifo.sv \
                 ../$(RTL_DIR)/common/nebula_credit_flow_ctrl.sv \
                 ../$(RTL_DIR)/common/nebula_rr_arbiter.sv \
                 ../$(RTL_DIR)/common/nebula_crc.sv \
                 ../$(RTL_DIR)/common/nebula_packet_assembler.sv \
                 ../$(RTL_DIR)/common/nebula_packet_disassembler.sv \
                 ../$(RTL_DIR)/nebula_router.sv

# Individual testbench targets
tb_fifo: $(BUILD_DIR)
	@echo "Running FIFO testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_fifo $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_fifo.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_fifo

tb_credit: $(BUILD_DIR)
	@echo "Running credit flow control testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_credit_flow_ctrl $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_credit_flow_ctrl.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_credit_flow_ctrl

tb_arbiter: $(BUILD_DIR)
	@echo "Running round-robin arbiter testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_rr_arbiter $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_rr_arbiter.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_rr_arbiter

tb_crc: $(BUILD_DIR)
	@echo "Running CRC testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_crc $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_crc.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_crc

tb_assembler: $(BUILD_DIR)
	@echo "Running packet assembler testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_packet_assembler $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_packet_assembler.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_packet_assembler

tb_disassembler: $(BUILD_DIR)
	@echo "Running packet disassembler testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_packet_disassembler $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_packet_disassembler.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_packet_disassembler

tb_integration: $(BUILD_DIR)
	@echo "Running Step 1 integration testbench..."
	cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_step1_integration $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_step1_integration.sv
	cd $(BUILD_DIR) && ./obj_dir/Vtb_step1_integration

# Quiet versions for batch testing (redirect compilation output but keep test results)
tb_fifo_quiet: $(BUILD_DIR)
	@echo "Compiling FIFO testbench..." 
	@cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_fifo $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_fifo.sv > /dev/null 2>&1
	@echo "--- FIFO TESTBENCH RESULTS ---"
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_fifo

tb_credit_quiet: $(BUILD_DIR)
	@echo "Compiling Credit Flow Control testbench..."
	@cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_credit_flow_ctrl $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_credit_flow_ctrl.sv > /dev/null 2>&1
	@echo "--- CREDIT FLOW CONTROL TESTBENCH RESULTS ---"
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_credit_flow_ctrl

tb_arbiter_quiet: $(BUILD_DIR)
	@echo "Compiling Round-Robin Arbiter testbench..."
	@cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_rr_arbiter $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_rr_arbiter.sv > /dev/null 2>&1
	@echo "--- ROUND-ROBIN ARBITER TESTBENCH RESULTS ---"
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_rr_arbiter

tb_crc_quiet: $(BUILD_DIR)
	@echo "Compiling CRC testbench..."
	@cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_crc $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_crc.sv > /dev/null 2>&1
	@echo "--- CRC TESTBENCH RESULTS ---"
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_crc

tb_assembler_quiet: $(BUILD_DIR)
	@echo "Compiling Packet Assembler testbench..."
	@cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_packet_assembler $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_packet_assembler.sv > /dev/null 2>&1
	@echo "--- PACKET ASSEMBLER TESTBENCH RESULTS ---"
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_packet_assembler

tb_disassembler_quiet: $(BUILD_DIR)
	@echo "Compiling Packet Disassembler testbench..."
	@cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_nebula_packet_disassembler $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_nebula_packet_disassembler.sv > /dev/null 2>&1
	@echo "--- PACKET DISASSEMBLER TESTBENCH RESULTS ---"
	cd $(BUILD_DIR) && ./obj_dir/Vtb_nebula_packet_disassembler

tb_integration_quiet: $(BUILD_DIR)
	@echo "Compiling Step 1 Integration testbench..."
	@cd $(BUILD_DIR) && $(VERILATOR) $(TB_VERILATOR_FLAGS) --binary \
		--top-module tb_step1_integration $(TB_RTL_SOURCES) ../$(TB_DIR)/tb_step1_integration.sv > /dev/null 2>&1
	@echo "--- STEP 1 INTEGRATION TESTBENCH RESULTS ---"
	cd $(BUILD_DIR) && ./obj_dir/Vtb_step1_integration

# Run all Step 1 testbenches with results summary
test_step1: $(BUILD_DIR)
	@echo "=== STEP 1 TESTBENCH SUITE ==="
	@echo "Running all testbenches and collecting results..."
	@echo ""
	@results_file="$(BUILD_DIR)/test_results.txt"; \
	echo "=== NEBULA STEP 1 TESTBENCH RESULTS ===" > $$results_file; \
	echo "Generated on: $$(date)" >> $$results_file; \
	echo "" >> $$results_file; \
	total_tests=0; \
	passed_tests=0; \
	failed_tests=0; \
	echo "Running FIFO testbench..."; \
	if $(MAKE) tb_fifo_quiet >> $$results_file 2>&1; then \
		echo "✓ FIFO testbench: PASSED" | tee -a $$results_file; \
		passed_tests=$$((passed_tests + 1)); \
	else \
		echo "✗ FIFO testbench: FAILED" | tee -a $$results_file; \
		failed_tests=$$((failed_tests + 1)); \
	fi; \
	total_tests=$$((total_tests + 1)); \
	echo ""; \
	echo "Running Credit Flow Control testbench..."; \
	if $(MAKE) tb_credit_quiet >> $$results_file 2>&1; then \
		echo "✓ Credit Flow Control testbench: PASSED" | tee -a $$results_file; \
		passed_tests=$$((passed_tests + 1)); \
	else \
		echo "✗ Credit Flow Control testbench: FAILED" | tee -a $$results_file; \
		failed_tests=$$((failed_tests + 1)); \
	fi; \
	total_tests=$$((total_tests + 1)); \
	echo ""; \
	echo "Running Round-Robin Arbiter testbench..."; \
	if $(MAKE) tb_arbiter_quiet >> $$results_file 2>&1; then \
		echo "✓ Round-Robin Arbiter testbench: PASSED" | tee -a $$results_file; \
		passed_tests=$$((passed_tests + 1)); \
	else \
		echo "✗ Round-Robin Arbiter testbench: FAILED" | tee -a $$results_file; \
		failed_tests=$$((failed_tests + 1)); \
	fi; \
	total_tests=$$((total_tests + 1)); \
	echo ""; \
	echo "Running CRC testbench..."; \
	if $(MAKE) tb_crc_quiet >> $$results_file 2>&1; then \
		echo "✓ CRC testbench: PASSED" | tee -a $$results_file; \
		passed_tests=$$((passed_tests + 1)); \
	else \
		echo "✗ CRC testbench: FAILED" | tee -a $$results_file; \
		failed_tests=$$((failed_tests + 1)); \
	fi; \
	total_tests=$$((total_tests + 1)); \
	echo ""; \
	echo "Running Packet Assembler testbench..."; \
	if $(MAKE) tb_assembler_quiet >> $$results_file 2>&1; then \
		echo "✓ Packet Assembler testbench: PASSED" | tee -a $$results_file; \
		passed_tests=$$((passed_tests + 1)); \
	else \
		echo "✗ Packet Assembler testbench: FAILED" | tee -a $$results_file; \
		failed_tests=$$((failed_tests + 1)); \
	fi; \
	total_tests=$$((total_tests + 1)); \
	echo ""; \
	echo "Running Packet Disassembler testbench..."; \
	if $(MAKE) tb_disassembler_quiet >> $$results_file 2>&1; then \
		echo "✓ Packet Disassembler testbench: PASSED" | tee -a $$results_file; \
		passed_tests=$$((passed_tests + 1)); \
	else \
		echo "✗ Packet Disassembler testbench: FAILED" | tee -a $$results_file; \
		failed_tests=$$((failed_tests + 1)); \
	fi; \
	total_tests=$$((total_tests + 1)); \
	echo ""; \
	echo "Running Step 1 Integration testbench..."; \
	if $(MAKE) tb_integration_quiet >> $$results_file 2>&1; then \
		echo "✓ Step 1 Integration testbench: PASSED" | tee -a $$results_file; \
		passed_tests=$$((passed_tests + 1)); \
	else \
		echo "✗ Step 1 Integration testbench: FAILED" | tee -a $$results_file; \
		failed_tests=$$((failed_tests + 1)); \
	fi; \
	total_tests=$$((total_tests + 1)); \
	echo ""; \
	echo "========================================" | tee -a $$results_file; \
	echo "          FINAL TEST SUMMARY            " | tee -a $$results_file; \
	echo "========================================" | tee -a $$results_file; \
	echo "Total testbenches: $$total_tests" | tee -a $$results_file; \
	echo "Passed: $$passed_tests" | tee -a $$results_file; \
	echo "Failed: $$failed_tests" | tee -a $$results_file; \
	if [ $$failed_tests -eq 0 ]; then \
		echo "🎉 ALL TESTS PASSED!" | tee -a $$results_file; \
		echo "Results saved to: $$results_file"; \
		exit 0; \
	else \
		echo "❌ $$failed_tests test(s) failed" | tee -a $$results_file; \
		echo "Results saved to: $$results_file"; \
		echo "Check the log file for detailed failure information."; \
		exit 1; \
	fi

# Lint testbenches
lint_tb:
	@echo "Linting testbench files..."
	$(VERILATOR) --lint-only -Wall -Wno-fatal -I$(RTL_DIR) -I$(RTL_DIR)/common $(RTL_SOURCES) $(TB_FILES)

# Help target
help:
	@echo "Available targets:"
	@echo "  all           - Compile all RTL (default)"
	@echo "  compile       - Compile RTL with Verilator"
	@echo "  lint          - Run linting on RTL code"
	@echo "  lint_tb       - Run linting on testbench files"
	@echo "  format        - Format SystemVerilog code"
	@echo "  clean         - Clean build artifacts"
	@echo "  test_step1    - Run all Step 1 testbenches with results summary"
	@echo "  tb_fifo       - Run FIFO testbench (verbose)"
	@echo "  tb_credit     - Run credit flow control testbench (verbose)"
	@echo "  tb_arbiter    - Run round-robin arbiter testbench (verbose)"
	@echo "  tb_crc        - Run CRC testbench (verbose)"
	@echo "  tb_assembler  - Run packet assembler testbench (verbose)"
	@echo "  tb_disassembler - Run packet disassembler testbench (verbose)"
	@echo "  tb_integration - Run Step 1 integration testbench (verbose)"
	@echo "  help          - Show this help message"

.PHONY: all compile clean lint lint_tb format help test_step1 tb_fifo tb_credit tb_arbiter tb_crc tb_assembler tb_disassembler tb_integration tb_fifo_quiet tb_credit_quiet tb_arbiter_quiet tb_crc_quiet tb_assembler_quiet tb_disassembler_quiet tb_integration_quiet
