# Nebula SystemC TLM-2.0 Makefile

# SystemC installation path
SYSTEMC_HOME ?= /usr/local/systemc-2.3.3

# Compiler settings
CXX = g++
CXXFLAGS = -std=c++11 -Wall -O3
INCLUDES = -I$(SYSTEMC_HOME)/include -I.
LDFLAGS = -L$(SYSTEMC_HOME)/lib-linux64
LIBS = -lsystemc -lm

# Target executable
TARGET = nebula_tlm_sim

# Source files
SOURCES = nebula_testbench.cpp
HEADERS = nebula_noc_tlm.h

# Object files
OBJECTS = $(SOURCES:.cpp=.o)

.PHONY: all clean run help

all: $(TARGET)

$(TARGET): $(OBJECTS)
	$(CXX) $(LDFLAGS) -o $@ $^ $(LIBS)

%.o: %.cpp $(HEADERS)
	$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

clean:
	rm -f $(OBJECTS) $(TARGET) *.vcd *.wlf transcript vsim.wlf

run: $(TARGET)
	./$(TARGET) 4 4 0.1 uniform_random 50000

run-hotspot: $(TARGET)
	./$(TARGET) 4 4 0.2 hotspot 50000

run-large: $(TARGET)
	./$(TARGET) 8 8 0.05 uniform_random 100000

help:
	@echo "Nebula SystemC TLM-2.0 Build System"
	@echo "==================================="
	@echo "Targets:"
	@echo "  all        - Build the TLM simulator"
	@echo "  run        - Run 4x4 mesh with uniform random traffic"
	@echo "  run-hotspot- Run 4x4 mesh with hotspot traffic"
	@echo "  run-large  - Run 8x8 mesh with low injection rate"
	@echo "  clean      - Remove build artifacts"
	@echo "  help       - Show this help message"
	@echo ""
	@echo "Usage: ./$(TARGET) <width> <height> <injection_rate> <pattern> <time_ns>"
	@echo "Example: ./$(TARGET) 4 4 0.1 uniform_random 10000"
	@echo ""
	@echo "Patterns: uniform_random, hotspot"
