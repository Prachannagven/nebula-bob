/*
 * Nebula NoC SystemC TLM-2.0 Testbench
 *
 * Main testbench for the SystemC TLM-2.0 performance model
 */

#include "nebula_noc_tlm.h"
#include <iostream>
#include <fstream>
#include <random>

class PerformanceMonitor : public sc_module {
public:
    SC_CTOR(PerformanceMonitor) :
        total_transactions(0),
        total_latency(0),
        simulation_start_time(SC_ZERO_TIME)
    {
        SC_THREAD(monitoring_process);
    }

    void record_transaction(sc_time latency) {
        total_transactions++;
        total_latency += latency.to_double();
    }

    void monitoring_process() {
        simulation_start_time = sc_time_stamp();

        while (true) {
            wait(sc_time(1000, SC_NS)); // Report every microsecond

            if (total_transactions > 0) {
                double avg_latency_ns = total_latency / total_transactions;
                double throughput = total_transactions /
                    (sc_time_stamp() - simulation_start_time).to_double() * 1e9;

                std::cout << "[" << sc_time_stamp() << "] Performance: "
                    << total_transactions << " transactions, "
                    << "avg latency: " << avg_latency_ns << " ns, "
                    << "throughput: " << throughput << " trans/sec"
                    << std::endl;
            }
        }
    }

private:
    uint64_t total_transactions;
    double total_latency;
    sc_time simulation_start_time;
};

class TrafficGenerator : public sc_module {
public:
    tlm_utils::simple_initiator_socket<TrafficGenerator> initiator_socket;

    SC_CTOR(TrafficGenerator) :
        node_id(0),
        target_node(0),
        transaction_count(0),
        injection_rate(0.1)
    {
        SC_THREAD(traffic_process);
    }

    void configure(uint32_t id, uint32_t target, double rate) {
        node_id = id;
        target_node = target;
        injection_rate = rate;
    }

    void traffic_process() {
        wait(sc_time(100, SC_NS)); // Initial delay

        while (true) {
            if (should_inject()) {
                generate_transaction();
            }
            wait(sc_time(10, SC_NS)); // Check every 10ns
        }
    }

private:
    uint32_t node_id;
    uint32_t target_node;
    uint64_t transaction_count;
    double injection_rate;

    bool should_inject() {
        static std::random_device rd;
        static std::mt19937 gen(rd());
        static std::uniform_real_distribution<> dis(0.0, 1.0);
        return dis(gen) < injection_rate;
    }

    void generate_transaction() {
        tlm_generic_payload* trans = new tlm_generic_payload();
        NebulaExtension* ext = new NebulaExtension();

        // Set transaction properties
        trans->set_command(TLM_READ_COMMAND);
        trans->set_address(0x1000 + transaction_count * 64);
        trans->set_data_length(64);

        ext->source_node_id = node_id;
        ext->dest_node_id = target_node;
        ext->transaction_type = NebulaExtension::AXI_READ;
        ext->packet_id = transaction_count++;
        ext->injection_time = sc_time_stamp();

        trans->set_extension(ext);

        // Send transaction
        sc_time delay = SC_ZERO_TIME;
        initiator_socket->b_transport(*trans, delay);

        std::cout << "[" << sc_time_stamp() << "] TrafficGen[" << node_id
            << "] sent transaction " << transaction_count - 1
            << " to node " << target_node << std::endl;

        delete trans;
    }
};

int sc_main(int argc, char* argv[]) {
    // Parse command line arguments
    uint32_t mesh_width = 4;
    uint32_t mesh_height = 4;
    double injection_rate = 0.1;
    std::string traffic_pattern = "uniform_random";
    uint64_t simulation_time_ns = 10000;

    if (argc > 1) mesh_width = std::atoi(argv[1]);
    if (argc > 2) mesh_height = std::atoi(argv[2]);
    if (argc > 3) injection_rate = std::atof(argv[3]);
    if (argc > 4) traffic_pattern = argv[4];
    if (argc > 5) simulation_time_ns = std::atoll(argv[5]);

    std::cout << "Nebula NoC SystemC TLM-2.0 Simulation" << std::endl;
    std::cout << "=====================================" << std::endl;
    std::cout << "Mesh: " << mesh_width << "x" << mesh_height << std::endl;
    std::cout << "Traffic pattern: " << traffic_pattern << std::endl;
    std::cout << "Injection rate: " << injection_rate << std::endl;
    std::cout << "Simulation time: " << simulation_time_ns << " ns" << std::endl;
    std::cout << "=====================================" << std::endl;

    // Create topology
    NebulaTopology topology("nebula_topology");
    topology.configure(mesh_width, mesh_height);
    topology.set_traffic_pattern(traffic_pattern, injection_rate);

    // Create performance monitor
    PerformanceMonitor monitor("performance_monitor");

    // Enable tracing
    sc_trace_file* tf = sc_create_vcd_trace_file("nebula_tlm_trace");

    // Run simulation
    std::cout << "Starting simulation..." << std::endl;
    sc_start(sc_time(simulation_time_ns, SC_NS));

    std::cout << "Simulation completed." << std::endl;

    // Close trace file
    sc_close_vcd_trace_file(tf);

    return 0;
}
