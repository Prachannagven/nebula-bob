/*
 * Nebula NoC SystemC TLM-2.0 Performance Model
 *
 * This SystemC TLM-2.0 model provides transaction-level modeling
 * of the Nebula GPU interconnect for rapid performance analysis.
 *
 * Features:
 * - Transaction-level modeling with accurate timing
 * - Configurable mesh topology and routing
 * - AXI4 and CHI protocol transaction support
 * - Performance monitoring and statistics
 * - Co-simulation capabilities with RTL
 */

#ifndef NEBULA_NOC_TLM_H
#define NEBULA_NOC_TLM_H

#include <systemc>
#include <tlm>
#include <tlm_utils/simple_initiator_socket.h>
#include <tlm_utils/simple_target_socket.h>
#include <map>
#include <vector>
#include <queue>
#include <string>
#include <iostream>
#include <fstream>

using namespace sc_core;
using namespace tlm;

// Forward declarations
class NebulaRouter;
class NebulaNode;
class NebulaTopology;
class PerformanceMonitor;

// ============================================================================
// TLM Transaction Extensions for Nebula NoC
// ============================================================================

class NebulaExtension : public tlm_extension<NebulaExtension> {
public:
    enum TransactionType {
        AXI_READ,
        AXI_WRITE,
        CHI_READ_SHARED,
        CHI_READ_UNIQUE,
        CHI_WRITE_UNIQUE,
        CHI_SNOOP,
        CHI_RESPONSE
    };

    enum Priority {
        LOW = 0,
        NORMAL = 1,
        HIGH = 2,
        URGENT = 3
    };

    NebulaExtension() :
        transaction_type(AXI_READ),
        source_node_id(0),
        dest_node_id(0),
        priority(NORMAL),
        virtual_channel(0),
        sequence_number(0),
        packet_id(0),
        injection_time(SC_ZERO_TIME) {    
}

    virtual tlm_extension_base* clone() const override {
        NebulaExtension* ext = new NebulaExtension();
        ext->transaction_type = this->transaction_type;
        ext->source_node_id = this->source_node_id;
        ext->dest_node_id = this->dest_node_id;
        ext->priority = this->priority;
        ext->virtual_channel = this->virtual_channel;
        ext->sequence_number = this->sequence_number;
        ext->packet_id = this->packet_id;
        ext->injection_time = this->injection_time;
        return ext;
    }

    virtual void copy_from(const tlm_extension_base& ext) override {
        const NebulaExtension& nebula_ext = static_cast<const NebulaExtension&>(ext);
        transaction_type = nebula_ext.transaction_type;
        source_node_id = nebula_ext.source_node_id;
        dest_node_id = nebula_ext.dest_node_id;
        priority = nebula_ext.priority;
        virtual_channel = nebula_ext.virtual_channel;
        sequence_number = nebula_ext.sequence_number;
        packet_id = nebula_ext.packet_id;
        injection_time = nebula_ext.injection_time;
    }

    TransactionType transaction_type;
    uint32_t source_node_id;
    uint32_t dest_node_id;
    Priority priority;
    uint32_t virtual_channel;
    uint64_t sequence_number;
    uint64_t packet_id;
    sc_time injection_time;
};

// ============================================================================
// Router TLM Model
// ============================================================================

class NebulaRouter : public sc_module {
public:
    // TLM sockets for 5 directions: North, South, East, West, Local
    tlm_utils::simple_target_socket<NebulaRouter> north_in;
    tlm_utils::simple_target_socket<NebulaRouter> south_in;
    tlm_utils::simple_target_socket<NebulaRouter> east_in;
    tlm_utils::simple_target_socket<NebulaRouter> west_in;
    tlm_utils::simple_target_socket<NebulaRouter> local_in;

    tlm_utils::simple_initiator_socket<NebulaRouter> north_out;
    tlm_utils::simple_initiator_socket<NebulaRouter> south_out;
    tlm_utils::simple_initiator_socket<NebulaRouter> east_out;
    tlm_utils::simple_initiator_socket<NebulaRouter> west_out;
    tlm_utils::simple_initiator_socket<NebulaRouter> local_out;

    SC_CTOR(NebulaRouter) :
        router_id(0),
        x_coord(0),
        y_coord(0),
        mesh_width(4),
        mesh_height(4),
        total_packets_routed(0),
        total_latency_cycles(0)
    {
        // Register TLM transport methods
        north_in.register_b_transport(this, &NebulaRouter::b_transport);
        south_in.register_b_transport(this, &NebulaRouter::b_transport);
        east_in.register_b_transport(this, &NebulaRouter::b_transport);
        west_in.register_b_transport(this, &NebulaRouter::b_transport);
        local_in.register_b_transport(this, &NebulaRouter::b_transport);

        SC_THREAD(statistics_process);
    }

    void configure(uint32_t id, uint32_t x, uint32_t y, uint32_t width, uint32_t height) {
        router_id = id;
        x_coord = x;
        y_coord = y;
        mesh_width = width;
        mesh_height = height;
    }

    virtual void b_transport(tlm_generic_payload& trans, sc_time& delay) {
        // Extract Nebula extension
        NebulaExtension* ext = trans.get_extension<NebulaExtension>();
        if (!ext) {
            SC_REPORT_ERROR("NebulaRouter", "Missing NebulaExtension");
            trans.set_response_status(TLM_GENERIC_ERROR_RESPONSE);
            return;
        }

        // Calculate routing decision
        uint32_t dest_x = ext->dest_node_id % mesh_width;
        uint32_t dest_y = ext->dest_node_id / mesh_width;

        // XY routing algorithm
        tlm_utils::simple_initiator_socket<NebulaRouter>* output_port = nullptr;
        sc_time routing_delay = sc_time(1, SC_NS); // Base routing delay

        if (dest_x == x_coord && dest_y == y_coord) {
            // Local delivery
            output_port = &local_out;
        }
        else if (dest_x != x_coord) {
            // Route in X dimension first
            if (dest_x > x_coord) {
                output_port = &east_out;
            }
            else {
                output_port = &west_out;
            }
        }
        else {
            // Route in Y dimension
            if (dest_y > y_coord) {
                output_port = &south_out;
            }
            else {
                output_port = &north_out;
            }
        }

        // Add router-specific delays
        switch (ext->transaction_type) {
        case NebulaExtension::AXI_READ:
        case NebulaExtension::AXI_WRITE:
            routing_delay += sc_time(2, SC_NS); // AXI processing
            break;
        case NebulaExtension::CHI_READ_SHARED:
        case NebulaExtension::CHI_READ_UNIQUE:
        case NebulaExtension::CHI_WRITE_UNIQUE:
            routing_delay += sc_time(3, SC_NS); // CHI processing
            break;
        case NebulaExtension::CHI_SNOOP:
        case NebulaExtension::CHI_RESPONSE:
            routing_delay += sc_time(1, SC_NS); // Snoop/response processing
            break;
        }

        // Add congestion-based delay (simplified model)
        if (total_packets_routed % 100 == 0 && total_packets_routed > 0) {
            routing_delay += sc_time(5, SC_NS); // Congestion penalty
        }

        // Forward transaction
        delay += routing_delay;
        if (output_port && output_port->get_base_port().size() > 0) {
            (*output_port)->b_transport(trans, delay);
        }
        else {
            // Dead end - this shouldn't happen in a properly connected mesh
            SC_REPORT_WARNING("NebulaRouter", "No valid output port found");
            trans.set_response_status(TLM_GENERIC_ERROR_RESPONSE);
        }

        // Update statistics
        total_packets_routed++;
        sc_time current_latency = sc_time_stamp() + delay - ext->injection_time;
        total_latency_cycles += current_latency.to_double() / 1e-9; // Convert to cycles (1GHz)

        trans.set_response_status(TLM_OK_RESPONSE);
    }

    void statistics_process() {
        while (true) {
            wait(sc_time(1000, SC_NS)); // Report every 1000ns

            if (total_packets_routed > 0) {
                double avg_latency = total_latency_cycles / total_packets_routed;
                std::cout << "Router[" << router_id << "] @ (" << x_coord << "," << y_coord
                    << "): " << total_packets_routed << " packets, avg latency: "
                    << avg_latency << " cycles" << std::endl;
            }
        }
    }

private:
    uint32_t router_id;
    uint32_t x_coord, y_coord;
    uint32_t mesh_width, mesh_height;
    uint64_t total_packets_routed;
    double total_latency_cycles;
};

// ============================================================================
// Node TLM Model (combines NIU, AXI/CHI interfaces)
// ============================================================================

class NebulaNode : public sc_module {
public:
    // Connection to local router
    tlm_utils::simple_initiator_socket<NebulaNode> router_out;
    tlm_utils::simple_target_socket<NebulaNode> router_in;

    // External interfaces
    tlm_utils::simple_target_socket<NebulaNode> axi_target;
    tlm_utils::simple_target_socket<NebulaNode> chi_target;

    SC_CTOR(NebulaNode) :
        node_id(0),
        x_coord(0),
        y_coord(0),
        mesh_width(4),
        mesh_height(4),
        packet_id_counter(0),
        axi_transactions(0),
        chi_transactions(0)
    {
        // Register TLM transport methods
        router_in.register_b_transport(this, &NebulaNode::router_b_transport);
        axi_target.register_b_transport(this, &NebulaNode::axi_b_transport);
        chi_target.register_b_transport(this, &NebulaNode::chi_b_transport);

        SC_THREAD(traffic_generation_process);
    }

    void configure(uint32_t id, uint32_t x, uint32_t y, uint32_t width, uint32_t height) {
        node_id = id;
        x_coord = x;
        y_coord = y;
        mesh_width = width;
        mesh_height = height;
    }

    void set_traffic_pattern(const std::string& pattern, double injection_rate) {
        traffic_pattern = pattern;
        this->injection_rate = injection_rate;
    }

    virtual void router_b_transport(tlm_generic_payload& trans, sc_time& delay) {
        // Handle incoming transactions from the network
        NebulaExtension* ext = trans.get_extension<NebulaExtension>();
        if (!ext) {
            trans.set_response_status(TLM_GENERIC_ERROR_RESPONSE);
            return;
        }

        // Process transaction based on type
        sc_time processing_delay = sc_time(5, SC_NS); // Base processing delay

        switch (ext->transaction_type) {
        case NebulaExtension::AXI_READ:
            // Simulate memory read
            processing_delay += sc_time(20, SC_NS);
            break;
        case NebulaExtension::AXI_WRITE:
            // Simulate memory write
            processing_delay += sc_time(15, SC_NS);
            break;
        case NebulaExtension::CHI_READ_SHARED:
        case NebulaExtension::CHI_READ_UNIQUE:
            // Simulate cache lookup
            processing_delay += sc_time(10, SC_NS);
            break;
        case NebulaExtension::CHI_WRITE_UNIQUE:
            // Simulate cache write
            processing_delay += sc_time(12, SC_NS);
            break;
        default:
            processing_delay += sc_time(5, SC_NS);
            break;
        }

        delay += processing_delay;
        trans.set_response_status(TLM_OK_RESPONSE);

        std::cout << "[" << sc_time_stamp() << "] Node[" << node_id
            << "] processed " << transaction_type_to_string(ext->transaction_type)
            << " from node " << ext->source_node_id << std::endl;
    }

    virtual void axi_b_transport(tlm_generic_payload& trans, sc_time& delay) {
        // Convert AXI transaction to NoC transaction
        NebulaExtension* ext = new NebulaExtension();

        if (trans.get_command() == TLM_READ_COMMAND) {
            ext->transaction_type = NebulaExtension::AXI_READ;
        }
        else {
            ext->transaction_type = NebulaExtension::AXI_WRITE;
        }

        ext->source_node_id = node_id;
        ext->dest_node_id = address_to_node_id(trans.get_address());
        ext->priority = NebulaExtension::NORMAL;
        ext->packet_id = packet_id_counter++;
        ext->injection_time = sc_time_stamp();

        trans.set_extension(ext);

        // Forward to router
        sc_time routing_delay = sc_time(2, SC_NS);
        router_out->b_transport(trans, routing_delay);
        delay += routing_delay;

        axi_transactions++;
    }

    virtual void chi_b_transport(tlm_generic_payload& trans, sc_time& delay) {
        // Convert CHI transaction to NoC transaction
        NebulaExtension* ext = new NebulaExtension();

        // Simplified CHI transaction type mapping
        if (trans.get_command() == TLM_READ_COMMAND) {
            ext->transaction_type = NebulaExtension::CHI_READ_SHARED;
        }
        else {
            ext->transaction_type = NebulaExtension::CHI_WRITE_UNIQUE;
        }

        ext->source_node_id = node_id;
        ext->dest_node_id = address_to_node_id(trans.get_address());
        ext->priority = NebulaExtension::HIGH; // CHI has higher priority
        ext->packet_id = packet_id_counter++;
        ext->injection_time = sc_time_stamp();

        trans.set_extension(ext);

        // Forward to router
        sc_time routing_delay = sc_time(3, SC_NS);
        router_out->b_transport(trans, routing_delay);
        delay += routing_delay;

        chi_transactions++;
    }

    void traffic_generation_process() {
        wait(sc_time(100, SC_NS)); // Initial delay

        while (true) {
            // Generate traffic based on pattern
            if (should_inject_traffic()) {
                generate_traffic_transaction();
            }

            // Wait for next injection opportunity
            wait(sc_time(10, SC_NS));
        }
    }

private:
    uint32_t node_id;
    uint32_t x_coord, y_coord;
    uint32_t mesh_width, mesh_height;
    uint64_t packet_id_counter;
    uint64_t axi_transactions;
    uint64_t chi_transactions;

    std::string traffic_pattern = "uniform_random";
    double injection_rate = 0.1;

    uint32_t address_to_node_id(uint64_t address) {
        // Simple address mapping: use upper bits for node ID
        return (address >> 20) % (mesh_width * mesh_height);
    }

    bool should_inject_traffic() {
        static std::random_device rd;
        static std::mt19937 gen(rd());
        static std::uniform_real_distribution<> dis(0.0, 1.0);

        return dis(gen) < injection_rate;
    }

    void generate_traffic_transaction() {
        // Create a synthetic transaction for traffic generation
        tlm_generic_payload* trans = new tlm_generic_payload();
        NebulaExtension* ext = new NebulaExtension();

        // Generate destination based on traffic pattern
        uint32_t dest_node;
        if (traffic_pattern == "uniform_random") {
            dest_node = rand() % (mesh_width * mesh_height);
            while (dest_node == node_id) {
                dest_node = rand() % (mesh_width * mesh_height);
            }
        }
        else if (traffic_pattern == "hotspot") {
            // 80% traffic to center nodes
            if ((rand() % 100) < 80) {
                dest_node = (mesh_width * mesh_height) / 2; // Center node
            }
            else {
                dest_node = rand() % (mesh_width * mesh_height);
            }
        }
        else {
            dest_node = rand() % (mesh_width * mesh_height);
        }

        // Set transaction properties
        trans->set_command((rand() % 2 == 0) ? TLM_READ_COMMAND : TLM_WRITE_COMMAND);
        trans->set_address(dest_node << 20); // Embed destination in address
        trans->set_data_length(64); // 64-byte packets

        ext->source_node_id = node_id;
        ext->dest_node_id = dest_node;
        ext->transaction_type = (rand() % 2 == 0) ?
            NebulaExtension::AXI_READ : NebulaExtension::CHI_READ_SHARED;
        ext->packet_id = packet_id_counter++;
        ext->injection_time = sc_time_stamp();

        trans->set_extension(ext);

        // Inject into network
        sc_time delay = SC_ZERO_TIME;
        router_out->b_transport(*trans, delay);

        std::cout << "[" << sc_time_stamp() << "] Node[" << node_id
            << "] injected traffic to node " << dest_node << std::endl;
    }

    std::string transaction_type_to_string(NebulaExtension::TransactionType type) {
        switch (type) {
        case NebulaExtension::AXI_READ: return "AXI_READ";
        case NebulaExtension::AXI_WRITE: return "AXI_WRITE";
        case NebulaExtension::CHI_READ_SHARED: return "CHI_READ_SHARED";
        case NebulaExtension::CHI_READ_UNIQUE: return "CHI_READ_UNIQUE";
        case NebulaExtension::CHI_WRITE_UNIQUE: return "CHI_WRITE_UNIQUE";
        case NebulaExtension::CHI_SNOOP: return "CHI_SNOOP";
        case NebulaExtension::CHI_RESPONSE: return "CHI_RESPONSE";
        default: return "UNKNOWN";
        }
    }
};

// ============================================================================
// Top-Level Mesh Topology
// ============================================================================

class NebulaTopology : public sc_module {
public:
    std::vector<std::vector<NebulaRouter*>> routers;
    std::vector<NebulaNode*> nodes;

    SC_CTOR(NebulaTopology) : mesh_width(4), mesh_height(4) {
        build_topology();
        connect_topology();
    }

    void configure(uint32_t width, uint32_t height) {
        mesh_width = width;
        mesh_height = height;
        build_topology();
        connect_topology();
    }

    void set_traffic_pattern(const std::string& pattern, double injection_rate) {
        for (auto& node : nodes) {
            node->set_traffic_pattern(pattern, injection_rate);
        }
    }

private:
    uint32_t mesh_width, mesh_height;

    void build_topology() {
        // Create routers in 2D grid
        routers.resize(mesh_height);
        for (uint32_t y = 0; y < mesh_height; y++) {
            routers[y].resize(mesh_width);
            for (uint32_t x = 0; x < mesh_width; x++) {
                uint32_t router_id = y * mesh_width + x;
                std::string router_name = "router_" + std::to_string(router_id);

                routers[y][x] = new NebulaRouter(router_name.c_str());
                routers[y][x]->configure(router_id, x, y, mesh_width, mesh_height);
            }
        }

        // Create nodes (one per router)
        nodes.resize(mesh_width * mesh_height);
        for (uint32_t i = 0; i < mesh_width * mesh_height; i++) {
            uint32_t x = i % mesh_width;
            uint32_t y = i / mesh_width;
            std::string node_name = "node_" + std::to_string(i);

            nodes[i] = new NebulaNode(node_name.c_str());
            nodes[i]->configure(i, x, y, mesh_width, mesh_height);
        }
    }

    void connect_topology() {
        // Connect routers in mesh topology
        for (uint32_t y = 0; y < mesh_height; y++) {
            for (uint32_t x = 0; x < mesh_width; x++) {
                NebulaRouter* current = routers[y][x];

                // North connection
                if (y > 0) {
                    current->north_out.bind(routers[y - 1][x]->south_in);
                }

                // South connection  
                if (y < mesh_height - 1) {
                    current->south_out.bind(routers[y + 1][x]->north_in);
                }

                // East connection
                if (x < mesh_width - 1) {
                    current->east_out.bind(routers[y][x + 1]->west_in);
                }

                // West connection
                if (x > 0) {
                    current->west_out.bind(routers[y][x - 1]->east_in);
                }

                // Local connection to node
                uint32_t node_id = y * mesh_width + x;
                current->local_out.bind(nodes[node_id]->router_in);
                nodes[node_id]->router_out.bind(current->local_in);
            }
        }
    }
};

#endif // NEBULA_NOC_TLM_H
