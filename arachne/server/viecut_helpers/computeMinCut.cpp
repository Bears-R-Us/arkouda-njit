#include "computeMinCut.h"
#include <algorithms/global_mincut/cactus/cactus_mincut.h>

int cpp_computeMinCut(int64_t src[], int64_t dst[], int64_t n, int64_t m) {
    // std::cout << "We get here 1!" << std::endl;
    int edge_cut_size = -1;
    auto cfg = configuration::getConfig();
    cfg->find_most_balanced_cut = true;
    cfg->threads = 1;
    cfg->save_cut = true;
    cfg->set_node_in_cut = true;

    std::shared_ptr<mutable_graph> G = std::make_shared<mutable_graph>();
    G->start_construction(n);
    // std::cout << "We get here 2!" << std::endl;
    for(int i = 0; i < n; i ++) {
        NodeID current_node = G->new_node();
        G->setPartitionIndex(current_node, 0);
    }
    // std::cout << "We get here 3!" << std::endl;

    for(int j = 0; j < m; j++) {
        int from_node = src[j];
        int to_node = dst[j];
        int source_node = -1;
        int target_node = -1;
        if(from_node < target_node) {
            source_node = from_node;
            target_node = to_node;
        } else {
            source_node = to_node;
            target_node = from_node;
        }
        G->new_edge(source_node, target_node, 1);
    }
    // std::cout << "We get here 4!" << std::endl;
    G->finish_construction();
    G->computeDegrees();

    // std::cout << "We get here 5!" << std::endl;
    
    cactus_mincut<std::shared_ptr<mutable_graph>> cmc;
    edge_cut_size = cmc.perform_minimum_cut(G);
    // std::cout << "We get here 6!" << std::endl;

    std::vector<int> in_partition;
    std::vector<int> out_partition;

    for(int node_id = 0; node_id < n; node_id++) {
        if(G->getNodeInCut(node_id)) {
            // std::cout << node_id << " is in the cut" << std::endl;
            in_partition.push_back(node_id);
        } else {
            // std::cout << node_id << " is out the cut" << std::endl;
            out_partition.push_back(node_id);
        }
    }
    std::cout << "size of in_partition = " << in_partition.size() << std::endl;
    std::cout << "size of out_partition = " << out_partition.size() << std::endl;

    return edge_cut_size;
}

extern "C" {
    int c_computeMinCut(int64_t src[], int64_t dst[], int64_t n, int64_t m) {
        return cpp_computeMinCut(src, dst, n, m);
    }
}