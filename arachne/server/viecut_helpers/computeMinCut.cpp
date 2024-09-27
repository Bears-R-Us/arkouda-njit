#include "computeMinCut.h"
#include <algorithms/global_mincut/cactus/cactus_mincut.h>

int cpp_computeMinCut(int64_t partition_arr[], int64_t src[], int64_t dst[], int64_t n, int64_t m) {
    int edge_cut_size = -1;
    auto cfg = configuration::getConfig();
    cfg->find_most_balanced_cut = true;
    cfg->threads = 1;
    cfg->save_cut = true;
    cfg->set_node_in_cut = true;

    std::shared_ptr<mutable_graph> G = std::make_shared<mutable_graph>();
    G->start_construction(n);
    for(int i = 0; i < n; i ++) {
        NodeID current_node = G->new_node();
        G->setPartitionIndex(current_node, 0);
    }

    for(int j = 0; j < m; j++) {
        int from_node = src[j], to_node = dst[j];
        int source_node = -1, target_node = -1;
        if(from_node < target_node) {
            source_node = from_node;
            target_node = to_node;
        } else {
            source_node = to_node;
            target_node = from_node;
        }
        G->new_edge(source_node, target_node, 1);
    }
    G->finish_construction();
    G->computeDegrees();
    
    cactus_mincut<std::shared_ptr<mutable_graph>> cmc;
    edge_cut_size = cmc.perform_minimum_cut(G);

    for(int node_id = 0; node_id < n; node_id++) {
        if(G->getNodeInCut(node_id)) {
            partition_arr[node_id] = 1;
        } else {
            partition_arr[node_id] = 0;
        }
    }
    return edge_cut_size;
}

extern "C" {
    int c_computeMinCut(int64_t partition_arr[], int64_t src[], int64_t dst[], int64_t n, int64_t m) {
        return cpp_computeMinCut(partition_arr, src, dst, n, m);
    }
}