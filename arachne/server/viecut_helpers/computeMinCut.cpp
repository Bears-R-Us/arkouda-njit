#include "computeMinCut.h"
#include <algorithms/global_mincut/cactus/cactus_mincut.h>

int cpp_computeMinCut(int64_t src[], int64_t dst[], int64_t n, int64_t m) {
    int edge_cut_size = -1;
    std::shared_ptr<mutable_graph> G = std::make_shared<mutable_graph>();
    G->start_construction(n);
    for(int i = 0; i < n; i ++) {
        NodeID current_node = G->new_node();
        G->setPartitionIndex(current_node, 0);
    }

    for(int j = 0; j < m; j++) {
        G->new_edge(src[j], dst[j], 1);
    }
    G->finish_construction();
    G->computeDegrees();
    
    cactus_mincut<std::shared_ptr<mutable_graph>> cmc;
    edge_cut_size = cmc.perform_minimum_cut(G);

    return edge_cut_size;
}

extern "C" {
    int c_computeMinCut(int64_t src[], int64_t dst[], int64_t n, int64_t m) {
        return cpp_computeMinCut(src, dst, n, m);
    }
}