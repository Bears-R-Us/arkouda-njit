#include <iostream>
#include "igraph/igraph.h"
#include "libleidenalg/Optimiser.h"
#include "libleidenalg/CPMVertexPartition.h"
#include "libleidenalg/ModularityVertexPartition.h"
#include "libleidenalg/SignificanceVertexPartition.h"
#include "libleidenalg/SurpriseVertexPartition.h"
#include "libleidenalg/RBConfigurationVertexPartition.h"
#include "libleidenalg/RBERVertexPartition.h"
#include "computeLeiden.h"

void compute_leiden(
    const int64_t src[], 
    const int64_t dst[], 
    int64_t NumEdges, 
    int64_t NumNodes, 
    int64_t modularity_option, 
    float64_t resolution, 
    int64_t communities[], 
    int64_t numCommunities
) {
    igraph_t g;
    igraph_vector_int_t edges;
    igraph_vector_int_init(&edges, NumEdges * 2);

    for (int64_t i = 0; i < NumEdges; i++) {
        VECTOR(edges)[2 * i] = src[i];
        VECTOR(edges)[2 * i + 1] = dst[i];
    }

    igraph_create(&g, &edges, NumNodes, IGRAPH_DIRECTED);
    igraph_vector_int_destroy(&edges);

    Graph graph(&g);

    MutableVertexPartition* partition = nullptr;
    switch (modularity_option) {
        case CPM:
            partition = new CPMVertexPartition(&graph, resolution);
            break;
        case MODULARITY:
            partition = new ModularityVertexPartition(&graph);
            break;
        case SIGNIFICANCE:
            partition = new SignificanceVertexPartition(&graph);
            break;
        case SURPRISE:
            partition = new SurpriseVertexPartition(&graph);
            break;
        case RBCONFIGURATION:
            partition = new RBConfigurationVertexPartition(&graph, resolution);
            break;
        case RBER:
            partition = new RBERVertexPartition(&graph, resolution);
            break;
        default:
            std::cerr << "Error: Invalid modularity option selected." << std::endl;
            igraph_destroy(&g);
            return;
    }

    Optimiser optimiser;
    optimiser.optimise_partition(partition);

    // numCommunities = 0;
    // for (int64_t i = 0; i < NumNodes; i++) {
    //     communities[i] = partition->membership(i);
    //     if (communities[i] > numCommunities) {
    //         numCommunities = communities[i];
    //     }
    // }

    // numCommunities += 1;

    //std::cout << "Leiden clustering complete. Found " << numCommunities << " communities." << std::endl;

    delete partition;
    igraph_destroy(&g);
}

// C-compatible wrapper for Chapel
int64_t c_computeLeiden(
    const int64_t src[], 
    const int64_t dst[], 
    int64_t NumEdges, 
    int64_t NumNodes, 
    int64_t modularity_option, 
    float64_t resolution, 
    int64_t communities[], 
    int64_t numCommunities
) {
    //std::cout << "Calling run_leiden from Chapel..." << std::endl;
    compute_leiden(src, dst, NumEdges, NumNodes, modularity_option, resolution, communities, numCommunities);
    return numCommunities;
}