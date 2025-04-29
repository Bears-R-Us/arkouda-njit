#ifndef COMPUTELEIDEN_H
#define COMPUTELEIDEN_H

#include <stdint.h>

typedef double float64_t;

enum ModularityType : int64_t {
    CPM,
    MODULARITY,
    SIGNIFICANCE,
    SURPRISE,
    RBCONFIGURATION,
    RBER
};

#ifdef __cplusplus
extern "C" {
#endif

void compute_leiden(
    const int64_t src[], 
    const int64_t dst[], 
    int64_t NumEdges, 
    int64_t NumNodes, 
    int64_t modularity_option, 
    float64_t resolution, 
    int64_t communities[], 
    int64_t numCommunities
);

// C wrapper for Chapel
int64_t c_computeLeiden(
    const int64_t src[], 
    const int64_t dst[], 
    int64_t NumEdges, 
    int64_t NumNodes, 
    int64_t modularity_option, 
    float64_t resolution, 
    int64_t communities[], 
    int64_t numCommunities
);

#ifdef __cplusplus
}
#endif

#endif // RUN_LEIDEN_H