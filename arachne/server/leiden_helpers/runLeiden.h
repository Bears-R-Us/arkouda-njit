// runLeiden.h // it is ready to add to Arachne
#include <cstdint>
#include <string>
#include <vector>
#include <map>

#ifdef __cplusplus
extern "C" {
#endif
/**
 * @brief Runs the Leiden community detection algorithm on a graph.
 *
 * @param partition_arr       Output array to store cluster assignments.
 *                            Size should be equal to the number of original nodes (n).
 *                            The i-th element corresponds to the cluster ID of the i-th original node.
 * @param src                 Array of source nodes for each edge. Size should be m.
 * @param dst                 Array of destination nodes for each edge. Size should be m.
 * @param n                   Number of nodes in the graph.
 * @param m                   Number of edges in the graph.
 * @param partitionType       Type of partition to use ("CPM", "RBConfiguration", "Modularity").
 * @param resolution          Resolution parameter for the CPM partition type.
 * @param randomSeed          Seed for the random number generator to ensure reproducibility.
 * @param iterations          Number of iterations to perform (-1 for running until convergence).
 * @param original_node_ids   Vector of original node IDs, ordered by internal graph node IDs (0 to n-1).
 *
 * @throws std::invalid_argument If input parameters are inconsistent or invalid.
 * @throws std::runtime_error     If graph construction or algorithm execution fails.
 */
int cpp_runLeiden(int64_t partition_arr[], 
              int64_t src[], 
              int64_t dst[], 
              int64_t n, 
              int64_t m,
              const std::string& partitionType, 
              double resolution, 
              int randomSeed, 
              int iterations,
              const int64_t original_node_ids[]);
int c_runLeiden(int64_t partition_arr[],
                    int64_t src[],
                    int64_t dst[],
                    int64_t n,
                    int64_t m,
                    const char* partitionType,
                    double resolution,
                    int randomSeed,
                    int iterations,
                    const int64_t original_node_ids[]);
#ifdef __cplusplus
}
#endif