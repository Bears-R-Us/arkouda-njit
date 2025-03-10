import networkx as nx

# Load edges into a graph
def load_graph(edge_file):
    G = nx.Graph()
    with open(edge_file, 'r') as f:
        for line in f:
            src, dst = map(int, line.strip().split())
            G.add_edge(src, dst)
    return G

# Load nodes and their cluster assignments
def load_clusters(cluster_file):
    clusters = {}
    with open(cluster_file, 'r') as f:
        for line in f:
            node, cluster_id = map(int, line.strip().split())
            if cluster_id not in clusters:
                clusters[cluster_id] = set()
            clusters[cluster_id].add(node)
    return clusters

# Check connectivity of each cluster
def check_clusters_connectivity(G, clusters):
    results = {}
    for cluster_id, nodes in clusters.items():
        subgraph = G.subgraph(nodes)
        connected = nx.is_connected(subgraph)
        print(f"Cluster {cluster_id}: {'Connected' if connected else 'Not Connected'}")
        
# Example usage
edge_file = '/home/md724/testFolder/wcc_inputs/networks/cen_0.01_cm_v1_sample_0.tsv'
cluster_file = ' /home/md724/arkouda-njit/arachne/output/log10_test_network_wcc_output_post.tsv'

G = load_graph(edge_file)
clusters = load_clusters(cluster_file)

check_clusters_connectivity(G, clusters)
