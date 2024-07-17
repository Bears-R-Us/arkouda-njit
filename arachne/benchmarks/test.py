import arkouda as ak
from collections import deque, defaultdict

# Connect to the Arkouda server
ak.connect("n116", 5555)

def compute_degrees(src, dst):
    # Find unique nodes
    unique_nodes = ak.unique(ak.concatenate([src, dst]))
    
    # Initialize degree arrays
    in_degree = ak.zeros(len(unique_nodes), dtype=ak.int64)
    out_degree = ak.zeros(len(unique_nodes), dtype=ak.int64)
    
    # Convert Arkouda arrays to Python lists for iteration
    unique_nodes_list = unique_nodes.to_list()
    
    # Create a dictionary to map nodes to their index in unique_nodes
    node_to_index = {node: idx for idx, node in enumerate(unique_nodes_list)}
    
    # Calculate out-degrees
    for node in src.to_list():
        out_degree[node_to_index[node]] += 1
    
    # Calculate in-degrees
    for node in dst.to_list():
        in_degree[node_to_index[node]] += 1
    
    # Calculate total degrees
    total_degree = in_degree + out_degree
    
    return unique_nodes_list, node_to_index, in_degree.to_list(), out_degree.to_list(), total_degree.to_list()

def bfs_tree(src, dst, root, node_to_index):
    # Create adjacency list
    adj_list = defaultdict(list)
    for i in range(len(src)):
        adj_list[src[i]].append(dst[i])
    
    # BFS traversal to create BFS tree
    bfs_tree = defaultdict(list)
    visited = set()
    queue = deque([root])
    visited.add(root)
    
    while queue:
        node = queue.popleft()
        for neighbor in adj_list[node]:
            if neighbor not in visited:
                visited.add(neighbor)
                queue.append(neighbor)
                bfs_tree[node].append(neighbor)
    
    return bfs_tree

def vf2pp_ordering(src, dst):
    # Compute degrees
    unique_nodes_list, node_to_index, in_degree, out_degree, total_degree = compute_degrees(src, dst)
    
    # Step 1: Select the initial vertex with the highest degree
    candidates = [(unique_nodes_list[i], total_degree[i]) for i in range(len(unique_nodes_list))]
    candidates.sort(key=lambda x: -x[1])
    
    if not candidates:
        return [], [], [], []
    
    root = candidates[0][0]
    
    print(f"Initial Selected Root: {root}")
    
    # Step 2: Construct BFS tree
    bfs_tree_dict = bfs_tree(src, dst, root, node_to_index)
    
    # Step 3: Process vertices level-by-level from the BFS tree
    order = []
    queue = deque([root])
    visited = set([root])
    
    while queue:
        node = queue.popleft()
        order.append(node)
        neighbors = bfs_tree_dict[node]
        # Sort neighbors by degree and add to queue
        neighbors.sort(key=lambda x: (-total_degree[node_to_index[x]], -out_degree[node_to_index[x]]))
        for neighbor in neighbors:
            if neighbor not in visited:
                visited.add(neighbor)
                queue.append(neighbor)
    
    # Generate new src and dst based on order
    new_node_indices = {node: i for i, node in enumerate(order)}
    new_src = [new_node_indices[node] for node in src.to_list()]
    new_dst = [new_node_indices[node] for node in dst.to_list()]
    
    return ak.array(new_src), ak.array(new_dst), order, unique_nodes_list

# Testing the function
src_subgraph = ak.array([0, 1, 2, 1])
dst_subgraph = ak.array([1, 2, 0, 3])

updated_src, updated_dst, order, unique_nodes_list = vf2pp_ordering(src_subgraph, dst_subgraph)

print("\nFinal Results:")
print("Unique Nodes:", unique_nodes_list)
print("Order:", order)
print("Updated src:", updated_src.to_list())
print("Updated dst:", updated_dst.to_list())
