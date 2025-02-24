import os
import networkx as nx

def generate_directed_graph_networkx(file_path, num_nodes, p):
    # Create a random directed graph using the G(n, p) model
    G = nx.gnp_random_graph(num_nodes, p, directed=True)
    
    # Automatically generate the file name in the format "random_P_NumberOfNodes.txt"
    file_name = f"random_{p}_{num_nodes}.txt"
    full_path = os.path.join(file_path, file_name)
    
    with open(full_path, 'w') as f:
        # Write the number of nodes as the first line
        f.write(f"{num_nodes}\n")
        
        # Write each edge as a tab-separated pair (source, destination)
        for src, dst in G.edges():
            f.write(f"{src}\t{dst}\n")
    
    print(f"Graph generated and saved at: {full_path}")

def main():
    # Set your file path
    file_path = "/mmfs1/home/md724/arkouda-njit/arachne/data/motifCounting/"
    
    # Set the number of nodes and the edge probability
    num_nodes = 1000
    p = 0.05
    
    generate_directed_graph_networkx(file_path, num_nodes, p)

if __name__ == "__main__":
    main()
