import networkx as nx
from PIL import Image

# Function to convert an image to a directed graph
def image_to_directed_graph(image_path):
    img = Image.open(image_path)
    width, height = img.size
    G = nx.DiGraph()  # Creating a directed graph

    # Add nodes for each pixel
    for y in range(height):
        for x in range(width):
            pixel = img.getpixel((x, y))
            G.add_node((x, y), color=pixel)

    # Connect adjacent pixels as directed edges
    for y in range(height):
        for x in range(width):
            if x < width - 1:
                G.add_edge((x, y), (x + 1, y))
            if y < height - 1:
                G.add_edge((x, y), (x, y + 1))

    return G

# Example image paths
image_path_main = 'a.jpg'
image_path_sub = 'b.jpg'

# Create directed graphs from images
main_digraph = image_to_directed_graph(image_path_main)
subgraph_digraph = image_to_directed_graph(image_path_sub)

# Run VF2 algorithm for directed graph matching
vf2_matcher_digraph = nx.algorithms.isomorphism.DiGraphMatcher(main_digraph, subgraph_digraph)
matches_digraph = vf2_matcher_digraph.subgraph_is_isomorphic()

if matches_digraph:
    print("Subgraph found in the main directed graph!")
else:
    print("Subgraph not found in the main directed graph.")
