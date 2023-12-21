import networkx as nx
from PIL import Image

# Function to convert an image to a graph
def image_to_graph(image_path):
    img = Image.open(image_path)
    width, height = img.size
    G = nx.Graph()

    # Add nodes for each pixel
    for y in range(height):
        for x in range(width):
            pixel = img.getpixel((x, y))
            G.add_node((x, y), color=pixel)

    # Connect adjacent pixels as edges
    for y in range(height):
        for x in range(width):
            if x < width - 1:
                G.add_edge((x, y), (x + 1, y))
            if y < height - 1:
                G.add_edge((x, y), (x, y + 1))

    return G
print("here")
# Example image paths
image_path_main = 'a.jpg'
image_path_sub = 'b.jpg'

# Create graphs from images
main_graph = image_to_graph(image_path_main)
print("main_graph done")
subgraph = image_to_graph(image_path_sub)
print("subgraph done")

# Run VF2 algorithm for graph matching
vf2_matcher = nx.algorithms.isomorphism.GraphMatcher(main_graph, subgraph)
matches = vf2_matcher.subgraph_is_isomorphic()

if matches:
    print("Subgraph found in the main graph!")
else:
    print("Subgraph not found in the main graph.")
