    import networkx as nx
    import time

    # Connect to the Arkouda server.
    ak.verbose = False
    ak.connect(args.hostname, args.port)
    
    # Creating directed graphs
    G = nx.DiGraph()
    H = nx.DiGraph()

    # Clearing graphs (optional in this context)
    G.clear()
    H.clear()

    # Adding nodes and edges to directed graphs
    G.add_nodes_from(range(0, 10))
    G.add_edges_from([(3, 0), (1, 3), (4, 1), (2, 4), (5, 2), (3, 4), (4, 5), 
                      (3, 7), (7, 6), (4, 8), (5, 9),(1, 0),(2,1),(8, 7), (7,4), (8, 5), (9,8)])

    H.add_nodes_from(range(0, 4))
    H.add_edges_from([(0, 1), (1, 2), (2, 0), (1, 3)])
    #H.add_edges_from([(3, 1), (1, 2), (2, 3), (1, 0)])

    node_label = 'NodeLabel'
    edge_label = 'EdgeLabel'
    nx.set_node_attributes(G, node_label, 'label1')
    nx.set_edge_attributes(G, edge_label, 'Y1')

    nx.set_node_attributes(H, node_label, 'label1')
    nx.set_edge_attributes(H, edge_label, 'Y1')
    

    
    # Extracting src and dst arrays from G
    edgesG = G.edges()
    srcG = [edge[0] for edge in edgesG]
    dstG = [edge[1] for edge in edgesG]


    
    # Extracting all_nodes array
    vertex_idsG = list(G.nodes())
    vertex_labelsG = ['label1'] * len(vertex_idsG)
    edge_relationshipsG = ['Y1'] * len(srcG)
    

    prop_graph = ar.PropGraph()
    
    prop_graph.add_edges_from(ak.array(srcG),ak.array(dstG))
    
    node_labelsG = ak.DataFrame({"vertex_ids" : ak.array(vertex_idsG), 
                                "vertex_labels" : ak.array(vertex_labelsG)})
    edge_relationshipsG = ak.DataFrame({"src" : ak.array(srcG), 
                                       "dst" : ak.array(dstG), 
                    "edge_relationships" : ak.array(edge_relationshipsG)})
    prop_graph.add_node_labels(node_labelsG)
    prop_graph.add_edge_relationships(edge_relationshipsG)

    
     # Extracting src and dst arrays from H
    edgesH = H.edges()
    srcH = [edge[0] for edge in edgesH]
    dstH = [edge[1] for edge in edgesH]


    
    # Extracting all_nodes array H
    vertex_idsH = list(H.nodes())
    vertex_labelsH = ['label1'] * len(vertex_idsH)
    edge_relationshipsH = ['Y1'] * len(srcH)
    
 

    subgraph = ar.PropGraph()
    
    subgraph.add_edges_from(ak.array(srcH),ak.array(dstH))
    
    node_labelsH = ak.DataFrame({"vertex_ids" : ak.array(vertex_idsH), 
                                "vertex_labels" : ak.array(vertex_labelsH)})
    edge_relationshipsH = ak.DataFrame({"src" : ak.array(srcH), 
                                       "dst" : ak.array(dstH), 
                    "edge_relationships" : ak.array(edge_relationshipsH)})
    subgraph.add_node_labels(node_labelsH)
    subgraph.add_edge_relationships(edge_relationshipsH)
    
    start_time1 = time.time()
 
    mappings_df = ar.subgraph_isomorphism_VF2(prop_graph, subgraph, "VF2")
    # Access the DataFrame data
    print("VF2 subgraph_isomorphism run and this is the found ISOs:")
    #print(mappings_df)
    print(len(mappings_df)/4)
    for i in range(0, len(mappings_df), 4):
        print(mappings_df[i:i+4])
    elapsed_time1 = time.time() - start_time1
    print(f"Execution time: {elapsed_time1} seconds")
    
    print("srcG = ",srcG)
    print("dstG = ",dstG)
    print("number of edges: ", len(edgesG))
    print("number of nodes: ", len(vertex_idsG))
    print("subgraph #edges: ", len(edgesH))
    print("subgraph #nodes: ", len(vertex_idsH))
    

    ak.shutdown()