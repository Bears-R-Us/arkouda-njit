from base_test import ArkoudaTest
import networkx as nx
import arachne as ar
import arkouda as ak

class AlgorithmTest(ArkoudaTest):
    """Test graph algorithm methods."""
    def build_undirected_graph(self):
        """Builds undirected and weighted graphs in both Arachne and NetworkX for tests."""
        src_list = [2,5,2,3,3,3,3,2,3,4,5,5,5,5,5,5,7,8,9,9,8,9 ,10,10,10,24,25,25]
        dst_list = [1,0,0,0,3,3,3,3,4,3,5,2,2,2,2,7,8,9,8,8,5,10,7 ,7 ,7 ,24,26,27]
        wgt_list = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1 ,1 ,1 ,1 ,1 ,10,20]
        src = ak.array(src_list)
        dst = ak.array(dst_list)
        wgt = ak.array(wgt_list)

        ar_graph = ar.Graph()
        ar_graph.add_edges_from(src,dst)
        ar_graph_weighted = ar.Graph()
        ar_graph_weighted.add_edges_from(src,dst,wgt)

        ebunch = list(zip(src_list,dst_list))
        nx_graph = nx.Graph()
        nx_graph.add_edges_from(ebunch)
        ebunchw = list(zip(src_list,dst_list,wgt_list))
        nx_graph_weighted = nx.Graph()
        nx_graph_weighted.add_weighted_edges_from(ebunchw)

        return ar_graph, nx_graph, ar_graph_weighted, nx_graph_weighted

    def build_directed_graph(self):
        """Builds directed and weighted graphs in both Arachne and NetworkX for tests."""
        src_list = [2,5,2,3,3,3,3,2,3,4,5,5,5,5,5,5,7,8,9,9,8,9 ,10,10,10,24,25,25]
        dst_list = [1,0,0,0,3,3,3,3,4,3,5,2,2,2,2,7,8,9,8,8,5,10,7 ,7 ,7 ,24,26,27]
        wgt_list = [1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1 ,1 ,1 ,1 ,1 ,10,20]
        src = ak.array(src_list)
        dst = ak.array(dst_list)
        wgt = ak.array(wgt_list)

        ar_di_graph = ar.DiGraph()
        ar_di_graph.add_edges_from(src,dst)
        ar_di_graph_weighted = ar.DiGraph()
        ar_di_graph_weighted.add_edges_from(src,dst,wgt)

        ebunch = list(zip(src_list,dst_list))
        nx_di_graph = nx.DiGraph()
        nx_di_graph.add_edges_from(ebunch)
        ebunchw = list(zip(src_list,dst_list,wgt_list))
        nx_di_graph_weighted = nx.DiGraph()
        nx_di_graph_weighted.add_weighted_edges_from(ebunchw)

        return ar_di_graph, nx_di_graph, ar_di_graph_weighted, nx_di_graph_weighted

    def test_undirected_bfs_layers(self):
        """Tests Arachne bfs_layers() and compares against NetworkX."""
        # Read in graphs with Arachne and NetworkX.
        ar_graph, nx_graph,_,_ = self.build_undirected_graph()

        # Extract vertices to launch breadth-first search from each.
        vertices = ar_graph.nodes().to_list()

        ar_all_layers = []
        nx_all_layers = []
        for root in vertices:
            # Compute breadth-first search with Arachne.
            ar_layers = ar.bfs_layers(ar_graph, root).to_list()

            # Compute breadth-first search with NetworkX.
            nx_layer_dict = dict(enumerate(nx.bfs_layers(nx_graph, root)))
            nx_layers = [-1] * len(ar_layers)
            for layer,vertices_at_layer in nx_layer_dict.items():
                for vertex in vertices_at_layer:
                    nx_layers[vertices.index(vertex)] = layer

            # Add both to corresponding layers tracker.
            ar_all_layers.append(ar_layers)
            nx_all_layers.append(nx_layers)

        self.assertEqual(ar_all_layers, nx_all_layers)

    def test_directed_bfs_layers(self):
        """Tests Arachne bfs_layers() and compares against NetworkX."""
        # Read in graphs with Arachne and NetworkX.
        ar_graph, nx_graph,_,_ = self.build_directed_graph()

        # Extract vertices to launch breadth-first search from each.
        vertices = ar_graph.nodes().to_list()

        ar_all_layers = []
        nx_all_layers = []
        for root in vertices:
            # Compute breadth-first search with Arachne.
            ar_layers = ar.bfs_layers(ar_graph, root).to_list()

            # Compute breadth-first search with NetworkX.
            nx_layer_dict = dict(enumerate(nx.bfs_layers(nx_graph, root)))
            nx_layers = [-1] * len(ar_layers)
            for layer,vertices_at_layer in nx_layer_dict.items():
                for vertex in vertices_at_layer:
                    nx_layers[vertices.index(vertex)] = layer

            # Add both to corresponding layers tracker.
            ar_all_layers.append(ar_layers)
            nx_all_layers.append(nx_layers)

        self.assertEqual(ar_all_layers, nx_all_layers)

    def test_square_count(self):
        """Tests Arachne squares() and compares it against base case."""
        # Read in graph with Arachne.
        ar_graph,_,_,_ = self.build_undirected_graph()

        # Get the square count.
        sc = ar.squares(ar_graph)

        self.assertEqual(2, sc)

    def test_triangles(self):
        """Tests Arachne triangles() and compares it against NetworkX."""
        # Read in the graph with Arachne and NetworkX.
        ar_graph, nx_graph,_,_ = self.build_undirected_graph()
        nodes = [0,2,3,4]

        # Get triangle counts with Arachne.
        ar_tri_full = ar.triangles(ar_graph)
        ar_tri_partial = ar.triangles(ar_graph, ak.array(nodes))

        # Get triangle counts with NetworkX.
        nx_tri_full = nx.triangles(nx_graph)
        nx_tri_partial = nx.triangles(nx_graph, nodes)

        ret = [nx_tri_partial[v] for v in nodes]
        self.assertEqual(ret, ar_tri_partial.to_list())
        self.assertEqual(sum(nx_tri_full.values())/3, ar_tri_full/3)

    def test_triangle_centrality(self):
        """Tests Arachne triangles() and compares it against NetworkX."""
        # Read in the graph with Arachne.
        src = [0, 1, 2, 3, 4, 4, 5, 6, 7, 8, 0]
        dst = [1, 2, 0, 0, 3, 0, 6, 7, 5, 9, 0]
        graph = ar.Graph()
        graph.add_edges_from(ak.array(src), ak.array(dst))

        # Get triangle centralities with Arachne.
        triangle_centralities = ar.triangle_centrality(graph)
        triangle_centralities = triangle_centralities * 10
        triangle_centralities = ak.cast(triangle_centralities, ak.int64)

        # Actual results.
        results = [6, 4, 4, 4, 4, 3, 3, 3, 0, 0]

        self.assertListEqual(results, triangle_centralities.to_list())

    def test_subgraph_isomorphism(self):
        #### Run Arachne subgraph isomorphism.
        # 1. Create vertices, edges, and attributes for main property graph.
        src_prop_graph = ak.array([1, 1, 2, 2, 3, 0, 3, 3, 4, 4, 4, 5, 5, 7, 7, 8, 8, 9])
        dst_prop_graph = ak.array([3, 0, 1, 4, 0, 3, 4, 7, 1, 5, 8, 2, 9, 4, 6, 5, 7, 8])
        labels1_prop_graph = ak.array(["lbl1"] * 10)
        labels2_prop_graph = ak.array(["lbl2"] * 10)
        rels1_prop_graph = ak.array(["rel1"] * 18)
        rels2_prop_graph =  ak.array(["rel2"] * 18)

        # 2. Transer data above into main property graph.
        prop_graph = ar.PropGraph()
        edge_df_h = ak.DataFrame({"src":src_prop_graph, "dst":dst_prop_graph,
                                "rels1":rels1_prop_graph, "rels2":rels2_prop_graph})
        node_df_h = ak.DataFrame({"nodes": ak.arange(0,10), "lbls1":labels1_prop_graph,
                                "lbls2":labels2_prop_graph})
        prop_graph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                        relationship_columns=["rels1","rels2"])
        prop_graph.load_node_attributes(node_df_h, node_column="nodes", label_columns=["lbls1","lbls2"])

        # 3. Create vertices, edges, and attributes for subgraph.
        src_subgraph = ak.array([0, 1, 2, 1])
        dst_subgraph = ak.array([1, 2, 0, 3])
        labels1_subgraph = ak.array(["lbl1", "lbl1", "lbl1", "lbl1"])
        labels2_subgraph = ak.array(["lbl2", "lbl2", "lbl2", "lbl2"])
        rels1_subgraph = ak.array(["rel1", "rel1", "rel1", "rel1"])
        rels2_subgraph = ak.array(["rel2", "rel2", "rel2", "rel2"])

        # 4. Transer data above into subgraph.
        subgraph = ar.PropGraph()
        edge_df_h = ak.DataFrame({"src":src_subgraph, "dst":dst_subgraph,
                                "rels1":rels1_subgraph, "rels2":rels2_subgraph})
        node_df_h = ak.DataFrame({"nodes": ak.arange(0,4), "lbls1":labels1_subgraph,
                                "lbls2":labels2_subgraph})
        subgraph.load_edge_attributes(edge_df_h, source_column="src", destination_column="dst",
                                        relationship_columns=["rels1","rels2"])
        subgraph.load_node_attributes(node_df_h,
                                      node_column="nodes",
                                      label_columns=["lbls1","lbls2"])

        # 5. Run the subgraph isomorphism.
        isos = ar.subgraph_isomorphism(prop_graph, subgraph)

        #### Run NetworkX subgraph isomorphism.
        # Grab vertex and edge data from the Arachne dataframes.
        graph_node_information = prop_graph.get_node_attributes()
        graph_edge_information = prop_graph.get_edge_attributes()
        subgraph_node_information = subgraph.get_node_attributes()
        subgraph_edge_information = subgraph.get_edge_attributes()

        # The 4 for loops below convert internal integer labels to original strings.
        for (column,_) in graph_node_information.items():
            if column != "nodes":
                cat = graph_node_information[column]
                graph_node_information[column] = cat.categories[cat.codes]

        for (column,_) in graph_edge_information.items():
            if column not in ("src", "dst"):
                cat = graph_edge_information[column]
                graph_edge_information[column] = cat.categories[cat.codes]

        for (column,_) in subgraph_node_information.items():
            if column != "nodes":
                cat = subgraph_node_information[column]
                subgraph_node_information[column] = cat.categories[cat.codes]

        for (column,_) in subgraph_edge_information.items():
            if column not in ("src", "dst"):
                cat = subgraph_edge_information[column]
                subgraph_edge_information[column] = cat.categories[cat.codes]

        # Convert Arkouda dataframes to Pandas dataframes to NetworkX graph attributes.
        G = nx.from_pandas_edgelist(graph_edge_information.to_pandas(), source='src',
                                    target='dst', edge_attr=True, create_using=nx.DiGraph)
        H = nx.from_pandas_edgelist(subgraph_edge_information.to_pandas(), source='src',
                                    target='dst', edge_attr=True, create_using=nx.DiGraph)

        # Convert graph node attributes to Pandas dfs, remove nodes, and convert rows to dicts.
        graph_node_attributes = graph_node_information.to_pandas()
        graph_nodes_from_df = list(graph_node_attributes.pop("nodes"))
        graph_node_attributes = graph_node_attributes.to_dict('index')
        graph_node_attributes_final = {}

        # Convert subgraph node attributes to Pandas dfs remove nodes, and convert rows to dicts.
        subgraph_node_attributes = subgraph_node_information.to_pandas()
        subgraph_nodes_from_df = list(subgraph_node_attributes.pop("nodes"))
        subgraph_node_attributes = subgraph_node_attributes.to_dict('index')
        subgraph_node_attributes_final = {}

        # Convert Pandas index to original node index.
        for key in graph_node_attributes:
            graph_node_attributes_final[graph_nodes_from_df[key]] = graph_node_attributes[key]

        for key in subgraph_node_attributes:
            subgraph_node_attributes_final[subgraph_nodes_from_df[key]] = \
                                                                    subgraph_node_attributes[key]

        # Set the node attributes for G and H from dicts.
        nx.set_node_attributes(G, graph_node_attributes_final)
        nx.set_node_attributes(H, subgraph_node_attributes_final)

        # Find subgraph isomorphisms of H in G.
        GM = nx.algorithms.isomorphism.DiGraphMatcher(G, H)

        # List of dicts. For each dict, keys is original graph vertex, values are subgraph vertices.
        subgraph_isomorphisms = list(GM.subgraph_monomorphisms_iter())

        #### Compare Arachne subgraph isomorphism to NetworkX.
        isos_list = isos.to_list()
        isos_sublists = [isos_list[i:i+4] for i in range(0, len(isos_list), 4)]

        isos_as_dicts = []
        subgraph_vertices = [0, 1, 2, 3]
        for iso in isos_sublists:
            isos_as_dicts.append(dict(zip(iso, subgraph_vertices)))

        self.assertEqual(len(isos_as_dicts), len(subgraph_isomorphisms))
