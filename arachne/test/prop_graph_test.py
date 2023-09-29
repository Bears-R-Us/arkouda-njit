from base_test import ArkoudaTest
import arkouda as ak
import arachne as ar

class PropGraphTest(ArkoudaTest):
    def build_prop_graph(self):
        """Builds undirected and weighted graphs in both Arachne and NetworkX for tests."""
        src_list = [2,5,2,3,3,3,3,2,3,4,5,5,5,5,5,5,7,8,9,9,8,9 ,10,10,10,24,25,25]
        dst_list = [1,0,0,0,3,3,3,3,4,3,5,2,2,2,2,7,8,9,8,8,5,10,7 ,7 ,7 ,24,26,27]
        src = ak.array(src_list)
        dst = ak.array(dst_list)

        graph = ar.PropGraph()
        graph.add_edges_from(src,dst)

        nodes_with_labels = ak.array([  2,   2,   5,   8,   9,   3,   3,   9,  10])
        labels            = ak.array(["r", "b", "b", "g", "r", "r", "b", "b", "b"])

        src_with_relationships   = ak.array([  2,   2,   2,   2])
        dst_with_relationships   = ak.array([  1,   3,   1,   3])
        relationships            = ak.array(["w", "a", "a", "w"])

        labels_df = ak.DataFrame({"vertex_ids" : nodes_with_labels, "vertex_labels" : labels})
        relationships_df = ak.DataFrame({"src" : src_with_relationships, 
                                     "dst" : dst_with_relationships, 
                                     "edge_relationships" : relationships})

        graph.add_node_labels(labels_df)
        graph.add_edge_relationships(relationships_df)

        return graph

    def test_query_node_labels(self):
        """Tests querying node labels in a property graph."""
        graph = self.build_prop_graph()

        labels_to_find_or = ak.array(["r", "g"])
        labels_to_find_and = ak.array(["r", "b"])
        or_query = graph.query_labels(labels_to_find_or, "or")
        and_query = graph.query_labels(labels_to_find_and, "and")

        or_actual = [2, 8, 9, 3]
        and_actual = [2, 3, 9]
        or_actual.sort()
        and_actual.sort()

        # TODO: Inspect lists instead of strings. During the writing of this function there was a
        #       weird bug where or_query was being turned into an integer when calling to_list() on
        #       it.
        or_query = str(or_query)
        and_query = str(and_query)
        or_actual = str(or_actual).replace(",", "")
        and_actual = str(and_actual).replace(",", "")

        or_test = self.assertEqual(or_query, or_actual)
        and_test = self.assertEqual(and_query, and_actual)

        return self.assertEqual(or_test, and_test)

