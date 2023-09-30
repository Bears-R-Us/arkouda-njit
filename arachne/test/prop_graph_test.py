from base_test import ArkoudaTest
import arkouda as ak
import arachne as ar

class PropGraphTest(ArkoudaTest):
    """Test property graph functionality."""
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

        src_with_relationships   = ak.array([  2,   2,   2,   2,   8])
        dst_with_relationships   = ak.array([  1,   3,   1,   3,   5])
        relationships            = ak.array(["w", "a", "a", "w", "s"])

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

        # NOTE: Compares strings instead of lists. During the writing of this function there was a
        #       weird bug where or_query was being turned into an integer when calling to_list() on
        #       it, making all list functions such as sort uncallable. Converting them to strinks
        #       was the workaround.
        or_query = str(or_query)
        and_query = str(and_query)
        or_actual = str(or_actual).replace(",", "")
        and_actual = str(and_actual).replace(",", "")

        or_test = self.assertEqual(or_query, or_actual)
        and_test = self.assertEqual(and_query, and_actual)

        return self.assertEqual(or_test, and_test)

    def test_query_edge_relationships(self):
        """Tests querying edge relationships in a property graph."""
        graph = self.build_prop_graph()

        relationships_to_find_or = ak.array(["a", "w", "s"])
        relationships_to_find_and = ak.array(["a", "w"])
        or_query = graph.query_relationships(relationships_to_find_or, "or")
        and_query = graph.query_relationships(relationships_to_find_and, "and")

        or_actual_src = [2, 2, 8]
        or_actual_dst = [1, 3, 5]

        and_actual_src = [2, 2]
        and_actual_dst = [1, 3]

        # NOTE: Compares strings instead of lists. During the writing of this function there was a
        #       weird bug where or_query was being turned into an integer when calling to_list() on
        #       it, making all list functions such as sort uncallable. Converting them to strinks
        #       was the workaround.
        or_query_src = str(or_query[0])
        or_query_dst = str(or_query[1])
        and_query_src = str(and_query[0])
        and_query_dst = str(and_query[1])

        or_actual_src = str(or_actual_src).replace(",", "")
        or_actual_dst = str(or_actual_dst).replace(",", "")
        and_actual_src = str(and_actual_src).replace(",", "")
        and_actual_dst = str(and_actual_dst).replace(",", "")

        or_src_test = self.assertEqual(or_query_src, or_actual_src)
        or_dst_test = self.assertEqual(or_query_dst, or_actual_dst)
        and_src_test = self.assertEqual(and_query_src, and_actual_src)
        and_dst_test = self.assertEqual(and_query_dst, and_actual_dst)

        or_test = self.assertEqual(or_src_test, or_dst_test)
        and_test = self.assertEqual(and_src_test, and_dst_test)

        return self.assertEqual(or_test, and_test)

    def test_one_path(self):
        """Tests one path function for property graphs."""
        graph = self.build_prop_graph()

        r_to_find_or = ak.array(["a", "w", "s"])
        r_to_find_and = ak.array(["a", "w"])
        l_to_find_or = ak.array(["r", "g"])
        l_to_find_and = ak.array(["r", "b"])
        one_path_and_and = graph.one_path(l_to_find_and, r_to_find_and, "and", "and")
        one_path_and_or = graph.one_path(l_to_find_and, r_to_find_or, "and", "or")
        one_path_or_and = graph.one_path(l_to_find_or, r_to_find_and, "or", "and")
        one_path_or_or = graph.one_path(l_to_find_or, r_to_find_or, "or", "or")

        # NOTE: Compares strings instead of lists. During the writing of this function there was a
        #       weird bug where or_query was being turned into an integer when calling to_list() on
        #       it, making all list functions such as sort uncallable. Converting them to strinks
        #       was the workaround.
        all_actual = str([2]) + " " + str([3])
        one_path_and_and = str(one_path_and_and[0]) + " " + str(one_path_and_and[1])
        one_path_and_or = str(one_path_and_or[0]) + " " + str(one_path_and_or[1])
        one_path_or_and = str(one_path_or_and[0]) + " " + str(one_path_or_and[1])
        one_path_or_or = str(one_path_or_or[0]) + " " + str(one_path_or_or[1])

        test1 = self.assertEqual(one_path_and_and, all_actual)
        test2 = self.assertEqual(one_path_and_or, all_actual)
        test3 = self.assertEqual(one_path_or_and, all_actual)
        test4 = self.assertEqual(one_path_or_or, all_actual)
        test5 = self.assertEqual(test1, test2)
        test6 = self.assertEqual(test3, test4)

        return self.assertEqual(test5, test6)
