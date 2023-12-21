"""Contains the graph class defintion for `PropGraph`."""

from __future__ import annotations
from typing import List, Dict
from sys import exit

import arachne as ar
import arkouda as ak

__all__ = ["PropGraph"]

class PropGraph(ar.DiGraph):
    """`PropGraph` is the base class to represent a property graph. It inherits from `DiGraph` since
    all property graphs are composed of directed edges. Property graphs contain vertices (nodes) and
    edges as a graph typically does, however, their nodes and edges may contain extra information 
    referred to as attributes. Now, we will discuss each possible type of attribute in more detail.

    Nodes of a property graph contain an attribute called a `label` that may contain any number of
    extra identifiers for that node, including none. Some examples could be identifying a vertex in
    a transaction network as a `Person`, `Buyer`, and `Loyalty Member`. 

    Edges of a property graph each must contain one attribute called a `relationship`. If there are
    two instances of an edge, as in a multigraph, each edge must be uniquely identified by its
    relationship. An edge without a uniquely identifiable relationship is removed from the 
    `PropGraph` during construction. The user can specify the relationship for each edge typically
    as a column composed of a `pdarray` of strings. If the user does not specify the relationship
    while using any of the methods that loads attributes, such as `PropGraph.load_edge_attributes`
    then we remove all duplicate edges and assign every edge the same unique identifier. Continuing
    the example of the transaction network above, say we have two edges from the same buyer to an
    item. One of these edges may be identifiable as a purchase with the relationship `Buys` or as
    a return with the relationship `Returns`. This allows for multiple different interactions to be
    logged between the same two pairs of nodes. **Currently, multiple edges are not allowed but it
    is planned for a future release of Arachne.**

    Both nodes and edges can contain more properties to hold extra data for each node or edge. For
    example, a `Person` node can contain properties such as `Address`, `Phone Number`, and `Email`.
    Edges with relationship `Buys` could have a property identifying the `Shipping Address` whereas
    an edge with relationship `Returns` could have a property identifying `Return Date`.

    To query a `PropGraph` the user can extract a `pdarray` for each attribute by accessing either
    the `edge_attributes` or `node_attributes` from the attributes list of `PropGraph`. Then, the
    user can use all class methods for `ak.DataFrame`s and `pdarrays` to perform searches within
    the `PropGraph` object. 

    >>> import arachne as ar
    >>> G = ar.PropGraph()
    >>> G.load_edge_attributes(some_dataframe, src = "source", dst = "destination")
    >>> edges_of_G = G.edges()
    >>> bool_edges = G.edge_attributes["some_column"] == 1
    >>> edges_where_query_matches = edges_of_G[bool_edges]

    The above example can also be applied to node attributes. 

    Attributes
    ----------
    multied : int
        The graph is a multi graph (True) or not a multi graph (False).
    edge_attributes : ak.DataFrame
        Dataframe containing the edges of the graph and their attributes. 
    node_attributes : ak.DataFrame
        Dataframe containing the nodes of the graph and their attributes.
    relationship_mapper : Dict
        List of the attribute (column) names that correspond to relationships.
    label_mapper : Dict
        List of the attribute (column) names that correspond to labels.

    See Also
    --------
    Graph, DiGraph
        
    Notes
    -----
    """

    def __init__(self) -> None:
        """Initializes an empty graph instance."""
        super().__init__()
        self.multied = 0
        self.edge_attributes = ak.DataFrame()
        self.relationship_mapper = Dict()
        self.node_attributes = ak.DataFrame()
        self.label_mapper = Dict()

    def add_node_labels(self, labels:ak.DataFrame) -> None:
        """Populates the graph object with labels from a dataframe. Passed dataframe should follow
        the same format specified in the Parameters section below. The column containing the nodes
        should be called `nodes`. Every column that is not the `nodes` column is inferred to be a
        column containing labels. Duplicate nodes are removed.
        
        Parameters
        ----------
        labels : ak.DataFrame
            `ak.DataFrame({"nodes" : nodes, "labels1" : labels1, ..., "labelsN" : labelsN})`

        Returns
        -------
        None
        """
        cmd = "addNodeLabels"
        # 0. Do preliminary check to make sure any attribute (column) names do not already exist.
        try:
            [self.node_attributes[col] for col in labels.columns]
        except KeyError:
            raise KeyError("duplicated attribute (column) name in labels")
            
        set(self.node_attributes.columns).intersection(labels.columns)

        # 1. Extract the nodes and labels from the dataframe.
        vertex_ids = None
        try:
            vertex_ids = labels["nodes"]
        except KeyError:
            raise KeyError("attributed (column) nodes does not exist in labels")
        
        labels = labels.drop("nodes", axis=1)

        # 2. Convert labels to integers and store the index to label mapping in the label_mapper.
        for col in labels.columns:
            if labels[col] is ak.Strings:
                gb_labels = ak.GroupBy(labels)
                new_label_ids = ak.arange(gb_labels.unique_keys.size)
                new_vertex_labels = gb_labels.broadcast(new_label_ids)
                self.label_mapper[col] = gb_labels.unique_keys
                labels[col] = new_vertex_labels
            else:
                labels[col] = None

        # 3. Convert the vertex ids to internal vertex ids.
        vertex_map = self.nodes()
        inds = ak.in1d(vertex_ids, vertex_map) # Gets rid of vertex_ids that do not exist.
        vertex_ids = vertex_ids[inds]
        labels = labels[inds]
        vertex_ids = ak.find(vertex_ids, vertex_map) # Generated internal vertex representations.

        # 4. GroupBy to sort the vertex ids and labels together and remove duplicates.
        gb_vertex_ids = ak.GroupBy(vertex_ids)
        vertex_ids = gb_vertex_ids.unique_keys[0]
        inds = gb_vertex_ids.permutation[gb_vertex_ids.segments]
        labels = labels[inds]

        args = { "GraphName" : self.name,
                 "VertexIdsName" : vertex_ids.name,
                 "VertexLabelsName" : vertex_labels.name,
                 "LabelMapperName" : label_mapper.name
        }

        ak.generic_msg(cmd=cmd, args=args)

    def add_edge_relationships(self, relationships:ak.DataFrame) -> None:
        """Populates the graph object with edge relationships from a dataframe. Passed dataframe 
        should follow the same format specified in the Parameters section below. The columns
        containing the edges should be called `source` for the source vertex of an edge and 
        `destination` for the destination vertex of the edge. The column with the relationships
        should be called `relationships`. 
        
        Parameters
        ----------
        relationships : ak.DataFrame
            `ak.DataFrame({"source" : source, "destination" : destination,
                           "relationships" : relationships})`

        Returns
        -------
        None
        """
        cmd = "addEdgeRelationships"

        ### Preprocessing steps for faster back-end array population.
        # 0. Extract the source and destination vertices and the relationships from the dataframe.
        src_vertex_ids = relationships["source"]
        dst_vertex_ids = relationships["destination"]
        edge_relationships = relationships["relationships"]

        # 1. Convert the relationships to integers and store the index to label mapping in an array.
        gb_relationships = ak.GroupBy(edge_relationships)
        new_relationship_ids = ak.arange(gb_relationships.unique_keys.size)
        edge_relationships = gb_relationships.broadcast(new_relationship_ids)
        relationship_mapper = gb_relationships.unique_keys

        # 2. Convert the source and destination vertex ids to the internal vertex_ids.
        vertex_map = self.nodes()
        src_vertex_ids = ak.find(src_vertex_ids, vertex_map)
        dst_vertex_ids = ak.find(dst_vertex_ids, vertex_map)

        # 3. Ensure all edges are actually present in the underlying graph data structure.
        edges = self.edges()
        edge_inds = ak.in1d([src_vertex_ids,dst_vertex_ids],[edges[0],edges[1]])
        src_vertex_ids = src_vertex_ids[edge_inds]
        dst_vertex_ids = dst_vertex_ids[edge_inds]
        edge_relationships = edge_relationships[edge_inds]

        # 4. GroupBy of the src and dst vertex ids and relationships to remove any duplicates.
        gb_edges_and_relationships = ak.GroupBy([src_vertex_ids,dst_vertex_ids,edge_relationships])
        src_vertex_ids = gb_edges_and_relationships.unique_keys[0]
        dst_vertex_ids = gb_edges_and_relationships.unique_keys[1]
        edge_relationships = gb_edges_and_relationships.unique_keys[2]

        # 5. Generate internal edge indices.
        internal_edge_indices = ak.find([src_vertex_ids,dst_vertex_ids],[edges[0],edges[1]])

        args = {  "GraphName" : self.name,
                  "InternalEdgeIndicesName" : internal_edge_indices.name, 
                  "EdgeRelationshipsName" : edge_relationships.name,
                  "RelationshipMapperName" : relationship_mapper.name
        }

        ak.generic_msg(cmd=cmd, args=args)

    def load_node_attributes(self,
                             node_attributes:ak.DataFrame,
                             node_column:str,
                             label_column:List(str)|str|None = None) -> None:
        """Populates the graph object with attributes derived from the columns of a dataframe. Node
        properties are different from node labels where labels just extra identifiers for nodes.
        On the other hand, properties are key-value pairs more akin to storing the columns of a 
        dataframe. The column to be used as the node labels can be denoted by setting the 
        `label_column` parameter. A node can have multiple labels so `label_column` can be a list
        of column names.
        
        Parameters
        ----------
        node_attributes : ak.DataFrame
            `ak.DataFrame({"nodes" : nodes, "attribute1" : attribute1, ..., 
                           "attributeN" : attributeN})`
        node_column : str
            The column denoting the values to be treated as the nodes of the graph.
        label_column : List(str) | str | None
            Name of the column(s) to be used to denote the labels of the nodes. 

        See Also
        --------
        add_node_labels, add_edge_relationships, add_edge_attributes
        """
        cmd = "loadNodeAttributes"
        columns = node_attributes.columns

        ### Modify the inputted dataframe by sorting it.
        # 1. Sort the data and remove duplicates.
        node_attributes_sorted_idx = node_attributes.argsort( [ node_column ] )
        node_attributes = node_attributes[node_attributes_sorted_idx]

        # 2. Store the modified edge attributes into the class variable.
        self.node_attributes = node_attributes

        # 3. Extract the nodes column as a pdarray.
        nodes = self.node_attributes[node_column]

        # 2. Populate the graph object with labels if specified.
        if label_column is not None and label_column is str:
            self.add_node_labels(ak.DataFrame(
                {"nodes":nodes,
                 "labels":self.node_attributes[label_column]}))
            self.edge_attributes.rename(column={label_column:"labels"}, inplace=True)
            columns.remove(label_column)
        elif label_column is List(str):
            for col in label_column:


        ### Prepare the columns that are to be sent to the back-end to be stored per-edge.
        # 1. Remove the first two column names, edge ids, since those are sent separately.
        columns.remove(source_column)
        columns.remove(destination_column)
        column_names = ak.array(columns)

        # 2. Extract symbol table names of arrays to use in the back-end.
        column_ids = []
        for column in columns:
            column_ids.append(edge_attributes[column].name)
        column_ids = ak.array(column_ids)

        # 3. Sort the strings in size and lexical order.
        perm = ak.GroupBy(column_names).permutation
        column_names = column_names[perm]
        column_ids = column_ids[perm]

        # 4. Generate internal indices for the edges.
        edges = self.edges()
        nodes = self.nodes()
        src = ak.find([src], [nodes])
        dst = ak.find([dst], [nodes])
        internal_indices = ak.find([src,dst], [edges[0],edges[1]])

        args = { "GraphName" : self.name,
                 "ColumnNames" : column_names.name,
                 "ColumnIdsName" : column_ids.name,
                 "InternalIndicesName" : internal_indices.name
               }

        ak.generic_msg(cmd=cmd, args=args)

    def load_edge_attributes(self,
                             edge_attributes:ak.DataFrame,
                             source_column:str,
                             destination_column:str,
                             relationship_column:str|None = None) -> None:
        """Populates the graph object with attributes derived from the columns of a dataframe. Edge
        properties are different from edge relationships where relationships are used to tell apart
        multiple edges. On the other hand, properties are key-value pairs more akin to storing the 
        columns of a dataframe. The column to be used as the edge relationship can be denoted by 
        setting the `relationship_column` parameter.
        
        Parameters
        ----------
        edge_attributes : ak.DataFrame
            `ak.DataFrame({"src_vertex_ids" : src_vertex_ids, "dst_vertex_ids" : dst_vertex_ids,
                           "attribute1" : attribute1, ..., "attributeN" : attributeN})`
        source_column : str
            The column denoting the values to be treated as the source vertices of an edge in 
            a graph.
        destination_column : str
            The column denoting the values to be treated as the destination vertices of an edge in
            a graph.
        relationship_column : str | None
            Name of the column to be used to denote the relationships of each edge. If unset, no
            column is used as relationships and multiple edges will be deleted.

        See Also
        --------
        add_node_labels, add_edge_relationships, add_node_attributes
        """
        cmd = "loadEdgeAttributes"
        columns = edge_attributes.columns

        ### Modify the inputted dataframe by sorting it and removing duplicates.
        # 1. Sort the data and remove duplicates.
        edge_attributes_gb = edge_attributes.groupby( [ source_column, destination_column ] )
        new_rows = edge_attributes_gb.permutation[edge_attributes_gb.segments]
        edge_attributes = edge_attributes[new_rows]
        self.multied = 0 # TODO: Allow for multigraphs in Arachne.

        # 2. Store the modified edge attributes into the class variable.
        self.edge_attributes = edge_attributes

        # 3. Initialize our src and destination arrays.
        src = edge_attributes[source_column]
        dst = edge_attributes[destination_column]

        ### Build the graph and load in relationships.
        # 1. Populate the graph object with edges.
        super().add_edges_from(src, dst)

        # 2. Populate the graph object with relationships.
        if relationship_column is None:
            relationships = ak.full(len(src), "relationship", str)
            self.add_edge_relationships(ak.DataFrame({"source":src, "destination":dst,
                                                      "relationships":relationships}))
            self.edge_attributes["relationships"] = relationships
        else:
            self.add_edge_relationships(ak.DataFrame(
                {"source":src,
                 "destination":dst,
                 "relationships":edge_attributes[relationship_column]}))
            self.edge_attributes.rename(column={relationship_column:"relationships"}, inplace=True)
            columns.remove(relationship_column)

        ### Prepare the columns that are to be sent to the back-end to be stored per-edge.
        # 1. Remove the first two column names, edge ids, since those are sent separately.
        columns.remove(source_column)
        columns.remove(destination_column)
        column_names = ak.array(columns)

        # 2. Extract symbol table names of arrays to use in the back-end.
        column_ids = []
        for column in columns:
            column_ids.append(edge_attributes[column].name)
        column_ids = ak.array(column_ids)

        # 3. Sort the strings in size and lexical order.
        perm = ak.GroupBy(column_names).permutation
        column_names = column_names[perm]
        column_ids = column_ids[perm]

        # 4. Generate internal indices for the edges.
        edges = self.edges()
        nodes = self.nodes()
        src = ak.find([src], [nodes])
        dst = ak.find([dst], [nodes])
        internal_indices = ak.find([src,dst], [edges[0],edges[1]])

        args = { "GraphName" : self.name,
                 "ColumnNames" : column_names.name,
                 "ColumnIdsName" : column_ids.name,
                 "InternalIndicesName" : internal_indices.name
               }

        ak.generic_msg(cmd=cmd, args=args)

    def get_node_labels(self) -> ak.Strings | ak.pdarray | -1:
        """Returns the `pdarray` or `Strings` object holding the nodel labels of the `PropGraph`
        object. If return is -1 then no node labels found.

        Returns
        -------
        `ak.Strings` | `ak.pdarray` | `int`
            The node labels of the property graph. If return is -1 then no node labels found.
        """
        labels = None
        try:
            labels = self.node_attributes["labels"]
        except KeyError:
            raise KeyError("no labels property found.")
        return labels

    def get_node_attributes(self) -> ak.DataFrame:
        """Returns the `ak.DataFrame` object holding all the node attributes of the `PropGraph`
        object.

        Returns
        -------
        `ak.DataFrame`
            The node attributes of the graph.
        """
        return self.node_attributes

    def get_edge_relationships(self) -> ak.Strings | ak.pdarray:
        """Returns the `pdarray` or `Strings` object holding the edge relationships of the 
        `PropGraph` object. If return is -1 then no edge relationships found.

        Returns
        -------
        `ak.Strings` | `ak.pdarray` | `int`
            The edge relationships of the property graph. If return is -1 then no edge relationships 
            found.
        """
        labels = None
        try:
            labels = self.node_attributes["labels"]
        except KeyError:
            raise KeyError("no relationships property found.")
        return labels

    def get_edge_attributes(self) -> ak.DataFrame:
        """Returns the `ak.DataFrame` object holding all the edge attributes of the `PropGraph`
        object.

        Returns
        -------
        `ak.DataFrame`
            The edge attributes of the graph.
        """
        return self.edge_attributes

    def find_paths_of_length_one( self,
                                  node_column_names: List(str),
                                  node_column_values: List,
                                  edge_column_names: List(str),
                                  edge_column_values: List) -> (ak.pdarray, ak.pdarray):
        """Given a list of node and edge attribute column names, and desired values, find the paths
        of length one that satisfy the query.

        Parameters
        ----------
        node_column_names : List(str)
            Names of the node attribute to search for.
        node_column_values : List
            Values of the node attributes to search for.
        edge_column_namse : List(str)
            Names of the edge attribute to search for.
        edge_column_values : List
            Values of the edge attributes to search for.

        Returns
        -------
        (pdarray,pdarray)
            Source and destination vertex pairs that contain the length one paths.
        """
        # 1. Get the nodes and edges that contain the specified labels and relationships.
        nodes = ak.intx(ak.DataFrame(dict(zip(node_column_names, node_column_values))),
                        self.node_attributes)
        edges = ak.intx(ak.DataFrame(dict(zip(edge_column_names, edge_column_values))),
                        self.edge_attributes)

        # 2. Find the overlap of returned edges and returned nodes.
        src = ak.in1d(edges[0], nodes)
        dst = ak.in1d(edges[1], nodes)

        # 3. Perform a Boolean and operation to keep only the edges where nodes were also returned
        #    in a query.
        kept_edges = src & dst

        # 4. Extract the actual edges with original node names.
        src = edges[0][kept_edges]
        dst = edges[1][kept_edges]

        return (src, dst)
    