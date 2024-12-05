"""Contains the graph class defintion for `PropGraph`."""

from __future__ import annotations
from typing import List, Dict, Tuple, Union
import random
import string

import arachne as ar
import arkouda as ak

__all__ = ["PropGraph", "no_filter"]

def generate_string(n=5):
    """Generate random digit strings of the size of parameter `n`."""
    return ''.join(random.choices(string.digits, k=n))

def no_filter(attributes: ak.DataFrame):
    """Default filtering method for property subgraph view generation."""
    return ak.full(attributes.shape[0], True, ak.akbool)

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
    relationship. The user can specify the relationship for each edge typically as a column composed
    of a `pdarray` of strings. If the user does not specify the relationship while using any of the 
    methods that loads attributes, such as `PropGraph.load_edge_attributes` then we remove all 
    duplicate edges and assign every edge the same unique identifier. Continuing the example of the 
    transaction network above, say we have two edges from the same buyer to an item. One of these 
    edges may be identifiable as a purchase with the relationship `Buys` or as a return with the 
    relationship `Returns`. This allows for multiple different interactions to be logged between the
    same two pairs of nodes. **Currently, multiple edges are not allowed but it is planned for a 
    future release of Arachne.**

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
    edge_names : List(str)
        Names of the columns that signify the source and destination vertices of edges.
    edge_attributes : ak.DataFrame
        Dataframe containing the edges of the graph and their attributes.
    relationship_columns : List
        List of the attribute (column) names that correspond to relationships.
    node_name : str
        Name of column within node_attributes that signifies the nodes column.
    node_attributes : ak.DataFrame
        Dataframe containing the nodes of the graph and their attributes.
    label_columns : List
        List of the attribute (column) names that correspond to labels.

    See Also
    --------
    Graph, DiGraph
        
    Notes
    -----
    Capaiblity to store multiple edges is a work-in-progress.
    """

    def __init__(self) -> None:
        """Initializes an empty `PropGraph` instance."""
        super().__init__()
        self.multied = 0
        self.edge_names = ()
        self.edge_attributes = ak.DataFrame()
        self.relationship_columns = []
        self.node_name = ()
        self.node_attributes = ak.DataFrame()
        self.label_columns = []

    def add_node_labels(self,
                        labels:ak.DataFrame,
                        node_column:str,
                        assume_sorted:bool=False,
                        convert_strings_to_categoricals:bool=True) -> None:
        """Populates the graph object with labels from a dataframe. Passed dataframe should follow
        the same format specified in the Parameters section below. The column containing the nodes
        should be called `nodes`. Every column that is not the `nodes` column is inferred to be a
        column containing labels. Duplicate nodes are removed.
        
        Parameters
        ----------
        labels : ak.DataFrame
            `ak.DataFrame({"nodes" : nodes, "labels1" : labels1, ..., "labelsN" : labelsN})`
        node_column : str
            Name of column that represents the nodes.
        assume_sorted : bool
            If the edges are already sorted, skip a `ak.GroupBy`.
        convert_strings_to_categoricals : bool
            If True, all Strings are converted to Categorical.

        Returns
        -------
        None
        """
        cmd = "addNodeLabels"

        # 0. Do preliminary check to make sure any attribute (column) names do not already exist.
        try:
            [self.node_attributes[col] for col in labels.columns]
        except KeyError as exc:
            raise KeyError("duplicated attribute (column) name in labels") from exc

        # 1. Extract the nodes from the dataframe and drop them from the labels dataframe.
        vertex_ids = None
        try:
            vertex_ids = labels[node_column]
        except KeyError as exc:
            raise KeyError("column for nodes does not exist in labels") from exc
        labels.drop(node_column, axis=1, inplace=True)

        # 2. Convert labels to integers and store the index to label mapping in the label_mapper.
        vertex_labels_symbol_table_ids = []
        vertex_labels_object_types = []
        for col in labels.columns:
            if isinstance(labels[col], ak.Strings) and convert_strings_to_categoricals:
                self.node_attributes[col] = ak.Categorical(labels[col])
                self.node_attributes[col].register(generate_string())
                vertex_labels_symbol_table_ids.append(self.node_attributes[col].registered_name)
                vertex_labels_object_types.append("Categorical")
            elif isinstance(labels[col], ak.Strings) and not convert_strings_to_categoricals:
                self.node_attributes[col] = labels[col]
                vertex_labels_symbol_table_ids.append(self.node_attributes[col].name)
                vertex_labels_object_types.append("Strings")
            elif isinstance(labels[col], ak.Categorical):
                self.node_attributes[col] = labels[col]
                self.node_attributes[col].register(generate_string())
                vertex_labels_symbol_table_ids.append(self.node_attributes[col].name)
                vertex_labels_object_types.append("Categorical")
            elif isinstance(labels[col], ak.pdarray):
                self.node_attributes[col] = labels[col]
                vertex_labels_symbol_table_ids.append(self.node_attributes[col].name)
                vertex_labels_object_types.append("pdarray")
            else:
                raise NotImplementedError(f"{type(labels[col])} not supported by property graph")
            self.label_columns.append(col)

        # 3. Convert the vertex ids to internal vertex ids.
        vertex_map = self.nodes()
        inds = ak.in1d(vertex_ids, vertex_map) # Gets rid of vertex_ids that do not exist.
        vertex_ids = vertex_ids[inds]
        labels = labels[inds]
        vertex_ids = ak.find(vertex_ids, vertex_map) # Generated internal vertex representations.

        # 4. GroupBy to sort the vertex ids and remove duplicates. Perform only if the vertices have
        #    not been sorted previously.
        if not assume_sorted:
            gb_vertex_ids = ak.GroupBy(vertex_ids)
            inds = gb_vertex_ids.permutation[gb_vertex_ids.segments]
            vertex_ids = vertex_ids[inds]
            labels = labels[inds]

        # 5. Prepare arguments to transmit to the Chapel back-end server.
        args = { "GraphName" : self.name,
                 "InputIndicesName" : vertex_ids.name,
                 "LabelColumnNames" : "+".join(labels.columns),
                 "LabelArrayNames" : "+".join(vertex_labels_symbol_table_ids),
                 "LabelArrayTypes" : "+".join(vertex_labels_object_types)
        }
        ak.generic_msg(cmd=cmd, args=args)

    def load_node_attributes(self,
                             node_attributes:ak.DataFrame,
                             node_column:str,
                             label_columns:Union[List[str],None] = None,
                             convert_string_labels_to_categoricals:bool=True) -> None:
        """Populates the graph object with attributes derived from the columns of a dataframe. Node
        properties are different from node labels where labels just extra identifiers for nodes.
        On the other hand, properties are key-value pairs more akin to storing the columns of a 
        dataframe. The column to be used as the node labels can be denoted by setting the 
        `label_column` parameter. A node can have multiple labels so `label_column` can be a list
        of column names.

        **Graph must already be pupulated with edges prior to calling this method**.
        
        Parameters
        ----------
        node_attributes : ak.DataFrame
            `ak.DataFrame({"nodes" : nodes, "attribute1" : attribute1, ..., 
                           "attributeN" : attributeN})`
        node_column : str
            The column denoting the values to be treated as the nodes of the graph.
        label_columns : Union[List(str),None]
            Name of the column(s) to be used to denote the labels of the nodes.
        convert_string_labels_to_categoricals : bool
            If True, Strings are converted to categoricals when node labels are added, if any.

        See Also
        --------
        add_node_labels, add_edge_relationships, add_edge_attributes
        """
        cmd = "addNodeProperties" # TODO: This function should be command-less and just call a
                                  # `PropGraph` method called add_node_properties().
        columns = node_attributes.columns

        ### Modify the inputted dataframe by sorting it.
        # 1. Sort the data and remove duplicates since each node can only have one instance of a
        #    property.
        node_attributes_gb = node_attributes.groupby([ node_column ])
        node_attributes = node_attributes[
                            node_attributes_gb.permutation[node_attributes_gb.segments]
                        ]

        # 2. Store the modified edge attributes into the class variable.
        self.node_attributes = node_attributes
        self.node_attributes.reset_index(inplace=True)

        # 3. Extract the nodes column as a pdarray.
        nodes = self.node_attributes[node_column]

        # 4. Store the name of the nodes column.
        self.node_name = node_column

        # 5. Populate the graph object with labels if specified.
        if label_columns is not None and isinstance(label_columns, list):
            labels_to_add = {col: node_attributes[col] for col in label_columns}
            labels_to_add[node_column] = nodes
            self.add_node_labels(ak.DataFrame(labels_to_add), node_column, assume_sorted=True,
                                 convert_strings_to_categoricals=\
                                 convert_string_labels_to_categoricals)

        ### Prepare the columns that are to be sent to the back-end to be stored per node.
        # 1. From columns remove nodes and any other columns that were handled by adding node
        #    labels.
        columns = [col for col in columns if col not in label_columns]\
                  if label_columns is not None else list(columns)
        columns.remove(node_column)

        # 2. Extract symbol table names of arrays to use in the back-end and their types.
        column_ids = []
        vertex_property_object_types = []
        for col in columns:
            if isinstance(self.node_attributes[col], ak.Strings):
                vertex_property_object_types.append("Strings")
                column_ids.append(self.node_attributes[col].name)
            elif isinstance(self.node_attributes[col], ak.Categorical):
                vertex_property_object_types.append("Categorical")
                self.node_attributes[col].register(generate_string())
                column_ids.append(self.node_attributes[col].registered_name)
            elif isinstance(self.node_attributes[col], ak.pdarray):
                vertex_property_object_types.append("pdarray")
                column_ids.append(self.node_attributes[col].name)
            else:
                raise NotImplementedError(f"{type(self.node_attributes[col])} "
                                          f"not supported by property graph")

        # 3. Generate internal indices for the nodes.
        vertex_map = self.nodes()
        inds = ak.in1d(nodes, vertex_map) # Gets rid of vertex_ids that do not exist.
        vertex_ids = nodes[inds]
        node_attributes = node_attributes[inds]
        vertex_ids = ak.find(vertex_ids, vertex_map) # Generated internal vertex representations.

        args = { "GraphName" : self.name,
                 "InputIndicesName" : vertex_ids.name,
                 "ColumnNames" : "+".join(columns),
                 "PropertyArrayNames" : "+".join(column_ids),
                 "PropertyArrayTypes" : "+".join(vertex_property_object_types)
               }
        ak.generic_msg(cmd=cmd, args=args)

    def add_edge_relationships(self,
                               relationships:ak.DataFrame,
                               source_column:str,
                               desination_column:str,
                               assume_sorted:bool=False,
                               convert_strings_to_categoricals:bool=True) -> None:
        """Populates the graph object with edge relationships from a dataframe. Passed dataframe 
        should follow the same format specified in the Parameters section below. The columns
        containing the edges should be called `source` for the source vertex of an edge and 
        `destination` for the destination vertex of the edge. The column with the relationships
        should be called `relationships`. 
        
        Parameters
        ----------
        relationships : ak.DataFrame
            `ak.DataFrame({"src" : source, "dst" : destination, "relationship1" : relationship1,
                           ..., "relationshipN" : relationshipN})`
        source_column : str
            Column name that represents the source vertices of each edge. 
        destination_column : str
            Column name that represents the destination vertices of each edge. 
        assume_sorted : bool
            If the edges are already sorted, skip a `ak.GroupBy`.
        convert_strings_to_categoricals : bool
            If True, converts Strings to Categorical. 

        Returns
        -------
        None
        """
        cmd = "addEdgeRelationships"

        # 0. Do preliminary check to make sure any attribute (column) names do not already exist.
        try:
            [self.edge_attributes[col] for col in relationships.columns]
        except KeyError as exc:
            raise KeyError("duplicated attribute (column) name in relationships") from exc

        # 1. Extract the nodes from the dataframe and drop them from the labels dataframe.
        src, dst = (None, None)
        try:
            src, dst = (relationships[source_column], relationships[desination_column])
        except KeyError as exc:
            raise KeyError("source or destination columns do not exist in relationship") from exc
        relationships.drop([source_column, desination_column], axis=1, inplace=True)

        # 2. Convert relationships to integers and store the index to relationship mapping in
        #    the relationship_mapper.
        edge_relationships_symbol_table_ids = []
        edge_relationships_object_types = []
        for col in relationships.columns:
            if isinstance(relationships[col], ak.Strings) and convert_strings_to_categoricals:
                self.edge_attributes[col] = ak.Categorical(relationships[col])
                self.edge_attributes[col].register(generate_string())
                edge_relationships_symbol_table_ids.append(self.edge_attributes[col].registered_name)
                edge_relationships_object_types.append("Categorical")
            elif isinstance(relationships[col], ak.Strings) and not convert_strings_to_categoricals:
                self.edge_attributes[col] = relationships[col]
                edge_relationships_symbol_table_ids.append(self.edge_attributes[col].name)
                edge_relationships_object_types.append("Strings")
            elif isinstance(relationships[col], ak.Categorical):
                self.edge_attributes[col] = relationships[col]
                self.edge_attributes[col].register(generate_string())
                edge_relationships_symbol_table_ids.append(self.edge_attributes[col].name)
                edge_relationships_object_types.append("Categorical")
            elif isinstance(relationships[col], ak.pdarray):
                self.edge_attributes[col] = relationships[col]
                edge_relationships_symbol_table_ids.append(self.edge_attributes[col].name)
                edge_relationships_object_types.append("pdarray")
            else:
                raise NotImplementedError(f"{type(relationships[col])} not "
                                          f"supported by property graph")
            self.relationship_columns.append(col)

        # 3. GroupBy of the src and dst vertex ids and relationships to remove any duplicates.
        #    Perform only if the edges have not been sorted previously.
        if not assume_sorted:
            gb_edges = ak.GroupBy([src,dst])
            inds = gb_edges.permutation[gb_edges.segments]
            src = src[inds]
            dst = dst[inds]
            relationships = relationships[inds]

        # 4. Generate internal edge indices.
        edges = self.edges()
        internal_edge_indices = ak.find([src,dst],[edges[0],edges[1]])

        args = {  "GraphName" : self.name,
                  "InputIndicesName" : internal_edge_indices.name, 
                  "RelationshipColumnNames" : "+".join(relationships.columns),
                  "RelationshipArrayNames" : "+".join(edge_relationships_symbol_table_ids),
                  "RelationshipArrayTypes" : "+".join(edge_relationships_object_types)
        }
        ak.generic_msg(cmd=cmd, args=args)

    def load_edge_attributes(self,
                             edge_attributes:ak.DataFrame,
                             source_column:str,
                             destination_column:str,
                             relationship_columns:Union[List[str]|None] = None,
                             convert_string_relationships_to_categoricals:bool=True) -> None:
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
        relationship_columns : str | None
            Name of the column to be used to denote the relationships of each edge. If unset, no
            column is used as relationships and multiple edges will be deleted.
        convert_strings_to_categoricals : bool
            If True, converts Strings to Categorical in adding edge relationships, if any. 

        See Also
        --------
        add_node_labels, add_edge_relationships, add_node_attributes
        """
        cmd = "addEdgeProperties" # TODO: This function should be command-less and just call a
                                  # `PropGraph` method called add_edge_properties().
        columns = edge_attributes.columns

        ### Modify the inputted dataframe by sorting it and removing duplicates.
        # 1. Sort the data and remove duplicates.
        edge_attributes_gb = edge_attributes.groupby([source_column, destination_column])
        edge_attributes = edge_attributes[edge_attributes_gb.permutation
                                          [edge_attributes_gb.segments]
                                        ]
        self.multied = 0 # TODO: Multigraphs are planned work.

        # 2. Store the modified edge attributes into the class variable.
        self.edge_attributes = edge_attributes
        self.edge_attributes.reset_index(inplace=True)

        # 3. Initialize our src and destination arrays.
        src = edge_attributes[source_column]
        dst = edge_attributes[destination_column]

        # 4. Add edge source and destination column names to property graph.
        self.edge_names = (source_column, destination_column)

        ### Build the graph and load in relationships.
        # 1. Populate the graph object with edges.
        super().add_edges_from(src, dst)

        # 2. Populate the graph object with relationships.
        if relationship_columns is not None and isinstance(relationship_columns, list):
            relationships_to_add = {col: edge_attributes[col] for col in relationship_columns}
            relationships_to_add[source_column] = src
            relationships_to_add[destination_column] = dst
            self.add_edge_relationships(ak.DataFrame(relationships_to_add),
                                                     source_column,
                                                     destination_column,
                                                     assume_sorted=True,
                                                     convert_strings_to_categoricals=\
                                                     convert_string_relationships_to_categoricals)

        ### Prepare the columns that are to be sent to the back-end to be stored per-edge.
        # 1. Remove edges since those are sent separately and any columns marked as relationships.
        columns = [col for col in columns if col not in relationship_columns]\
                  if relationship_columns is not None else list(columns)
        columns.remove(source_column)
        columns.remove(destination_column)

        # 2. Extract symbol table names of arrays to use in the back-end.
        column_ids = []
        edge_property_object_types = []
        for col in columns:
            if isinstance(self.edge_attributes[col], ak.Strings):
                edge_property_object_types.append("Strings")
                column_ids.append(self.edge_attributes[col].name)
            elif isinstance(self.edge_attributes[col], ak.Categorical):
                edge_property_object_types.append("Categorical")
                self.edge_attributes[col].register(generate_string())
                column_ids.append(self.edge_attributes[col].registered_name)
            elif isinstance(self.edge_attributes[col], ak.pdarray):
                edge_property_object_types.append("pdarray")
                column_ids.append(self.edge_attributes[col].name)
            else:
                raise NotImplementedError(f"{type(self.edge_attributes[col])} "
                                          f"not supported by property graph")

        # 3. Generate internal indices for the edges.
        edges = self.edges()
        internal_indices = ak.find([src,dst], [edges[0],edges[1]])

        args = { "GraphName" : self.name,
                 "InputIndicesName" : internal_indices.name,
                 "ColumnNames" : "+".join(columns),
                 "PropertyArrayNames" : "+".join(column_ids),
                 "PropertyArrayTypes" : "+".join(edge_property_object_types)
               }
        ak.generic_msg(cmd=cmd, args=args)

    def get_node_labels(self) -> ak.DataFrame:
        """Returns a a dataframe with the nodes and their labels.

        Returns
        -------
        `ak.DataFrame``
            The node labels of the property graph.
        
        Raises
        ------
        KeyError
        """
        labels = None
        try:
            ns = [self.node_name]
            ns.extend(self.label_columns)
            labels = self.node_attributes[ns]
        except KeyError as exc:
            raise KeyError("no label(s) found") from exc
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

    def get_edge_relationships(self) -> ak.DataFrame:
        """Returns a a dataframe with the edges and their relationships.

        Returns
        -------
        `ak.DataFrame`
            The edge relationships of the property graph.
        """
        relationships = None
        try:
            es = list(self.edge_names)
            es.extend(self.relationship_columns)
            relationships = self.edge_attributes[es]
        except KeyError as exc:
            raise KeyError("no relationship(s) found") from exc
        return relationships

    def get_edge_attributes(self) -> ak.DataFrame:
        """Returns the `ak.DataFrame` object holding all the edge attributes of the `PropGraph`
        object.

        Returns
        -------
        `ak.DataFrame`
            The edge attributes of the graph.
        """
        return self.edge_attributes

    def filter_edges(self,
                     node_types: Dict,
                     edge_types: Dict) -> Tuple[ak.pdarray, ak.pdarray]:
        """Given two dictionaries specifying the node and edge types to search for, it returns all 
        all edges with the matching types.

        Parameters
        ----------
        node_types : Dict
            Dictionary specifying the node attribute names and values to search for. 
        edge_types : Dict
            Dictionary specifying the edge attribute names and values to search for. 

        Returns
        -------
        `(ak.pdarray,ak.pdarray)`
            Edges that contain the given types.
        """
        # 1. Get the nodes and edges that contain the specified node and edge types.
        nodes = self.node_attributes[list(node_types.keys())].isin(node_types)
        edges = self.edge_attributes[list(edge_types.keys())].isin(edge_types)

        print(f"nodes = {nodes.__repr__}")
        print(f"edges = {edges.__repr__}")

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

    def subgraph_view(self, filter_node=no_filter, filter_edge=no_filter):
        """Given user-defined filters on nodes and edges, returns a subgraph that excludes the nodes
        and edges based on the outcomes of `filter_node` and `filter_edge`.

        Both `filter_node` and `filter_edge` take only one argument -- the dataframe induced by 
        node and edge attributes -- and returns a Boolean `pdarray` that is either the size of the
        node set or the edge set.

        Then, only edges where both vertices are kept by `filter_node` are used to construct the
        new graph.

        Parameters
        ----------
        filter_node : callable, optional
            A function taking a dataframe as input, which returns a Boolean `ak.pdarray` if the
            nodes are kept by the filter.

        filter_edge : callable, optional
            A function taking a dataframe as input, which returns a Boolean `ak.pdarray` if the
            edges are kept by the filter.

        Returns
        -------
        graph : ar.DiGraph
            A simple directed graph with the kept edge set.
        """
        filtered_nodes = filter_node(self.node_attributes)
        filtered_edges = filter_edge(self.edge_attributes)

        nodes = self.nodes()
        edges = self.edges()

        nodes = nodes[filtered_nodes]

        src = edges[0][filtered_edges]
        dst = edges[1][filtered_edges]

        src_in_nodes = ak.in1d(src, nodes)
        dst_in_nodes = ak.in1d(dst, nodes)

        kept_edges = src_in_nodes & dst_in_nodes if filter_edge.__name__ != "no_filter" else\
                     src_in_nodes | dst_in_nodes


        src = src[kept_edges]
        dst = dst[kept_edges]

        new_graph = ar.DiGraph()
        new_graph.add_edges_from(src,dst)

        return new_graph
