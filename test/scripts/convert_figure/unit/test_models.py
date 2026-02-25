"""Unit tests for convert_figure data model."""

import pytest

from convert_figure import Edge, Figure, Node, label_to_node_id


# ---- Node ------------------------------------------------------------------


def test_node_stores_id():
    """Node.node_id is accessible after construction."""
    assert Node(node_id="a", label="A").node_id == "a"


def test_node_stores_label():
    """Node.label is accessible after construction."""
    assert Node(node_id="a", label="A").label == "A"


def test_node_is_frozen():
    """Assigning to a frozen Node raises an error."""
    node = Node(node_id="a", label="A")
    with pytest.raises(AttributeError):
        node.node_id = "b"


# ---- Edge ------------------------------------------------------------------


def test_edge_stores_source():
    """Edge.source is accessible after construction."""
    assert Edge(source="a", target="b").source == "a"


def test_edge_stores_target():
    """Edge.target is accessible after construction."""
    assert Edge(source="a", target="b").target == "b"


def test_edge_is_frozen():
    """Assigning to a frozen Edge raises an error."""
    edge = Edge(source="a", target="b")
    with pytest.raises(AttributeError):
        edge.source = "c"


# ---- Figure ----------------------------------------------------------------


def test_figure_stores_number():
    """Figure.number is accessible after construction."""
    fig = Figure(
        number="4-1", title="T", graph_name="G",
        nodes=(), edges=(),
    )
    assert fig.number == "4-1"


def test_figure_stores_title():
    """Figure.title is accessible after construction."""
    fig = Figure(
        number="4-1", title="T", graph_name="G",
        nodes=(), edges=(),
    )
    assert fig.title == "T"


def test_figure_stores_graph_name():
    """Figure.graph_name is accessible after construction."""
    fig = Figure(
        number="4-1", title="T", graph_name="G",
        nodes=(), edges=(),
    )
    assert fig.graph_name == "G"


def test_figure_stores_nodes():
    """Figure.nodes is accessible after construction."""
    n = Node(node_id="a", label="A")
    fig = Figure(
        number="4-1", title="T", graph_name="G",
        nodes=(n,), edges=(),
    )
    assert fig.nodes == (n,)


def test_figure_stores_edges():
    """Figure.edges is accessible after construction."""
    e = Edge(source="a", target="b")
    fig = Figure(
        number="4-1", title="T", graph_name="G",
        nodes=(), edges=(e,),
    )
    assert fig.edges == (e,)


def test_figure_is_frozen():
    """Assigning to a frozen Figure raises an error."""
    fig = Figure(
        number="4-1", title="T", graph_name="G",
        nodes=(), edges=(),
    )
    with pytest.raises(AttributeError):
        fig.number = "5-1"


# ---- label_to_node_id -----------------------------------------------------


def test_label_to_node_id_simple_word():
    """A single word becomes an underscore-joined identifier."""
    assert label_to_node_id("Active") == "Active"


def test_label_to_node_id_hyphenated():
    """Hyphens are removed and casing is preserved."""
    assert label_to_node_id("Pre-Active") == "PreActive"


def test_label_to_node_id_multi_hyphen():
    """Multiple hyphens are all removed."""
    assert label_to_node_id("Re-NBA") == "ReNBA"


def test_label_to_node_id_spaces():
    """Spaces are replaced with underscores."""
    assert label_to_node_id("to next time slot") == "to_next_time_slot"
