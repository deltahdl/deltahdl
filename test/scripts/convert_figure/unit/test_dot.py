"""Unit tests for DOT generation in convert_figure."""

from convert_figure import (
    figure_number_to_graph_name,
    format_edge,
    format_node,
    generate_dot,
)
from helpers import make_edge, make_figure, make_node


# ---- format_node -----------------------------------------------------------


def test_format_node_basic():
    """format_node produces node_id [label="..."] syntax."""
    assert format_node(make_node()) == '  region_Active [label="region: Active"];'


def test_format_node_quoted_label():
    """format_node handles labels with special characters."""
    node = make_node(node_id="n", label='say "hello"')
    assert 'label="say \\"hello\\""' in format_node(node)


def test_format_node_special_id_quoted():
    """format_node quotes node IDs containing special characters."""
    node = make_node(node_id="trdy_(high)", label="trdy (high)")
    assert format_node(node) == '  "trdy_(high)" [label="trdy (high)"];'


def test_format_node_plain_id_unquoted():
    """format_node does not quote simple alphanumeric node IDs."""
    node = make_node(node_id="data_phase", label="data_phase")
    assert format_node(node) == '  data_phase [label="data_phase"];'


# ---- format_edge -----------------------------------------------------------


def test_format_edge_basic():
    """format_edge produces source -> target syntax."""
    assert format_edge(make_edge()) == "  region_Active -> region_Inactive;"


def test_format_edge_special_ids_quoted():
    """format_edge quotes node IDs containing special characters."""
    edge = make_edge(source="[1:2]", target="trdy_(high)")
    assert format_edge(edge) == '  "[1:2]" -> "trdy_(high)";'


# ---- figure_number_to_graph_name -------------------------------------------


def test_figure_number_to_graph_name_basic():
    """Converts '4-1' to 'Figure_4_1'."""
    assert figure_number_to_graph_name("4-1") == "Figure_4_1"


def test_figure_number_to_graph_name_multi_digit():
    """Converts '12-3' to 'Figure_12_3'."""
    assert figure_number_to_graph_name("12-3") == "Figure_12_3"


# ---- generate_dot ----------------------------------------------------------


def test_generate_dot_header():
    """Output starts with digraph declaration."""
    assert generate_dot(make_figure()).startswith("digraph Figure_4_1 {")


def test_generate_dot_rankdir():
    """Output contains rankdir=TB."""
    assert "rankdir=TB;" in generate_dot(make_figure())


def test_generate_dot_contains_node():
    """Output contains the formatted node."""
    assert 'region_Active [label="region: Active"]' in generate_dot(
        make_figure(),
    )


def test_generate_dot_contains_edge():
    """Output contains the formatted edge."""
    assert "region_Active -> region_Inactive;" in generate_dot(make_figure())


def test_generate_dot_closing_brace():
    """Output ends with a closing brace."""
    assert generate_dot(make_figure()).rstrip().endswith("}")


def test_generate_dot_multiple_nodes():
    """All nodes appear in the output."""
    n1 = make_node(node_id="a", label="A")
    n2 = make_node(node_id="b", label="B")
    fig = make_figure(nodes=(n1, n2))
    dot = generate_dot(fig)
    assert 'a [label="A"]' in dot


def test_generate_dot_multiple_nodes_second():
    """Second node also appears in the output."""
    n1 = make_node(node_id="a", label="A")
    n2 = make_node(node_id="b", label="B")
    fig = make_figure(nodes=(n1, n2))
    dot = generate_dot(fig)
    assert 'b [label="B"]' in dot


def test_generate_dot_multiple_edges():
    """All edges appear in the output."""
    e1 = make_edge(source="a", target="b")
    e2 = make_edge(source="c", target="d")
    fig = make_figure(edges=(e1, e2))
    dot = generate_dot(fig)
    assert "a -> b;" in dot


def test_generate_dot_multiple_edges_second():
    """Second edge also appears in the output."""
    e1 = make_edge(source="a", target="b")
    e2 = make_edge(source="c", target="d")
    fig = make_figure(edges=(e1, e2))
    dot = generate_dot(fig)
    assert "c -> d;" in dot


def test_generate_dot_empty_figure_starts_with_digraph():
    """An empty figure DOT output starts with 'digraph'."""
    fig = make_figure(nodes=(), edges=())
    dot = generate_dot(fig)
    assert dot.startswith("digraph")


def test_generate_dot_empty_figure_ends_with_brace():
    """An empty figure DOT output ends with '}'."""
    fig = make_figure(nodes=(), edges=())
    dot = generate_dot(fig)
    assert dot.rstrip().endswith("}")
