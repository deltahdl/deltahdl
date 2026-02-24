"""Shared test helpers for convert_figures unit tests."""

from convert_figures._models import Edge, Figure, Node


def make_node(
    node_id="region_Active",
    label="region: Active",
):
    """Shorthand factory for Node."""
    return Node(node_id=node_id, label=label)


def make_edge(
    source="region_Active",
    target="region_Inactive",
):
    """Shorthand factory for Edge."""
    return Edge(source=source, target=target)


def make_figure(
    number="4-1",
    title="Event scheduling regions",
    graph_name="Figure_4_1",
    nodes=None,
    edges=None,
):
    """Shorthand factory for Figure."""
    return Figure(
        number=number,
        title=title,
        graph_name=graph_name,
        nodes=nodes if nodes is not None else (make_node(),),
        edges=edges if edges is not None else (make_edge(),),
    )
