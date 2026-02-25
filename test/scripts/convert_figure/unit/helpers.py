"""Shared test helpers for convert_figure unit tests."""

from convert_figure._models import Edge, Figure, Node


def mock_text_block(text, x0, y0, x1, y1):
    """Build a text-block dict matching pymupdf get_text('dict') format."""
    return {
        "type": 0,
        "bbox": (x0, y0, x1, y1),
        "lines": [{
            "bbox": (x0, y0, x1, y1),
            "spans": [{"text": text, "bbox": (x0, y0, x1, y1)}],
        }],
    }


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
