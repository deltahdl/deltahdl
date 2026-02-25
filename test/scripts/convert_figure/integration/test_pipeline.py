"""Integration tests for the convert_figure pipeline."""

from unittest.mock import MagicMock

from convert_figure._dot import generate_dot
from convert_figure._pdf import extract_figure


# ---- Pipeline: mocked page -> Figure -> DOT --------------------------------


def _mock_page(text_blocks, drawings=None):
    """Build a mock fitz.Page with text blocks and optional drawings."""
    blocks = []
    for text, x0, y0, x1, y1 in text_blocks:
        bbox = (x0, y0, x1, y1)
        span = {"text": text, "bbox": bbox}
        line = {"bbox": bbox, "spans": [span]}
        blocks.append({"type": 0, "bbox": bbox, "lines": [line]})
    page = MagicMock()
    page.get_text.return_value = {"blocks": blocks}
    page.get_drawings.return_value = drawings or []
    page.rect = MagicMock(x0=0, y0=0, x1=612, y1=792)
    return page


def test_pipeline_produces_valid_digraph():
    """Pipeline from mocked page data produces a digraph."""
    page = _mock_page([("Active", 307, 208, 332, 218)])
    fig = extract_figure(
        page=page, figure_number="4-1",
        figure_title="T", caption_y=690.0,
    )
    dot = generate_dot(fig)
    assert dot.startswith("digraph Figure_4_1 {")


def test_pipeline_figure_number_in_graph_name():
    """Graph name includes the figure number."""
    page = _mock_page([("Active", 307, 208, 332, 218)])
    fig = extract_figure(
        page=page, figure_number="6-2",
        figure_title="T", caption_y=690.0,
    )
    dot = generate_dot(fig)
    assert "Figure_6_2" in dot


def test_pipeline_nodes_from_text():
    """Nodes extracted from page text appear in DOT output."""
    page = _mock_page([
        ("Preponed", 300, 121, 339, 131),
        ("Active", 307, 208, 332, 218),
    ])
    fig = extract_figure(
        page=page, figure_number="4-1",
        figure_title="T", caption_y=690.0,
    )
    dot = generate_dot(fig)
    assert 'Preponed [label="Preponed"]' in dot


def test_pipeline_filters_non_node_text():
    """Legend and caption text is excluded from DOT nodes."""
    page = _mock_page([
        ("Active", 307, 208, 332, 218),
        ("Legend:", 139, 256, 175, 267),
        ("Figure 4-1\u2014Title", 200, 690, 400, 700),
    ])
    fig = extract_figure(
        page=page, figure_number="4-1",
        figure_title="T", caption_y=690.0,
    )
    assert len(fig.nodes) == 1


def test_pipeline_closing_brace():
    """DOT output ends with closing brace."""
    page = _mock_page([("Active", 307, 208, 332, 218)])
    fig = extract_figure(
        page=page, figure_number="4-1",
        figure_title="T", caption_y=690.0,
    )
    dot = generate_dot(fig)
    assert dot.rstrip().endswith("}")
