"""Unit tests for PDF extraction in convert_figures."""

from unittest.mock import MagicMock, patch

import convert_figures._pdf as pdf_mod
from helpers import mock_text_block

_find_figure_bounds = getattr(pdf_mod, "_find_figure_bounds")
_text_blocks_to_nodes = getattr(pdf_mod, "_text_blocks_to_nodes")
_stems_to_edges = getattr(pdf_mod, "_stems_to_edges")
_arrowheads_to_targets = getattr(pdf_mod, "_arrowheads_to_targets")
_extract_stems_and_arrowheads = getattr(
    pdf_mod, "_extract_stems_and_arrowheads",
)
_nearest_node_above = getattr(pdf_mod, "_nearest_node_above")
_nearest_node_below = getattr(pdf_mod, "_nearest_node_below")
_build_node_positions = getattr(pdf_mod, "_build_node_positions")


# ---- Helpers ---------------------------------------------------------------


def _mock_doc(pages_text):
    """Build a mock fitz.Document from a dict of {page_idx: text}."""
    page_count = max(pages_text) + 1 if pages_text else 0
    doc = MagicMock()
    doc.__len__ = lambda _self: page_count

    def getitem(_self, idx):
        page = MagicMock()
        page.get_text.return_value = pages_text.get(idx, "")
        page.rect = MagicMock()
        page.rect.x0 = 0.0
        page.rect.y0 = 0.0
        page.rect.x1 = 612.0
        page.rect.y1 = 792.0
        return page

    doc.__getitem__ = getitem

    def doc_iter(_self):
        for i in range(page_count):
            yield _self[i]

    doc.__iter__ = doc_iter
    return doc


# ---- open_document ---------------------------------------------------------


def test_open_document_calls_fitz_open(tmp_path):
    """open_document delegates to fitz.open."""
    dummy = tmp_path / "dummy.pdf"
    dummy.write_bytes(b"")
    with patch.object(pdf_mod, "fitz") as mock_fitz:
        mock_fitz.open.return_value = MagicMock()
        pdf_mod.open_document(dummy)
    assert mock_fitz.open.called


# ---- find_clause_pages -----------------------------------------------------


def test_find_clause_pages_single_match():
    """find_clause_pages returns a page that contains the clause heading."""
    doc = _mock_doc({5: "4.4.3 PLI regions\nSome text."})
    assert pdf_mod.find_clause_pages(doc, "4.4.3") == [5]


def test_find_clause_pages_no_match():
    """find_clause_pages returns empty list when clause is absent."""
    doc = _mock_doc({0: "No matching clause here."})
    assert not pdf_mod.find_clause_pages(doc, "99.1")


def test_find_clause_pages_multiple_pages():
    """find_clause_pages returns all pages containing the clause."""
    doc = _mock_doc({
        3: "4.4 Scheduling semantics",
        4: "4.4 continued discussion",
    })
    assert pdf_mod.find_clause_pages(doc, "4.4") == [3, 4]


def test_find_clause_pages_ignores_substring():
    """find_clause_pages does not match '4.4' inside '4.4.3'."""
    doc = _mock_doc({0: "4.4.3 PLI regions"})
    assert not pdf_mod.find_clause_pages(doc, "4.4")


# ---- find_figure_captions --------------------------------------------------


def test_find_figure_captions_found():
    """find_figure_captions returns figure data when caption is present."""
    page = MagicMock()
    blocks = [mock_text_block(
        "Figure 4-1\u2014Event scheduling regions",
        200, 690, 400, 700,
    )]
    page.get_text.return_value = {"blocks": blocks}
    page.search_for.return_value = [MagicMock(
        x0=200, y0=690, x1=400, y1=700,
    )]
    doc = MagicMock()
    doc.__getitem__ = lambda self, idx: page
    result = pdf_mod.find_figure_captions(doc, [0], "4")
    assert len(result) == 1


def test_find_figure_captions_extracts_number():
    """find_figure_captions extracts the figure number."""
    page = MagicMock()
    page.search_for.return_value = [MagicMock(
        x0=200, y0=690, x1=400, y1=700,
    )]
    page.get_text.return_value = {
        "blocks": [mock_text_block(
            "Figure 4-1\u2014Title", 200, 690, 400, 700,
        )],
    }
    doc = MagicMock()
    doc.__getitem__ = lambda self, idx: page
    result = pdf_mod.find_figure_captions(doc, [0], "4")
    assert result[0][1] == "4-1"


def test_find_figure_captions_extracts_title():
    """find_figure_captions extracts the figure title."""
    page = MagicMock()
    page.search_for.return_value = [MagicMock(
        x0=200, y0=690, x1=400, y1=700,
    )]
    page.get_text.return_value = {
        "blocks": [mock_text_block(
            "Figure 4-1\u2014Event scheduling regions",
            200, 690, 400, 700,
        )],
    }
    doc = MagicMock()
    doc.__getitem__ = lambda self, idx: page
    result = pdf_mod.find_figure_captions(doc, [0], "4")
    assert result[0][2] == "Event scheduling regions"


def test_find_figure_captions_no_figure():
    """find_figure_captions returns empty when no caption matches."""
    page = MagicMock()
    page.search_for.return_value = []
    page.get_text.return_value = {"blocks": []}
    doc = MagicMock()
    doc.__getitem__ = lambda self, idx: page
    assert not pdf_mod.find_figure_captions(doc, [0], "99")


# ---- _find_figure_bounds ---------------------------------------------------


def test_find_figure_bounds_returns_rect():
    """_find_figure_bounds returns a 4-tuple bounding box."""
    bounds = _find_figure_bounds(
        caption_y=690.0, page_top=50.0,
    )
    assert len(bounds) == 4


def test_find_figure_bounds_top_above_caption():
    """The figure area top is above the caption y."""
    bounds = _find_figure_bounds(
        caption_y=690.0, page_top=50.0,
    )
    assert bounds[1] < 690.0


def test_find_figure_bounds_bottom_at_caption():
    """The figure area bottom is at or near the caption y."""
    bounds = _find_figure_bounds(
        caption_y=690.0, page_top=50.0,
    )
    assert bounds[3] >= 690.0


# ---- _text_blocks_to_nodes ------------------------------------------------


def test_text_blocks_to_nodes_extracts_labels():
    """_text_blocks_to_nodes extracts node labels from text blocks."""
    blocks = [
        mock_text_block("Active", 307, 208, 332, 218),
        mock_text_block("Inactive", 303, 251, 335, 261),
    ]
    bounds = (0, 100, 600, 700)
    nodes = _text_blocks_to_nodes(blocks, bounds)
    assert len(nodes) == 2


def test_text_blocks_to_nodes_sets_label():
    """_text_blocks_to_nodes preserves the label text."""
    blocks = [mock_text_block("Pre-Active", 298, 165, 340, 175)]
    nodes = _text_blocks_to_nodes(blocks, (0, 100, 600, 700))
    assert nodes[0].label == "Pre-Active"


def test_text_blocks_to_nodes_sets_node_id():
    """_text_blocks_to_nodes derives node_id from label."""
    blocks = [mock_text_block("Pre-Active", 298, 165, 340, 175)]
    nodes = _text_blocks_to_nodes(blocks, (0, 100, 600, 700))
    assert nodes[0].node_id == "PreActive"


def test_text_blocks_to_nodes_filters_outside_bounds():
    """_text_blocks_to_nodes ignores text outside the figure bounds."""
    blocks = [
        mock_text_block("Active", 307, 208, 332, 218),
        mock_text_block("Page header", 100, 30, 400, 40),
    ]
    bounds = (0, 100, 600, 700)
    nodes = _text_blocks_to_nodes(blocks, bounds)
    assert len(nodes) == 1


def test_text_blocks_to_nodes_filters_caption():
    """_text_blocks_to_nodes ignores lines starting with 'Figure'."""
    blocks = [
        mock_text_block("Active", 307, 208, 332, 218),
        mock_text_block("Figure 4-1\u2014Title", 200, 690, 400, 700),
    ]
    bounds = (0, 100, 600, 750)
    nodes = _text_blocks_to_nodes(blocks, bounds)
    assert len(nodes) == 1


def test_text_blocks_to_nodes_filters_legend():
    """_text_blocks_to_nodes ignores 'Legend:' text."""
    blocks = [
        mock_text_block("Active", 307, 208, 332, 218),
        mock_text_block("Legend:", 139, 256, 175, 267),
    ]
    bounds = (0, 100, 600, 700)
    nodes = _text_blocks_to_nodes(blocks, bounds)
    assert len(nodes) == 1


# ---- _stems_to_edges ------------------------------------------------------


def test_stems_to_edges_connects_sequential_nodes():
    """_stems_to_edges creates an edge for a vertical stem between nodes."""
    node_positions = {"A": (300.0, 120.0), "B": (300.0, 170.0)}
    stems = [{"y_top": 137.0, "y_bottom": 155.0, "x_center": 319.0}]
    edges = _stems_to_edges(stems, node_positions)
    assert len(edges) == 1


def test_stems_to_edges_source_is_above():
    """_stems_to_edges assigns the upper node as source."""
    node_positions = {"A": (300.0, 120.0), "B": (300.0, 170.0)}
    stems = [{"y_top": 137.0, "y_bottom": 155.0, "x_center": 319.0}]
    edges = _stems_to_edges(stems, node_positions)
    assert edges[0].source == "A"


def test_stems_to_edges_target_is_below():
    """_stems_to_edges assigns the lower node as target."""
    node_positions = {"A": (300.0, 120.0), "B": (300.0, 170.0)}
    stems = [{"y_top": 137.0, "y_bottom": 155.0, "x_center": 319.0}]
    edges = _stems_to_edges(stems, node_positions)
    assert edges[0].target == "B"


def test_stems_to_edges_ignores_short_stems():
    """_stems_to_edges ignores stems shorter than a threshold."""
    node_positions = {"A": (300.0, 120.0), "B": (300.0, 170.0)}
    stems = [{"y_top": 120.0, "y_bottom": 122.0, "x_center": 319.0}]
    edges = _stems_to_edges(stems, node_positions)
    assert len(edges) == 0


# ---- _arrowheads_to_targets ------------------------------------------------


def test_arrowheads_to_targets_finds_target():
    """_arrowheads_to_targets maps arrowhead position to nearest node."""
    node_positions = {"A": (300.0, 120.0), "B": (300.0, 170.0)}
    arrowheads = [{"x": 318.0, "y": 155.0}]
    targets = _arrowheads_to_targets(arrowheads, node_positions)
    assert targets[0] == "B"


def test_arrowheads_to_targets_picks_nearest():
    """_arrowheads_to_targets selects the closest node."""
    node_positions = {"A": (300.0, 120.0), "B": (300.0, 300.0)}
    arrowheads = [{"x": 318.0, "y": 125.0}]
    targets = _arrowheads_to_targets(arrowheads, node_positions)
    assert targets[0] == "A"


# ---- extract_figure --------------------------------------------------------


def test_extract_figure_returns_figure():
    """extract_figure returns a Figure with nodes and edges."""
    page = MagicMock()
    page.get_text.return_value = {
        "blocks": [
            mock_text_block("Active", 307, 208, 332, 218),
            mock_text_block("Inactive", 303, 251, 335, 261),
        ],
    }
    page.get_drawings.return_value = []
    page.rect = MagicMock(x0=0, y0=0, x1=612, y1=792)
    fig = pdf_mod.extract_figure(
        page=page,
        figure_number="4-1",
        figure_title="Event scheduling regions",
        caption_y=690.0,
    )
    assert fig.number == "4-1"


def test_extract_figure_has_nodes():
    """extract_figure populates nodes from text blocks."""
    page = MagicMock()
    page.get_text.return_value = {
        "blocks": [
            mock_text_block("Active", 307, 208, 332, 218),
        ],
    }
    page.get_drawings.return_value = []
    page.rect = MagicMock(x0=0, y0=0, x1=612, y1=792)
    fig = pdf_mod.extract_figure(
        page=page,
        figure_number="4-1",
        figure_title="T",
        caption_y=690.0,
    )
    assert len(fig.nodes) == 1


def test_extract_figure_graph_name():
    """extract_figure sets graph_name from the figure number."""
    page = MagicMock()
    page.get_text.return_value = {
        "blocks": [mock_text_block("A", 300, 200, 340, 210)],
    }
    page.get_drawings.return_value = []
    page.rect = MagicMock(x0=0, y0=0, x1=612, y1=792)
    fig = pdf_mod.extract_figure(
        page=page,
        figure_number="4-1",
        figure_title="T",
        caption_y=690.0,
    )
    assert fig.graph_name == "Figure_4_1"


# ---- _text_blocks_to_nodes edge cases -------------------------------------


def test_text_blocks_to_nodes_filters_time_slot():
    """_text_blocks_to_nodes ignores 'time slot' text."""
    blocks = [
        mock_text_block("Active", 307, 208, 332, 218),
        mock_text_block("from previous time slot", 147, 103, 201, 113),
    ]
    bounds = (0, 100, 600, 700)
    nodes = _text_blocks_to_nodes(blocks, bounds)
    assert len(nodes) == 1


def test_text_blocks_to_nodes_skips_image_blocks():
    """_text_blocks_to_nodes skips non-text (image) blocks."""
    blocks = [
        {"type": 1, "bbox": (0, 0, 100, 100)},
        mock_text_block("Active", 307, 208, 332, 218),
    ]
    bounds = (0, 100, 600, 700)
    nodes = _text_blocks_to_nodes(blocks, bounds)
    assert len(nodes) == 1


def test_text_blocks_to_nodes_skips_empty_text():
    """_text_blocks_to_nodes skips empty text."""
    blocks = [
        mock_text_block("", 307, 208, 332, 218),
        mock_text_block("Active", 307, 250, 332, 260),
    ]
    bounds = (0, 100, 600, 700)
    nodes = _text_blocks_to_nodes(blocks, bounds)
    assert len(nodes) == 1


def test_text_blocks_to_nodes_filters_skip_labels():
    """_text_blocks_to_nodes ignores 'region' and 'PLI region' text."""
    blocks = [
        mock_text_block("Active", 307, 208, 332, 218),
        mock_text_block("region", 167, 286, 192, 296),
        mock_text_block("PLI region", 159, 318, 200, 328),
    ]
    bounds = (0, 100, 600, 700)
    nodes = _text_blocks_to_nodes(blocks, bounds)
    assert len(nodes) == 1


# ---- _nearest_node_above / _nearest_node_below ----------------------------


def test_nearest_node_above_no_match():
    """_nearest_node_above returns None when no node is above."""
    result = _nearest_node_above(50.0, {"A": (300.0, 200.0)})
    assert result is None


def test_nearest_node_below_no_match():
    """_nearest_node_below returns None when no node is below."""
    result = _nearest_node_below(500.0, {"A": (300.0, 200.0)})
    assert result is None


# ---- _extract_stems_and_arrowheads ----------------------------------------


def _make_rect_drawing(x0, y0, x1, y1, fill):
    """Build a mock drawing dict with a rectangle item."""
    rect = MagicMock()
    rect.width = x1 - x0
    rect.height = y1 - y0
    rect.x0 = x0
    rect.y0 = y0
    rect.x1 = x1
    rect.y1 = y1
    return {
        "rect": rect,
        "items": [("re", (x0, y0, x1, y1))],
        "fill": fill,
    }


def test_extract_stems_finds_stem():
    """_extract_stems_and_arrowheads identifies a stem drawing."""
    drawing = _make_rect_drawing(319.0, 137.0, 320.0, 155.0, (0, 0, 0))
    stems, _ = _extract_stems_and_arrowheads([drawing])
    assert len(stems) == 1


def test_extract_stems_finds_arrowhead():
    """_extract_stems_and_arrowheads identifies an arrowhead drawing."""
    drawing = _make_rect_drawing(317.0, 155.0, 319.0, 156.0, (0, 0, 0))
    _, arrowheads = _extract_stems_and_arrowheads([drawing])
    assert len(arrowheads) == 1


def test_extract_stems_ignores_no_rect_item():
    """_extract_stems_and_arrowheads skips drawings without 're' items."""
    rect = MagicMock()
    rect.width = 1.0
    rect.height = 1.0
    rect.x0 = 0.0
    rect.y0 = 0.0
    rect.x1 = 1.0
    rect.y1 = 1.0
    drawing = {
        "rect": rect,
        "items": [("l", (0, 0), (1, 1))],
        "fill": (0, 0, 0),
    }
    stems, _ = _extract_stems_and_arrowheads([drawing])
    assert len(stems) == 0


def test_extract_stems_ignores_no_fill():
    """_extract_stems_and_arrowheads skips drawings without fill."""
    drawing = _make_rect_drawing(317.0, 155.0, 319.0, 156.0, None)
    _, arrowheads = _extract_stems_and_arrowheads([drawing])
    assert len(arrowheads) == 0


def test_extract_stems_ignores_no_rect():
    """_extract_stems_and_arrowheads skips drawings without rect."""
    drawing = {"items": [("re", (0, 0, 1, 1))], "fill": (0, 0, 0)}
    stems, _ = _extract_stems_and_arrowheads([drawing])
    assert len(stems) == 0


def test_extract_stems_white_fill_not_arrowhead():
    """_extract_stems_and_arrowheads ignores white-filled small rects."""
    drawing = _make_rect_drawing(317.0, 155.0, 319.0, 156.0, (1, 1, 1))
    _, arrowheads = _extract_stems_and_arrowheads([drawing])
    assert len(arrowheads) == 0


def test_extract_stems_large_area_not_stem():
    """_extract_stems_and_arrowheads ignores large-area rectangles."""
    drawing = _make_rect_drawing(100.0, 100.0, 200.0, 200.0, (0, 0, 0))
    stems, _ = _extract_stems_and_arrowheads([drawing])
    assert len(stems) == 0


# ---- _stems_to_edges edge cases -------------------------------------------


def test_stems_to_edges_no_source_match():
    """_stems_to_edges skips stem when no source node is found."""
    node_positions = {"B": (300.0, 170.0)}
    stems = [{"y_top": 50.0, "y_bottom": 155.0, "x_center": 319.0}]
    edges = _stems_to_edges(stems, node_positions)
    assert len(edges) == 0


def test_stems_to_edges_same_source_and_target():
    """_stems_to_edges skips stem when source and target are the same."""
    node_positions = {"A": (300.0, 120.0)}
    stems = [{"y_top": 115.0, "y_bottom": 125.0, "x_center": 319.0}]
    edges = _stems_to_edges(stems, node_positions)
    assert len(edges) == 0


# ---- find_figure_captions edge cases ---------------------------------------


def test_find_figure_captions_skips_non_text_blocks():
    """find_figure_captions ignores image blocks."""
    page = MagicMock()
    page.search_for.return_value = [MagicMock(
        x0=200, y0=690, x1=400, y1=700,
    )]
    page.get_text.return_value = {
        "blocks": [
            {"type": 1, "bbox": (0, 0, 100, 100)},
            mock_text_block(
                "Figure 4-1\u2014Title", 200, 690, 400, 700,
            ),
        ],
    }
    doc = MagicMock()
    doc.__getitem__ = lambda self, idx: page
    result = pdf_mod.find_figure_captions(doc, [0], "4")
    assert len(result) == 1


def test_find_figure_captions_skips_non_matching_text():
    """find_figure_captions ignores text not matching figure pattern."""
    page = MagicMock()
    page.search_for.return_value = [MagicMock(
        x0=200, y0=690, x1=400, y1=700,
    )]
    page.get_text.return_value = {
        "blocks": [
            mock_text_block("Some random text", 200, 200, 400, 210),
            mock_text_block(
                "Figure 4-1\u2014Title", 200, 690, 400, 700,
            ),
        ],
    }
    doc = MagicMock()
    doc.__getitem__ = lambda self, idx: page
    result = pdf_mod.find_figure_captions(doc, [0], "4")
    assert len(result) == 1


# ---- _arrowheads_to_targets edge cases ------------------------------------


def test_arrowheads_to_targets_no_match():
    """_arrowheads_to_targets skips arrowheads far from any node."""
    node_positions = {"A": (300.0, 120.0)}
    arrowheads = [{"x": 900.0, "y": 900.0}]
    targets = _arrowheads_to_targets(arrowheads, node_positions)
    assert len(targets) == 0


# ---- extract_figure edge cases --------------------------------------------


def test_extract_figure_skips_image_block_in_positions():
    """extract_figure skips image blocks when building node positions."""
    page = MagicMock()
    page.get_text.return_value = {
        "blocks": [
            mock_text_block("Active", 307, 208, 332, 218),
            {"type": 1, "bbox": (0, 0, 100, 100)},
        ],
    }
    page.get_drawings.return_value = []
    page.rect = MagicMock(x0=0, y0=0, x1=612, y1=792)
    fig = pdf_mod.extract_figure(
        page=page,
        figure_number="4-1",
        figure_title="T",
        caption_y=690.0,
    )
    assert len(fig.nodes) == 1


def test_extract_figure_non_node_text_not_in_positions():
    """extract_figure excludes filtered text from node positions."""
    page = MagicMock()
    page.get_text.return_value = {
        "blocks": [
            mock_text_block("Active", 307, 208, 332, 218),
            mock_text_block("Legend:", 139, 256, 175, 267),
        ],
    }
    page.get_drawings.return_value = []
    page.rect = MagicMock(x0=0, y0=0, x1=612, y1=792)
    fig = pdf_mod.extract_figure(
        page=page,
        figure_number="4-1",
        figure_title="T",
        caption_y=690.0,
    )
    assert len(fig.nodes) == 1
