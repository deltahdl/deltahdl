"""Extract figure data from the LRM PDF using pymupdf."""

import re
from pathlib import Path

import fitz

from convert_figures._dot import figure_number_to_graph_name
from convert_figures._models import Edge, Figure, Node, label_to_node_id

_CAPTION_RE = re.compile(
    r"Figure\s+(\d+[A-Z]?-\d+)\s*\u2014\s*(.+)",
)

_SKIP_LABELS = frozenset({
    "Legend:",
    "region",
    "PLI region",
})

_MIN_STEM_HEIGHT = 5.0
_NODE_MATCH_TOLERANCE = 25.0


def open_document(lrm_path: Path) -> fitz.Document:
    """Open the LRM PDF and return a pymupdf Document."""
    return fitz.open(str(lrm_path))


def find_clause_pages(
    doc: fitz.Document,
    clause: str,
) -> list[int]:
    """Find page numbers containing the given clause heading.

    Matches clause numbers at word boundaries to avoid '4.4' matching
    inside '4.4.3'.
    """
    pattern = re.compile(
        rf"(?<!\d)(?<!\.){re.escape(clause)}(?!\.\d)(?!\d)\s",
    )
    pages: list[int] = []
    for i, page in enumerate(doc):
        text = page.get_text()
        if pattern.search(text):
            pages.append(i)
    return pages


def find_figure_captions(
    doc: fitz.Document,
    pages: list[int],
    clause: str,
) -> list[tuple[int, str, str, float]]:
    """Find figure captions on the given pages.

    Returns list of (page_number, figure_number, figure_title, caption_y).
    """
    search_text = f"Figure {clause.split('.')[0]}-"
    results: list[tuple[int, str, str, float]] = []
    for page_idx in pages:
        page = doc[page_idx]
        if not page.search_for(search_text):
            continue
        blocks = page.get_text("dict")["blocks"]
        for block in blocks:
            if block.get("type") != 0:
                continue
            for line in block["lines"]:
                full_text = " ".join(
                    span["text"] for span in line["spans"]
                )
                match = _CAPTION_RE.search(full_text)
                if match:
                    results.append((
                        page_idx,
                        match.group(1),
                        match.group(2).strip(),
                        line["bbox"][1],
                    ))
    return results


def _find_figure_bounds(
    caption_y: float,
    page_top: float,
) -> tuple[float, float, float, float]:
    """Determine the bounding rectangle of a figure on the page.

    Returns (x0, y_top, x1, y_bottom) where the figure extends from
    above the caption up to the page content area top.
    """
    y_top = page_top
    y_bottom = caption_y + 10.0
    return (0.0, y_top, 612.0, y_bottom)


def _iter_text_lines(
    blocks: list[dict],
) -> list[tuple[str, tuple[float, float, float, float]]]:
    """Extract (text, bbox) pairs from pymupdf text blocks."""
    results: list[tuple[str, tuple[float, float, float, float]]] = []
    for block in blocks:
        if block.get("type") != 0:
            continue
        for line in block["lines"]:
            text = " ".join(
                span["text"] for span in line["spans"]
            ).strip()
            results.append((text, line["bbox"]))
    return results


def _text_blocks_to_nodes(
    blocks: list[dict],
    bounds: tuple[float, float, float, float],
) -> list[Node]:
    """Convert text blocks within figure bounds to Nodes.

    Filters out page headers, captions, legend text, and labels
    containing 'time slot'.
    """
    _, y_top, _, y_bottom = bounds
    nodes: list[Node] = []
    for text, bbox in _iter_text_lines(blocks):
        y_center = (bbox[1] + bbox[3]) / 2.0
        if y_center < y_top or y_center > y_bottom:
            continue
        if not text or text in _SKIP_LABELS:
            continue
        if text.startswith("Figure"):
            continue
        if "time slot" in text.lower():
            continue
        node_id = label_to_node_id(text)
        nodes.append(Node(node_id=node_id, label=text))
    return nodes


def _stems_to_edges(
    stems: list[dict],
    node_positions: dict[str, tuple[float, float]],
) -> list[Edge]:
    """Convert vertical arrow stems to edges.

    Each stem dict has y_top, y_bottom, x_center.  Stems shorter than
    _MIN_STEM_HEIGHT are ignored.
    """
    edges: list[Edge] = []
    for stem in stems:
        height = stem["y_bottom"] - stem["y_top"]
        if height < _MIN_STEM_HEIGHT:
            continue
        mid_top = stem["y_top"]
        mid_bot = stem["y_bottom"]
        source = _nearest_node_above(mid_top, node_positions)
        target = _nearest_node_below(mid_bot, node_positions)
        if source and target and source != target:
            edges.append(Edge(source=source, target=target))
    return edges


def _nearest_node_above(
    y_pos: float,
    node_positions: dict[str, tuple[float, float]],
) -> str | None:
    """Find the node whose y-center is closest above y_pos."""
    best_id: str | None = None
    best_dist = _NODE_MATCH_TOLERANCE
    for node_id, (_, node_y) in node_positions.items():
        dist = y_pos - node_y
        if 0 < dist < best_dist:
            best_dist = dist
            best_id = node_id
    return best_id


def _nearest_node_below(
    y_pos: float,
    node_positions: dict[str, tuple[float, float]],
) -> str | None:
    """Find the node whose y-center is closest below y_pos."""
    best_id: str | None = None
    best_dist = _NODE_MATCH_TOLERANCE
    for node_id, (_, node_y) in node_positions.items():
        dist = node_y - y_pos
        if 0 < dist < best_dist:
            best_dist = dist
            best_id = node_id
    return best_id


def _arrowheads_to_targets(
    arrowheads: list[dict],
    node_positions: dict[str, tuple[float, float]],
) -> list[str]:
    """Map arrowhead positions to the nearest node (the edge target)."""
    targets: list[str] = []
    for head in arrowheads:
        best_id: str | None = None
        best_dist = _NODE_MATCH_TOLERANCE
        hx, hy = head["x"], head["y"]
        for node_id, (nx, ny) in node_positions.items():
            dist = ((hx - nx) ** 2 + (hy - ny) ** 2) ** 0.5
            if dist < best_dist:
                best_dist = dist
                best_id = node_id
        if best_id:
            targets.append(best_id)
    return targets


def _extract_stems_and_arrowheads(
    drawings: list[dict],
) -> tuple[list[dict], list[dict]]:
    """Categorize drawings into arrow stems and arrowheads.

    Stems are thin tall filled rectangles.  Arrowheads are small
    filled shapes (area < 5) near arrow endpoints.
    """
    stems: list[dict] = []
    arrowheads: list[dict] = []
    for drawing in drawings:
        rect = drawing.get("rect")
        if rect is None:
            continue
        has_re = any(
            item[0] == "re" for item in drawing.get("items", [])
        )
        fill = drawing.get("fill")
        if not has_re or fill is None:
            continue
        width = rect.width if hasattr(rect, "width") else (
            rect[2] - rect[0]
        )
        height = rect.height if hasattr(rect, "height") else (
            rect[3] - rect[1]
        )
        area = width * height
        x0 = rect.x0 if hasattr(rect, "x0") else rect[0]
        y0 = rect.y0 if hasattr(rect, "y0") else rect[1]
        x1 = rect.x1 if hasattr(rect, "x1") else rect[2]
        y1 = rect.y1 if hasattr(rect, "y1") else rect[3]
        if 8 < area < 25 and height > _MIN_STEM_HEIGHT:
            stems.append({
                "y_top": y0,
                "y_bottom": y1,
                "x_center": (x0 + x1) / 2.0,
            })
        elif area < 5 and fill == (0.0, 0.0, 0.0):
            arrowheads.append({
                "x": (x0 + x1) / 2.0,
                "y": (y0 + y1) / 2.0,
            })
    return stems, arrowheads


def _build_node_positions(
    blocks: list[dict],
    nodes: list[Node],
) -> dict[str, tuple[float, float]]:
    """Build a mapping from node_id to (x_center, y_center) positions."""
    positions: dict[str, tuple[float, float]] = {}
    for text, bbox in _iter_text_lines(blocks):
        node_id = label_to_node_id(text)
        if any(n.node_id == node_id for n in nodes):
            positions[node_id] = (
                (bbox[0] + bbox[2]) / 2.0,
                (bbox[1] + bbox[3]) / 2.0,
            )
    return positions


def extract_figure(
    page: fitz.Page,
    figure_number: str,
    figure_title: str,
    caption_y: float,
) -> Figure:
    """Extract a complete Figure from a PDF page."""
    page_top = page.rect.y0 + 50.0
    bounds = _find_figure_bounds(caption_y, page_top)

    blocks = page.get_text("dict")["blocks"]
    nodes = _text_blocks_to_nodes(blocks, bounds)
    node_positions = _build_node_positions(blocks, nodes)

    stems, _ = _extract_stems_and_arrowheads(page.get_drawings())
    edges = _stems_to_edges(stems, node_positions)

    return Figure(
        number=figure_number,
        title=figure_title,
        graph_name=figure_number_to_graph_name(figure_number),
        nodes=tuple(nodes),
        edges=tuple(edges),
    )
