"""Convert figures from the IEEE 1800-2023 SystemVerilog LRM to DOT."""

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

import fitz


# ---------------------------------------------------------------------------
# Data model
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class Node:
    """A graph node representing a labeled box in a figure."""

    node_id: str
    label: str


@dataclass(frozen=True)
class Edge:
    """A directed edge between two nodes."""

    source: str
    target: str


@dataclass(frozen=True)
class Figure:
    """A complete figure extracted from the LRM."""

    number: str
    title: str
    graph_name: str
    nodes: tuple[Node, ...]
    edges: tuple[Edge, ...]


def label_to_node_id(label: str) -> str:
    """Convert a figure label to a DOT node identifier.

    Removes hyphens and replaces spaces with underscores.
    """
    return label.replace("-", "").replace(" ", "_")


# ---------------------------------------------------------------------------
# DOT generation
# ---------------------------------------------------------------------------


def _quote_id(node_id: str) -> str:
    """Quote a DOT identifier if it contains special characters."""
    if re.match(r"^[A-Za-z_][A-Za-z0-9_]*$", node_id):
        return node_id
    escaped = node_id.replace('"', '\\"')
    return f'"{escaped}"'


def format_node(node: Node) -> str:
    """Format a single node as a DOT statement."""
    escaped = node.label.replace('"', '\\"')
    return f'  {_quote_id(node.node_id)} [label="{escaped}"];'


def format_edge(edge: Edge) -> str:
    """Format a single edge as a DOT statement."""
    return f"  {_quote_id(edge.source)} -> {_quote_id(edge.target)};"


def figure_number_to_graph_name(number: str) -> str:
    """Convert a figure number like '4-1' to a graph name like 'Figure_4_1'."""
    return "Figure_" + number.replace("-", "_")


def generate_dot(figure: Figure) -> str:
    """Generate complete DOT digraph source for a figure."""
    lines: list[str] = []
    lines.append(f"digraph {figure.graph_name} {{")
    lines.append("  rankdir=TB;")
    if figure.nodes:
        lines.append("")
        for node in figure.nodes:
            lines.append(format_node(node))
    if figure.edges:
        lines.append("")
        for edge in figure.edges:
            lines.append(format_edge(edge))
    lines.append("}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# PDF extraction
# ---------------------------------------------------------------------------

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


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

_CLAUSE_RE = re.compile(
    r"^([1-9][0-9]*|[A-Z])"  # V: positive non-zero integer or uppercase letter
    r"(\.[0-9]+){0,4}$"      # optional .W, .W.X, .W.X.Y, .W.X.Y.Z
)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse and validate command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Convert figures from the IEEE 1800-2023 "
        "SystemVerilog LRM.",
    )
    parser.add_argument(
        "--lrm",
        type=Path,
        required=True,
        help="Path to the IEEE 1800-2023 SystemVerilog LRM.",
    )
    parser.add_argument(
        "--clause",
        required=True,
        help="LRM clause (e.g. 6, 6.3, 6.3.1, A, A.1.2).",
    )
    args = parser.parse_args(argv)
    if not args.lrm.is_file():
        parser.error(f"LRM file not found: {args.lrm}")
    if not _CLAUSE_RE.match(args.clause):
        parser.error(
            f"Invalid clause '{args.clause}'. "
            "Expected V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z "
            "where V is a positive non-zero number or uppercase "
            "letter."
        )
    return args


def _run(lrm_path: Path, clause: str) -> None:
    """Open the LRM, extract figures for clause, print DOT to stdout."""
    doc = open_document(lrm_path)
    pages = find_clause_pages(doc, clause)
    if not pages:
        print(f"ERROR: No pages found for clause {clause}.", file=sys.stderr)
        sys.exit(1)
    captions = find_figure_captions(doc, pages, clause)
    if not captions:
        print(
            f"ERROR: No figures found for clause {clause}.",
            file=sys.stderr,
        )
        sys.exit(1)
    for page_idx, fig_num, fig_title, caption_y in captions:
        page = doc[page_idx]
        figure = extract_figure(
            page=page,
            figure_number=fig_num,
            figure_title=fig_title,
            caption_y=caption_y,
        )
        print(generate_dot(figure), end="")


def main(argv: list[str] | None = None) -> None:
    """Entry point: parse args, extract figures, emit DOT."""
    args = parse_args(argv)
    _run(args.lrm, args.clause)
