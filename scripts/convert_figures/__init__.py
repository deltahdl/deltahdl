"""Convert figures from the IEEE 1800-2023 SystemVerilog LRM to DOT."""

import argparse
import re
import sys
from pathlib import Path

from convert_figures import _pdf
from convert_figures._dot import generate_dot

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
    doc = _pdf.open_document(lrm_path)
    pages = _pdf.find_clause_pages(doc, clause)
    if not pages:
        print(f"ERROR: No pages found for clause {clause}.", file=sys.stderr)
        sys.exit(1)
    captions = _pdf.find_figure_captions(doc, pages, clause)
    if not captions:
        print(
            f"ERROR: No figures found for clause {clause}.",
            file=sys.stderr,
        )
        sys.exit(1)
    for page_idx, fig_num, fig_title, caption_y in captions:
        page = doc[page_idx]
        figure = _pdf.extract_figure(
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
