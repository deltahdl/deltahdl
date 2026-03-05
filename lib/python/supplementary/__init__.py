"""Shared figure/table supplementary-file helpers."""

import sys
from pathlib import Path


def label_from_gv(path: Path) -> str:
    """Figure_4_1.gv -> 'Figure 4-1'."""
    return path.stem.replace("_", " ", 1).replace("_", "-")


def label_from_md(path: Path) -> str:
    """TABLE_B_1.md -> 'Table B-1'."""
    raw = path.stem[len("TABLE_"):]
    return f"Table {raw.replace('_', '-')}"


def shorthand_from_label(label: str) -> str:
    """'Figure 4-1' -> '4-1', 'Table B-1' -> 'B-1'."""
    return label.split(" ", 1)[1]


def check_supplementary_args(
    clause: str,
    lrm_labels: tuple[list[str], list[str]],
    *,
    figures: list[Path],
    tables: list[Path],
    ignore_figures: list[str],
) -> list[str]:
    """Validate that all required figures/tables are provided.

    *lrm_labels* is ``(figure_shorthands, table_shorthands)`` as
    returned by the caller's LRM-label lookup function.

    Returns the combined list of figure + table labels.
    Raises ``SystemExit`` if any are missing or paths don't exist.
    """
    errors: list[str] = []

    for path in figures:
        if not path.is_file():
            errors.append(f"--figures path does not exist: {path}")
    for path in tables:
        if not path.is_file():
            errors.append(f"--tables path does not exist: {path}")

    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)

    lrm_figs, lrm_tbls = lrm_labels

    provided_fig_shorthands = {
        shorthand_from_label(label_from_gv(p)) for p in figures
    }
    ignored = set(ignore_figures)

    for label in lrm_figs:
        if label not in provided_fig_shorthands and label not in ignored:
            errors.append(
                f"Figure {label} required for clause {clause}"
                f" (use --figures or --ignore-figures {label})",
            )

    provided_tbl_shorthands = {
        shorthand_from_label(label_from_md(p)) for p in tables
    }

    for label in lrm_tbls:
        if label not in provided_tbl_shorthands:
            errors.append(
                f"Table {label} required for clause {clause}"
                f" (use --tables)",
            )

    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)

    return lrm_figs + lrm_tbls


def build_supplementary_lines(
    *, figures: list[Path], tables: list[Path],
) -> str:
    """Build prompt lines referencing available Figures/Tables."""
    if not figures and not tables:
        return ""
    lines: list[str] = []
    for path in figures:
        label = label_from_gv(path)
        lines.append(
            f"Consult {label} at {path} (DOT GraphViz)"
            f" when implementing.",
        )
    for path in tables:
        label = label_from_md(path)
        lines.append(
            f"Consult {label} at {path} (Markdown)"
            f" when implementing.",
        )
    return "\n".join(lines)


def add_supplementary_args(parser) -> None:
    """Add --figures, --tables, and --ignore-figures to *parser*."""
    parser.add_argument(
        "--figures", type=str, default="",
        help="Comma-separated list of .gv figure files.",
    )
    parser.add_argument(
        "--tables", type=str, default="",
        help="Comma-separated list of .md table files.",
    )
    parser.add_argument(
        "--ignore-figures", type=str, default="",
        help="Comma-separated shorthand labels to skip.",
    )


def parse_supplementary_csv_args(args) -> None:
    """Parse comma-separated --figures/--tables/--ignore-figures into lists."""
    args.figures = (
        [Path(p.strip()) for p in args.figures.split(",") if p.strip()]
        if args.figures else []
    )
    args.tables = (
        [Path(p.strip()) for p in args.tables.split(",") if p.strip()]
        if args.tables else []
    )
    args.ignore_figures = (
        [s.strip() for s in args.ignore_figures.split(",") if s.strip()]
        if args.ignore_figures else []
    )
