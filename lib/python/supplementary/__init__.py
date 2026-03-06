"""Shared figure/table supplementary-file helpers."""

import sys
from pathlib import Path


def check_supplementary_args(
    clause: str,
    lrm_labels: tuple[list[str], list[str]],
    *,
    figures: dict[str, Path],
    tables: dict[str, Path],
    ignore_figures: list[str],
) -> list[str]:
    """Validate that all required figures/tables are provided.

    *lrm_labels* is ``(figure_shorthands, table_shorthands)`` as
    returned by the caller's LRM-label lookup function.

    *figures* and *tables* are dicts mapping shorthand (e.g. ``"4-1"``)
    to a file path.

    Returns the combined list of figure + table labels.
    Raises ``SystemExit`` if any are missing or paths don't exist.
    """
    errors: list[str] = []

    for path in figures.values():
        if not path.is_file():
            errors.append(f"--figures path does not exist: {path}")
    for path in tables.values():
        if not path.is_file():
            errors.append(f"--tables path does not exist: {path}")

    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)

    lrm_figs, lrm_tbls = lrm_labels

    ignored = set(ignore_figures)

    for label in lrm_figs:
        if label not in figures and label not in ignored:
            errors.append(
                f"Figure {label} required for clause {clause}"
                f" (use --figures or --ignore-figures {label})",
            )

    for label in lrm_tbls:
        if label not in tables:
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
    *, figures: dict[str, Path], tables: dict[str, Path],
) -> str:
    """Build prompt lines referencing available Figures/Tables."""
    if not figures and not tables:
        return ""
    lines: list[str] = []
    for key, path in figures.items():
        lines.append(
            f"Consult Figure {key} at {path} (DOT GraphViz)"
            f" when implementing.",
        )
    for key, path in tables.items():
        lines.append(
            f"Consult Table {key} at {path} (Markdown)"
            f" when implementing.",
        )
    return "\n".join(lines)


def add_supplementary_args(parser) -> None:
    """Add --figures, --tables, and --ignore-figures to *parser*."""
    parser.add_argument(
        "--figures", type=str, default="",
        help="Comma-separated key=path pairs (e.g. 4_1=fig.gv).",
    )
    parser.add_argument(
        "--tables", type=str, default="",
        help="Comma-separated key=path pairs (e.g. 22_1=tbl.md).",
    )
    parser.add_argument(
        "--ignore-figures", type=str, default="",
        help="Comma-separated shorthand labels to skip.",
    )


def parse_supplementary_csv_args(args) -> None:
    """Parse key=path --figures/--tables and CSV --ignore-figures."""
    args.figures = _parse_key_path_csv(args.figures)
    args.tables = _parse_key_path_csv(args.tables)
    args.ignore_figures = (
        [s.strip() for s in args.ignore_figures.split(",") if s.strip()]
        if args.ignore_figures else []
    )


def _parse_key_path_csv(raw: str) -> dict[str, Path]:
    """Parse 'key=path,key=path' into {shorthand: Path}.

    Annex keys (starting with an uppercase letter) use dot separators
    (e.g. ``B_1`` → ``B.1``).  Numeric keys use dashes
    (e.g. ``4_1`` → ``4-1``).
    """
    if not raw:
        return {}
    result: dict[str, Path] = {}
    for item in raw.split(","):
        item = item.strip()
        if not item:
            continue
        key, path = item.split("=", 1)
        key = key.strip()
        sep = "." if key[0].isalpha() else "-"
        shorthand = key.replace("_", sep)
        result[shorthand] = Path(path.strip())
    return result
