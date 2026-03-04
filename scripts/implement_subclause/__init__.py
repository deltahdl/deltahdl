"""LRM subclause implementation prompt generator.

Builds an optimized prompt and invokes Claude CLI.
"""

import argparse
import functools
import os
import re
import subprocess
import sys
from pathlib import Path

from lib.lrm import extract_clause_text, load_lrm_titles


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")
FIGURE_LABEL_RE = re.compile(r"^Figure ([\d\w]+-[\d\w]+)")
TABLE_LABEL_RE = re.compile(r"^Table ([\d\w]+-[\d\w]+)")


# ---------------------------------------------------------------------------
# Hierarchy computation
# ---------------------------------------------------------------------------

def build_hierarchy(clause: str) -> dict:
    """Derive template variables from a clause string.

    Returns a dict with keys:
    - is_annex, subclause (always present)
    - Numeric: clause_number, ancestors
    - Annex: collection, letter, ancestors
    """
    parts = clause.split(".")
    is_annex = parts[0][0].isalpha() and parts[0][0].isupper()
    depth = len(parts)

    result = {"is_annex": is_annex, "subclause": clause}

    if is_annex:
        letter = parts[0]
        result["collection"] = f"Annex {letter}"
        result["letter"] = letter
        ancestors = []
        for k in range(2, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors
    else:
        result["clause_number"] = parts[0]
        ancestors = []
        for k in range(2, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors

    return result


def find_context_subclauses(
    clause: str, titles: dict[str, str],
) -> list[str]:
    """Find subclauses titled 'General' or 'Overview' at each ancestry level.

    Scans sibling subclauses at each level between the top-level clause
    and the target, returning those titled exactly 'General' or 'Overview'.
    Excludes the target itself.
    """
    parts = clause.split(".")
    context: list[str] = []

    for level in range(1, len(parts)):
        prefix = ".".join(parts[:level]) + "."
        target_depth = level + 1
        for key, title in sorted(titles.items()):
            if (
                key.startswith(prefix)
                and key.count(".") == prefix.count(".")
                and len(key.split(".")) == target_depth
                and title in ("General", "Overview")
                and key != clause
            ):
                context.append(key)

    return context


# ---------------------------------------------------------------------------
# Supplementary files (Figures / Tables)
# ---------------------------------------------------------------------------

def _label_from_gv(path: Path) -> str:
    """Figure_4_1.gv -> 'Figure 4-1'."""
    return path.stem.replace("_", " ", 1).replace("_", "-")


def _label_from_md(path: Path) -> str:
    """TABLE_B_1.md -> 'Table B-1'."""
    raw = path.stem[len("TABLE_"):]
    return f"Table {raw.replace('_', '-')}"


def _shorthand_from_label(label: str) -> str:
    """'Figure 4-1' -> '4-1', 'Table B-1' -> 'B-1'."""
    return label.split(" ", 1)[1]


def _lrm_labels_for_subclause(
    lrm_path: Path, clause: str,
) -> tuple[list[str], list[str]]:
    """Parse the LRM to find figure/table labels within *clause*'s text."""
    text = extract_clause_text(lrm_path, clause)
    figures: list[str] = []
    tables: list[str] = []

    for line in text.splitlines():
        m = FIGURE_LABEL_RE.match(line)
        if m:
            figures.append(m.group(1))
            continue
        m = TABLE_LABEL_RE.match(line)
        if m:
            tables.append(m.group(1))

    return figures, tables


def check_supplementary_args(
    clause: str,
    lrm_path: Path,
    *,
    figures: list[Path],
    tables: list[Path],
    ignore_figures: list[str],
) -> None:
    """Validate that all required figures/tables are provided.

    Exits with an error if any are missing or paths don't exist.
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

    lrm_figs, lrm_tbls = _lrm_labels_for_subclause(lrm_path, clause)

    provided_fig_shorthands = {
        _shorthand_from_label(_label_from_gv(p)) for p in figures
    }
    ignored = set(ignore_figures)

    for label in lrm_figs:
        if label not in provided_fig_shorthands and label not in ignored:
            errors.append(
                f"Figure {label} required for clause {clause}"
                f" (use --figures or --ignore-figures {label})"
            )

    provided_tbl_shorthands = {
        _shorthand_from_label(_label_from_md(p)) for p in tables
    }

    for label in lrm_tbls:
        if label not in provided_tbl_shorthands:
            errors.append(
                f"Table {label} required for clause {clause}"
                f" (use --tables)"
            )

    if errors:
        for e in errors:
            print(f"ERROR: {e}", file=sys.stderr)
        sys.exit(1)


def build_supplementary_lines(
    *, figures: list[Path], tables: list[Path],
) -> str:
    """Build prompt lines referencing available Figures/Tables."""
    if not figures and not tables:
        return ""
    lines: list[str] = []
    for path in figures:
        label = _label_from_gv(path)
        lines.append(
            f"Consult {label} at {path} (DOT GraphViz)"
            f" when implementing."
        )
    for path in tables:
        label = _label_from_md(path)
        lines.append(
            f"Consult {label} at {path} (Markdown)"
            f" when implementing."
        )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Prompt formatting
# ---------------------------------------------------------------------------

def _build_context_list(
    clause: str, titles: dict[str, str],
) -> list[str]:
    """Build the list of related LRM subclauses to read for context.

    Collects General/Overview siblings at each ancestry level and
    intermediate ancestors — all deduplicated.
    """
    h = build_hierarchy(clause)
    context: list[str] = []

    # Context subclauses (General/Overview siblings), deduped vs ancestors
    ancestor_set = set(h["ancestors"])
    for ctx in find_context_subclauses(clause, titles):
        if ctx not in ancestor_set:
            context.append(ctx)

    # Intermediate ancestors
    context.extend(h["ancestors"])

    return context


def format_prompt(
    subclause: str,
    lrm: str,
    context: list[str],
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Assemble the implementation prompt from structured inputs."""
    lines = [f"Implement §{subclause} from the LRM at {lrm}.\n"]

    if context:
        refs = ", ".join(f"§{s}" for s in context)
        lines.append(
            f"Read §{subclause} and related subclauses"
            f" ({refs}) for context.",
        )
    else:
        lines.append(f"Read §{subclause} for context.")

    lines.append(
        "Search the codebase for existing related code"
        " before writing anything new.",
    )

    if supplementary:
        lines.append(supplementary.rstrip("\n"))

    lines.append(
        "Use strict test-driven development:"
        f" for each requirement in §{subclause},"
        " write a failing unit test, then implement."
        " Cover all affected pipeline stages."
        " Include error conditions and edge cases.",
    )

    lines.append("Do not copy LRM prose into source comments.")

    lines.append(
        f"After implementation, mark §{subclause}"
        f" complete in Issue #{issue}.",
    )

    return "\n".join(lines) + "\n"


def build_prompt(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for any clause depth."""
    context = _build_context_list(clause, titles)
    return format_prompt(
        clause, lrm, context,
        issue=issue, supplementary=supplementary,
    )


# ---------------------------------------------------------------------------
# Claude CLI invocation
# ---------------------------------------------------------------------------

def invoke_claude(prompt: str, *, model: str = "sonnet") -> None:
    """Launch Claude CLI in print mode with the implementation prompt.

    Streams stdout/stderr to the terminal in real time.
    """
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    cmd = [
        "claude", "-p",
        "--model", model,
        "--dangerously-skip-permissions",
    ]

    print(f"Invoking Claude ({model})...")
    with subprocess.Popen(
        cmd,
        stdin=subprocess.PIPE,
        stdout=sys.stdout,
        stderr=sys.stderr,
        text=True,
        env=env,
    ) as proc:
        proc.communicate(input=prompt)

    if proc.returncode != 0:
        print(
            f"\nERROR: Claude exited with code {proc.returncode}",
            file=sys.stderr,
        )
        sys.exit(1)


def run_prompt(
    build_fn, lrm_path: Path, clause: str, *,
    issue: int, model: str,
) -> None:
    """Load titles, build a prompt via *build_fn*, and invoke Claude."""
    titles = load_lrm_titles(lrm_path)
    print(f"Loaded {len(titles)} LRM clause titles from {lrm_path}")
    prompt = build_fn(clause, titles, str(lrm_path), issue=issue)
    print(f"Built prompt ({len(prompt)} characters)")
    invoke_claude(prompt, model=model)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args(argv=None):
    """Parse command-line arguments for clause implementation."""
    parser = argparse.ArgumentParser(
        description="Generate an implementation prompt for a given LRM clause.",
    )
    parser.add_argument(
        "--lrm",
        type=Path,
        required=True,
        help="Path to the LRM text file.",
    )
    parser.add_argument(
        "--subclause",
        type=str,
        required=True,
        help="LRM subclause number (V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z).",
    )
    parser.add_argument(
        "--issue",
        type=int,
        required=True,
        help="GitHub Issue number to read and correct after implementation.",
    )
    parser.add_argument(
        "--model",
        type=str,
        default="opus",
        help="Claude model to use (default: opus).",
    )
    parser.add_argument(
        "--figures",
        type=str,
        default="",
        help="Comma-separated list of .gv figure files.",
    )
    parser.add_argument(
        "--tables",
        type=str,
        default="",
        help="Comma-separated list of .md table files.",
    )
    parser.add_argument(
        "--ignore-figures",
        type=str,
        default="",
        help="Comma-separated shorthand labels (e.g. 4-1,16-5) to skip.",
    )
    args = parser.parse_args(argv)

    if not args.lrm.is_file():
        parser.error(f"LRM file not found: {args.lrm}")

    if not CLAUSE_RE.match(args.subclause):
        parser.error(
            f"Invalid subclause format '{args.subclause}'. "
            "Expected V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z "
            "(V is a number or uppercase letter; remaining parts are numbers)."
        )

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

    return args


def clause_depth(clause: str) -> int:
    """Return the nesting depth of a clause string."""
    return clause.count(".") + 1


def main(argv=None):
    """Parse args, build prompt, and invoke Claude."""
    args = parse_args(argv)
    depth = clause_depth(args.subclause)
    print(
        f"Clause {args.subclause} (depth {depth}),"
        f" issue #{args.issue}, model {args.model}",
    )

    check_supplementary_args(
        args.subclause, args.lrm,
        figures=args.figures,
        tables=args.tables,
        ignore_figures=args.ignore_figures,
    )

    supplementary = build_supplementary_lines(
        figures=args.figures, tables=args.tables,
    )
    if supplementary:
        n_supp = supplementary.count("\n") + 1
        print(f"Found {n_supp} supplementary files")

    bound_handler = functools.partial(
        build_prompt, supplementary=supplementary,
    )
    run_prompt(
        bound_handler, args.lrm, args.subclause,
        issue=args.issue, model=args.model,
    )
