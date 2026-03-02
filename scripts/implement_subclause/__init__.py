"""LRM subclause implementation prompt generator.

Dispatches to depth-appropriate prompt builders and invokes Claude CLI.
"""

import argparse
import functools
import os
import re
import subprocess
import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")
FIGURE_LABEL_RE = re.compile(r"^Figure ([\d\w]+-[\d\w]+)")
TABLE_LABEL_RE = re.compile(r"^Table ([\d\w]+-[\d\w]+)")


# ---------------------------------------------------------------------------
# LRM title extraction
# ---------------------------------------------------------------------------

def load_lrm_titles(lrm_path: Path) -> dict[str, str]:
    """Build clause -> title map from an LRM text file.

    Handles three formats:
    - Subclauses: "4.1 General" or "A.8.1 Concatenations"
    - Top-level numeric: "4. Scheduling semantics"
    - Annex headers (multi-line): "Annex B\\n(normative)\\n\\nKeywords"
    """
    if not lrm_path.exists():
        return {}

    titles = {}
    lines = lrm_path.read_text(encoding="utf-8").splitlines()

    for i, line in enumerate(lines):
        # Subclauses: "4.1 General", "A.8.1 Concatenations"
        m = re.match(r"^(\d+(?:\.\d+)+)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
            continue
        m = re.match(r"^([A-Z]\.\d+(?:\.\d+)*)\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
            continue

        # Top-level numeric: "4. Scheduling semantics"
        m = re.match(r"^(\d+)\.\s+(.+)$", line)
        if m:
            titles[m.group(1)] = m.group(2).strip()
            continue

        # Annex headers (multi-line):
        #   Annex B
        #   (normative)
        #
        #   Keywords
        m = re.match(r"^Annex\s+([A-Z])$", line)
        if m:
            letter = m.group(1)
            normative = ""
            title = ""
            # Look ahead for (normative)/(informative) and title
            for j in range(i + 1, min(i + 6, len(lines))):
                nxt = lines[j].strip()
                if not nxt:
                    continue
                nm = re.match(r"^\((normative|informative)\)$", nxt)
                if nm:
                    normative = f"({nm.group(1)})"
                    continue
                # First non-empty, non-normative line is the title
                title = nxt
                break
            if normative and title:
                titles[letter] = f"{normative} {title}"
            elif title:
                titles[letter] = title

    return titles


# ---------------------------------------------------------------------------
# Hierarchy computation
# ---------------------------------------------------------------------------

def build_hierarchy(clause: str) -> dict:
    """Derive template variables from a clause string.

    Returns a dict with keys:
    - is_annex, subclause (always present)
    - Numeric: clause_number, principle (depth >= 3), ancestors
    - Annex: collection, letter, principles (depth >= 2), ancestors
    """
    parts = clause.split(".")
    is_annex = parts[0][0].isalpha() and parts[0][0].isupper()
    depth = len(parts)

    result = {"is_annex": is_annex, "subclause": clause}

    if is_annex:
        letter = parts[0]
        result["collection"] = f"Annex {letter}"
        result["letter"] = letter
        if depth >= 2:
            result["principles"] = f"{letter}.{parts[1]}"
        # Ancestors: intermediate levels between principles (V.W) and
        # subclause. For depth 3 (A.8.1), no ancestors. For depth 4
        # (A.7.5.3), ancestors = [A.7.5].
        ancestors = []
        for k in range(3, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors
    else:
        result["clause_number"] = parts[0]
        if depth >= 3:
            result["principle"] = f"{parts[0]}.1"
        # Ancestors: intermediate levels between principle (V.1) and
        # subclause. For depth 3 (6.24.1), ancestors = [6.24]. For
        # depth 4 (4.4.3.1), ancestors = [4.4, 4.4.3].
        ancestors = []
        for k in range(2, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors

    return result


def build_top_level_line(h: dict, titles: dict[str, str], lrm: str) -> str:
    """Return the first hierarchy line for the top-level clause or annex."""
    if h["is_annex"]:
        subject = titles.get(h["letter"], "")
        return (
            f"- Thoroughly understand that {h['collection']}"
            f" is about '{subject}' per LRM in {lrm}"
        )
    title = titles.get(h["clause_number"], "")
    return (
        f"- Thoroughly understand that Clause {h['clause_number']}"
        f" is about '{title}' per LRM in {lrm}"
    )


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


def _lrm_labels_for_clause(
    lrm_path: Path, clause: str,
) -> tuple[list[str], list[str]]:
    """Parse the LRM to find figure/table labels for a clause's top-level."""
    top = clause.split(".")[0]
    prefix_fig = f"Figure {top}-"
    prefix_tbl = f"Table {top}-"
    figures: list[str] = []
    tables: list[str] = []

    text = lrm_path.read_text(errors="replace")
    for line in text.splitlines():
        m = FIGURE_LABEL_RE.match(line)
        if m and line.startswith(prefix_fig):
            figures.append(m.group(1))
            continue
        m = TABLE_LABEL_RE.match(line)
        if m and line.startswith(prefix_tbl):
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

    lrm_figs, lrm_tbls = _lrm_labels_for_clause(lrm_path, clause)

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
    """Build prompt lines acknowledging available Figures/Tables."""
    if not figures and not tables:
        return ""
    lines: list[str] = []
    for path in figures:
        label = _label_from_gv(path)
        lines.append(
            f"- Acknowledge that you know {label} is available"
            f" at {path} as a DOT GraphViz"
        )
    for path in tables:
        label = _label_from_md(path)
        lines.append(
            f"- Acknowledge that you know {label} is available"
            f" at {path} as a Markdown file"
        )
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Prompt formatting
# ---------------------------------------------------------------------------

def format_prompt(
    hierarchy: str,
    subclause: str,
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Assemble the standard implementation prompt from hierarchy steps."""
    return (
        "Create and execute a Claude task list."
        " Each task must be blocked by the preceding task.\n\n"
        f"{hierarchy}"
        f"{supplementary}"
        f"- Implement ALL aspects (not just parsing) of"
        f" {subclause} per LRM in {lrm}"
        f" through test-driven development unit tests\n"
        f"- Prove that the unit tests cover ALL aspects of"
        f" {subclause} per LRM in {lrm} not just parsing\n"
        f"- Prove that the implementation covers ALL aspects of"
        f" {subclause} per LRM in {lrm} not just parsing\n"
        f"- Read all of Issue {issue}\n"
        f"- Correct Issue {issue}\n"
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

    print(f"Invoking Claude ({model})...", file=sys.stderr)
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
    print(
        f"Loaded {len(titles)} LRM clause titles from {lrm_path}",
        file=sys.stderr,
    )
    prompt = build_fn(clause, titles, str(lrm_path), issue=issue)
    print(f"Built prompt ({len(prompt)} characters)", file=sys.stderr)
    invoke_claude(prompt, model=model)


# ---------------------------------------------------------------------------
# Prompt builders (depth 1-5)
# ---------------------------------------------------------------------------

def _build_hierarchy_steps(h: dict, titles: dict, lrm: str) -> str:
    """Build the 'Thoroughly understand' hierarchy lines for depth 4+."""
    lines = [build_top_level_line(h, titles, lrm)]

    root = h["principles"] if h["is_annex"] else h["principle"]
    lines.append(
        f"- Thoroughly understand {root}"
        f" per LRM in {lrm}",
    )
    parent = root
    for ancestor in h["ancestors"]:
        lines.append(
            f"- Thoroughly understand {ancestor}"
            f" and how it fits within {parent}"
            f" per LRM in {lrm}",
        )
        parent = ancestor
    lines.append(
        f"- Thoroughly understand {h['subclause']}"
        f" and how it fits within {parent}"
        f" per LRM in {lrm}",
    )

    return "\n".join(lines) + "\n"


def build_prompt_v(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-1 clause."""
    h = build_hierarchy(clause)
    top = build_top_level_line(h, titles, lrm)
    hierarchy = f"{top}\n"
    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)


def build_prompt_v_w(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-2 clause."""
    h = build_hierarchy(clause)
    top = build_top_level_line(h, titles, lrm)
    hierarchy = (
        f"{top}\n"
        f"- Thoroughly understand {h['subclause']}"
        f" per LRM in {lrm}\n"
    )
    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)


def build_prompt_v_w_x(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-3 clause."""
    h = build_hierarchy(clause)
    top = build_top_level_line(h, titles, lrm)

    if h["is_annex"]:
        hierarchy = (
            f"{top}\n"
            f"- Thoroughly understand {h['principles']}"
            f" per LRM in {lrm}\n"
            f"- Thoroughly understand {h['subclause']}"
            f" and how it fits within {h['principles']}"
            f" per LRM in {lrm}\n"
        )
    else:
        hierarchy = (
            f"{top}\n"
            f"- Thoroughly understand {h['principle']}"
            f" per LRM in {lrm}\n"
            f"- Thoroughly understand {h['subclause']}"
            f" and how it fits within {h['ancestors'][0]}"
            f" per LRM in {lrm}\n"
        )

    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)


def build_prompt_v_w_x_y(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-4 clause."""
    h = build_hierarchy(clause)
    hierarchy = _build_hierarchy_steps(h, titles, lrm)
    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)


def build_prompt_v_w_x_y_z(
    clause: str,
    titles: dict[str, str],
    lrm: str,
    *,
    issue: int,
    supplementary: str = "",
) -> str:
    """Build the implementation prompt for a depth-5 clause."""
    h = build_hierarchy(clause)
    hierarchy = _build_hierarchy_steps(h, titles, lrm)
    return format_prompt(hierarchy, h["subclause"], lrm, issue=issue, supplementary=supplementary)


# ---------------------------------------------------------------------------
# CLI dispatch
# ---------------------------------------------------------------------------

_HANDLERS = {
    1: build_prompt_v,
    2: build_prompt_v_w,
    3: build_prompt_v_w_x,
    4: build_prompt_v_w_x_y,
    5: build_prompt_v_w_x_y_z,
}


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
        "--clause",
        type=str,
        required=True,
        help="LRM clause number (V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z).",
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

    if not CLAUSE_RE.match(args.clause):
        parser.error(
            f"Invalid clause format '{args.clause}'. "
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
    """Parse args, dispatch to the depth-appropriate prompt, and invoke Claude."""
    args = parse_args(argv)
    depth = clause_depth(args.clause)
    handler = _HANDLERS[depth]
    print(
        f"Clause {args.clause} (depth {depth}),"
        f" issue #{args.issue}, model {args.model}",
        file=sys.stderr,
    )

    check_supplementary_args(
        args.clause, args.lrm,
        figures=args.figures,
        tables=args.tables,
        ignore_figures=args.ignore_figures,
    )

    supplementary = build_supplementary_lines(
        figures=args.figures, tables=args.tables,
    )
    if supplementary:
        n_supp = supplementary.count("\n") + 1
        print(
            f"Found {n_supp} supplementary files",
            file=sys.stderr,
        )
        supplementary += "\n"

    bound_handler = functools.partial(handler, supplementary=supplementary)
    run_prompt(
        bound_handler, args.lrm, args.clause,
        issue=args.issue, model=args.model,
    )
