#!/usr/bin/env python3
"""LRM clause implementation prompt generator.

Dispatches to depth-appropriate prompt builders and invokes Claude CLI.
"""

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

_GDRIVE = Path(
    "/Users/jdrowne/Library/CloudStorage/"
    "GoogleDrive-jdrowne@10ulabs.com/Shared drives/"
    "10U Labs Shared Drive/Standards/SystemVerilog"
)
FIGURES_DIR = _GDRIVE / "Figures"
TABLES_DIR = _GDRIVE / "Tables"

CLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")


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

def find_supplementary_files(clause: str) -> list[tuple[str, Path]]:
    """Find converted Figure/Table files for the clause's top-level component.

    Returns (human_label, path) pairs for files that exist on disk.
    """
    top = clause.split(".")[0]
    results = []

    if FIGURES_DIR.is_dir():
        for path in sorted(FIGURES_DIR.glob(f"Figure_{top}_*.gv")):
            # Figure_4_1.gv -> "Figure 4-1"
            stem = path.stem  # "Figure_4_1"
            label = stem.replace("_", " ", 1).replace("_", "-")
            results.append((label, path))

    if TABLES_DIR.is_dir():
        for path in sorted(TABLES_DIR.glob(f"TABLE_{top}_*.md")):
            # TABLE_B_1.md -> "Table B-1"
            stem = path.stem  # "TABLE_B_1"
            raw = stem[len("TABLE_"):]  # "B_1"
            label = f"Table {raw.replace('_', '-')}"
            results.append((label, path))

    return results


def build_supplementary_lines(clause: str) -> str:
    """Build prompt lines acknowledging available Figures/Tables."""
    files = find_supplementary_files(clause)
    if not files:
        return ""
    lines = []
    for label, path in files:
        if path.suffix == ".gv":
            fmt = "a DOT GraphViz"
        elif path.suffix == ".md":
            fmt = "a Markdown file"
        else:
            fmt = "a file"
        lines.append(
            f"- Acknowledge that you know {label} is available"
            f" at {path} as {fmt}"
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
    supplementary = build_supplementary_lines(clause)
    if supplementary:
        n_supp = supplementary.count("\n") + 1
        print(
            f"Found {n_supp} supplementary files",
            file=sys.stderr,
        )
        supplementary += "\n"
    prompt = build_fn(
        clause, titles, str(lrm_path),
        issue=issue, supplementary=supplementary,
    )
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
    args = parser.parse_args(argv)

    if not args.lrm.is_file():
        parser.error(f"LRM file not found: {args.lrm}")

    if not CLAUSE_RE.match(args.clause):
        parser.error(
            f"Invalid clause format '{args.clause}'. "
            "Expected V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z "
            "(V is a number or uppercase letter; remaining parts are numbers)."
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

    run_prompt(
        handler, args.lrm, args.clause,
        issue=args.issue, model=args.model,
    )


if __name__ == "__main__":
    main()
