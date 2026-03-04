"""LRM clause implementation orchestrator.

Discovers subclauses, filters for implementability via Claude,
syncs a GitHub issue checklist, and invokes implement_subclause.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path

from lib.github import (
    build_synced_body,
    fetch_issue_body,
    next_unchecked,
    update_issue_body,
)
from lib.lrm import extract_clause_text, parse_subclauses


FIGURE_LABEL_RE = re.compile(r"^Figure ([\d\w]+-[\d\w]+)")
TABLE_LABEL_RE = re.compile(r"^Table ([\d\w]+-[\d\w]+)")


def _lrm_labels_for_clause(
    lrm_path: Path, clause: str,
) -> tuple[list[str], list[str]]:
    """Find all figure/table labels for a top-level clause in the LRM."""
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


def check_supplementary_args(
    clause: str,
    lrm_path: Path,
    *,
    figures: list[Path],
    tables: list[Path],
    ignore_figures: list[str],
) -> None:
    """Validate that all clause-level figures/tables are provided."""
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


def filter_implementable(
    clause_text: str,
    subclauses: dict[str, str],
    *,
    model: str = "sonnet",
) -> list[str]:
    """Return subclause numbers that are implementable as software."""
    print(
        f"Filtering {len(subclauses)} subclauses"
        f" for implementability via Claude ({model})...",
    )
    numbered = "\n".join(
        f"- {k}: {v}" for k, v in subclauses.items()
    )
    prompt = (
        "You are evaluating subclauses of the IEEE SystemVerilog "
        "Language Reference Manual. Determine which of the following "
        "subclauses describe functionality that can be implemented as "
        "software (e.g., parsing, simulation, synthesis, elaboration, "
        "scheduling).\n\n"
        f"Clause text:\n{clause_text}\n\n"
        f"Subclauses:\n{numbered}\n\n"
        "Return ONLY a JSON array of the implementable subclause "
        'numbers. Example: ["4.2", "4.3"]'
    )

    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    result = subprocess.run(
        ["claude", "-p", "--model", model],
        input=prompt,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    if result.returncode != 0:
        print(
            f"ERROR: Claude failed:\n{result.stderr}",
            file=sys.stderr,
        )
        sys.exit(1)

    print(f"Claude response:\n{result.stdout.strip()}")
    implementable = json.loads(result.stdout.strip())
    print(f"Implementable: {implementable}")
    return implementable


def invoke_implement_subclause(
    *,
    lrm: str,
    subclause: str,
    issue: int,
    organization: str,
    repo: str,
) -> None:
    """Shell out to ``python -m implement_subclause``."""
    print(f"Invoking implement_subclause for {subclause}...")
    result = subprocess.run(
        [
            sys.executable, "-m", "implement_subclause",
            "--lrm", lrm,
            "--subclause", subclause,
            "--issue", str(issue),
            "--organization", organization,
            "--repo", repo,
        ],
        check=False,
    )
    if result.returncode != 0:
        sys.exit(result.returncode)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments for implement_clause."""
    parser = argparse.ArgumentParser(
        description="Orchestrate LRM clause implementation.",
    )
    parser.add_argument("--lrm", required=True, help="Path to LRM text")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--clause", help="Numeric clause (e.g. 4)")
    group.add_argument("--annex", help="Annex letter (e.g. A)")
    parser.add_argument("--issue", type=int, required=True)
    parser.add_argument("--organization", required=True)
    parser.add_argument("--repo", required=True)
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

    args = parser.parse_args(argv)

    lrm = Path(args.lrm)
    if not lrm.exists():
        parser.error(f"LRM file not found: {args.lrm}")

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


def main(argv: list[str] | None = None) -> None:
    """Orchestrate implementation of an LRM clause."""
    args = parse_args(argv)
    clause = args.clause or args.annex
    lrm = Path(args.lrm)

    subclauses = parse_subclauses(lrm, clause)

    if not subclauses:
        print(f"No subclauses for {clause}; invoking directly.")
        invoke_implement_subclause(
            lrm=args.lrm, subclause=clause,
            issue=args.issue, organization=args.organization,
            repo=args.repo,
        )
        return

    print(f"Found {len(subclauses)} subclauses for {clause}.")

    clause_text = extract_clause_text(lrm, clause)
    implementable = filter_implementable(clause_text, subclauses)
    impl_items = {k: subclauses[k] for k in implementable}

    body = fetch_issue_body(args.organization, args.repo, args.issue)
    new_body = build_synced_body(body, impl_items)
    print(f"Synced issue body:\n{new_body}")
    update_issue_body(args.organization, args.repo, args.issue, new_body)

    subclause = next_unchecked(new_body)
    if subclause is None:
        print("All subclauses are done.")
        return

    print(f"Next unchecked: {subclause}")
    invoke_implement_subclause(
        lrm=args.lrm, subclause=subclause,
        issue=args.issue, organization=args.organization,
        repo=args.repo,
    )
