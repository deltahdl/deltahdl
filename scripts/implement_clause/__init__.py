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

from lib.python.github import (
    build_synced_body,
    fetch_issue_body,
    next_unchecked,
    update_issue_body,
)
from lib.python.lrm import extract_clause_text, parse_subclauses
from lib.python.supplementary import (
    add_supplementary_args,
    check_supplementary_args,
    parse_supplementary_csv_args,
)


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
        "Return ONLY a JSON object where each key is a subclause "
        "number and each value is one of:\n"
        "- true if the subclause is implementable\n"
        "- false if it is not implementable\n"
        "- For subclauses titled 'General' or 'Overview', you MUST "
        "provide a string rationale explaining why it is implementable, "
        "or false to exclude it.\n\n"
        'Example: {"4.1": "Defines syntax rules that must be parsed", '
        '"4.2": true, "4.3": false}'
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

    raw = result.stdout.strip()
    print(f"Claude response:\n{raw}")
    raw = re.sub(r"^```(?:json)?\s*\n?", "", raw)
    raw = re.sub(r"\n?```\s*$", "", raw)
    verdicts = json.loads(raw)

    implementable: list[str] = []
    for key, value in verdicts.items():
        if isinstance(value, str):
            print(f"Rationale for {key}: {value}")
            implementable.append(key)
        elif value:
            implementable.append(key)

    print(f"Implementable: {implementable}")
    return implementable


def commit_and_push(subclause: str) -> None:
    """Stage all changes, commit with subclause reference, and push."""
    subprocess.run(["git", "add", "-A"], check=True)
    result = subprocess.run(
        ["git", "diff", "--cached", "--quiet"], check=False,
    )
    if result.returncode == 0:
        print(f"No changes to commit for §{subclause}.")
        return
    msg = (
        f"Implement §{subclause}\n\n"
        "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
    )
    subprocess.run(["git", "commit", "-m", msg], check=True)
    subprocess.run(["git", "push"], check=True)
    print(f"Committed and pushed §{subclause}.")


def _lrm_labels_for_subclause(
    lrm_path: Path, clause: str,
) -> tuple[list[str], list[str]]:
    """Find figure/table labels within a subclause's LRM text."""
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


def _format_key_path_csv(mapping: dict[str, Path]) -> str:
    """Format a dict as 'key=path,key=path' for CLI forwarding."""
    return ",".join(
        f"{k.replace('-', '_')}={v}" for k, v in mapping.items()
    )


def invoke_implement_subclause(
    args: argparse.Namespace,
    subclause: str,
    *,
    continue_session: bool = False,
    figures: dict[str, Path] | None = None,
    tables: dict[str, Path] | None = None,
) -> None:
    """Shell out to ``python -m implement_subclause``."""
    print(f"Invoking implement_subclause for {subclause}...")
    cmd = [
        sys.executable, "-m", "implement_subclause",
        "--lrm", args.lrm,
        "--subclause", subclause,
        "--issue", str(args.issue),
    ]
    if continue_session:
        cmd.append("--continue")
    if figures:
        cmd.extend(["--figures", _format_key_path_csv(figures)])
    if tables:
        cmd.extend(["--tables", _format_key_path_csv(tables)])
    result = subprocess.run(cmd, check=False)
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
    add_supplementary_args(parser)

    args = parser.parse_args(argv)

    lrm = Path(args.lrm)
    if not lrm.exists():
        parser.error(f"LRM file not found: {args.lrm}")

    parse_supplementary_csv_args(args)

    return args


def main(argv: list[str] | None = None) -> None:
    """Orchestrate implementation of an LRM clause."""
    args = parse_args(argv)
    clause = args.clause or args.annex
    lrm = Path(args.lrm)

    lrm_labels = _lrm_labels_for_clause(lrm, clause)
    check_supplementary_args(
        clause, lrm_labels,
        figures=args.figures,
        tables=args.tables,
        ignore_figures=args.ignore_figures,
    )

    subclauses = parse_subclauses(lrm, clause)

    if not subclauses:
        print(f"No subclauses for {clause}; invoking directly.")
        invoke_implement_subclause(args, clause)
        return

    print(f"Found {len(subclauses)} subclauses for {clause}.")

    clause_text = extract_clause_text(lrm, clause)
    implementable = filter_implementable(clause_text, subclauses)
    impl_items = {k: subclauses[k] for k in implementable}

    first = True
    while True:
        body = fetch_issue_body(args.organization, args.repo, args.issue)
        new_body = build_synced_body(body, impl_items)
        print(f"Synced issue body:\n{new_body}")
        update_issue_body(
            args.organization, args.repo, args.issue, new_body,
        )

        subclause = next_unchecked(new_body)
        if subclause is None:
            print("All subclauses are done.")
            return

        print(f"Next unchecked: {subclause}")
        sub_figs, sub_tbls = _lrm_labels_for_subclause(lrm, subclause)
        sub_figures = {k: v for k, v in args.figures.items() if k in sub_figs}
        sub_tables = {k: v for k, v in args.tables.items() if k in sub_tbls}
        invoke_implement_subclause(
            args, subclause, continue_session=not first,
            figures=sub_figures, tables=sub_tables,
        )
        commit_and_push(subclause)
        first = False
