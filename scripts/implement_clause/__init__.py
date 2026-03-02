"""LRM clause implementation orchestrator.

Discovers subclauses, filters for implementability via Claude,
syncs a GitHub issue checklist, and invokes implement_subclause.
"""

import argparse
import json
import os
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
        file=sys.stderr,
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

    implementable = json.loads(result.stdout.strip())
    print(f"Implementable: {implementable}", file=sys.stderr)
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
    print(
        f"Invoking implement_subclause for {subclause}...",
        file=sys.stderr,
    )
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

    args = parser.parse_args(argv)

    lrm = Path(args.lrm)
    if not lrm.exists():
        parser.error(f"LRM file not found: {args.lrm}")

    return args


def main(argv: list[str] | None = None) -> None:
    """Orchestrate implementation of an LRM clause."""
    args = parse_args(argv)
    clause = args.clause or args.annex
    lrm = Path(args.lrm)

    subclauses = parse_subclauses(lrm, clause)

    if not subclauses:
        print(
            f"No subclauses for {clause}; invoking directly.",
            file=sys.stderr,
        )
        invoke_implement_subclause(
            lrm=args.lrm, subclause=clause,
            issue=args.issue, organization=args.organization,
            repo=args.repo,
        )
        return

    print(
        f"Found {len(subclauses)} subclauses for {clause}.",
        file=sys.stderr,
    )

    clause_text = extract_clause_text(lrm, clause)
    implementable = filter_implementable(clause_text, subclauses)
    impl_items = {k: subclauses[k] for k in implementable}

    body = fetch_issue_body(args.organization, args.repo, args.issue)
    new_body = build_synced_body(body, impl_items)
    update_issue_body(args.organization, args.repo, args.issue, new_body)

    subclause = next_unchecked(new_body)
    if subclause is None:
        print("All subclauses are done.", file=sys.stderr)
        return

    print(f"Next unchecked: {subclause}", file=sys.stderr)
    invoke_implement_subclause(
        lrm=args.lrm, subclause=subclause,
        issue=args.issue, organization=args.organization,
        repo=args.repo,
    )
