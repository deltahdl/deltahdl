"""LRM clause implementation orchestrator.

Discovers subclauses via Claude, syncs a GitHub issue checklist,
and invokes implement_subclauses.
"""

import argparse
import json
import os
import re
import subprocess
import time
import sys
from pathlib import Path

from lib.python.cli import (
    add_continue_arg,
    add_labels_arg,
    invoke_implement_subclauses,
    run_claude_cli,
    run_with_dots,
)
from lib.python.github import (
    close_issue,
    create_issue,
    extract_subclause_from_title,
    fetch_issue_body,
    fetch_issue_title,
    find_issue_by_title,
    format_subclause_label,
    update_issue_body,
)


def discover_subclauses(
    lrm_path: Path, clause: str, *, model: str = "opus",
) -> dict[str, str]:
    """Discover implementable subclauses by asking Claude.

    Returns a dict of ``{subclause_number: title}`` for subclauses
    that Claude determines are implementable as software.
    """
    label = format_subclause_label(clause)
    prompt = (
        f"Read {label} in the LRM at {lrm_path}. "
        "List ALL subclauses at EVERY depth level. For each subclause "
        "that has its own numbered subsections, list those too.\n\n"
        "Return ONLY a JSON object where each key is a subclause "
        "number and each value is the subclause title.\n\n"
        'Example: {"4.1": "General", "4.2": "Overview", "4.3": "Event simulation"}'
    )

    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    print(
        f"Discovering subclauses for {label}"
        f" via Claude ({model})...",
        end="", flush=True,
    )

    cmd = ["claude", "-p", "--model", model, "--effort", "high",
           "--dangerously-skip-permissions"]
    result = run_with_dots(run_claude_cli, cmd, prompt, env=env)
    if result.returncode != 0:
        print(
            f"ERROR: Claude failed:\n{result.stderr}",
            file=sys.stderr,
        )
        sys.exit(1)

    raw = result.stdout.strip()
    print(f"Claude response:\n{raw}")
    fenced = re.search(r"```(?:json)?\s*\n(.*?)\n```", raw, re.DOTALL)
    if fenced:
        raw = fenced.group(1)
    subclauses = json.loads(raw)
    subclauses.pop(clause, None)
    print(f"Subclauses: {list(subclauses.keys())}")
    return subclauses


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments for implement_clause."""
    parser = argparse.ArgumentParser(
        description="Orchestrate LRM clause implementation.",
    )
    parser.add_argument("--lrm", required=True, help="Path to LRM PDF")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--clause", help="Numeric clause (e.g. 4)")
    group.add_argument("--annex", help="Annex letter (e.g. A)")
    parser.add_argument("--issue", type=int, default=None,
                        help="Existing clause issue number (created if absent)")
    parser.add_argument("--organization", required=True)
    parser.add_argument("--repo", required=True)
    add_labels_arg(parser)
    add_continue_arg(parser)

    args = parser.parse_args(argv)

    lrm = Path(args.lrm)
    if not lrm.exists():
        parser.error(f"LRM file not found: {args.lrm}")

    return args


def _parse_issue_refs(body: str) -> list[int]:
    """Extract issue numbers from ``- #N`` lines in the body."""
    return [int(m.group(1)) for m in re.finditer(r"^- #(\d+)", body, re.MULTILINE)]


def _ensure_subclause_issues(
    organization, repo, discovered, existing_issues,
    *, labels=None,
):
    """Create missing subclause issues, return the full issue list."""
    covered = set()
    for issue_num in existing_issues:
        title = fetch_issue_title(organization, repo, issue_num)
        sc = extract_subclause_from_title(title)
        if sc:
            covered.add(sc)

    all_issues = list(existing_issues)
    for subclause in discovered:
        if subclause not in covered:
            label = format_subclause_label(subclause)
            title = _issue_title(label)
            existing = find_issue_by_title(organization, repo, title)
            if existing:
                all_issues.append(existing)
            else:
                issue_num = create_issue(
                    organization, repo, title, "",
                    labels=labels,
                )
                all_issues.append(issue_num)
                time.sleep(5)
    return all_issues


def _issue_title(label: str) -> str:
    """Build the issue title for a clause or subclause."""
    return (
        f"Ensure IEEE 1800-2023 {label}"
        " functionalities and tests are implemented and properly named"
    )


def main(argv: list[str] | None = None) -> None:
    """Orchestrate implementation of an LRM clause."""
    args = parse_args(argv)
    clause = args.clause or args.annex
    lrm = Path(args.lrm)

    if args.issue is None:
        clause_label = format_subclause_label(clause)
        args.issue = create_issue(
            args.organization, args.repo,
            _issue_title(clause_label), "",
            labels=args.labels,
        )

    discovered = discover_subclauses(lrm, clause)
    if not discovered:
        print(
            f"ERROR: discovery returned no subclauses for {clause}.",
            file=sys.stderr,
        )
        sys.exit(1)

    print(f"Found {len(discovered)} subclauses for {clause}.")

    body = fetch_issue_body(args.organization, args.repo, args.issue)
    existing = _parse_issue_refs(body)

    subclause_issues = _ensure_subclause_issues(
        args.organization, args.repo, discovered, existing,
        labels=args.labels,
    )

    body = "\n".join(f"- #{n}" for n in subclause_issues) + "\n"
    update_issue_body(args.organization, args.repo, args.issue, body)

    invoke_implement_subclauses(
        str(lrm), subclause_issues,
        organization=args.organization, repo=args.repo,
        continue_session=args.continue_session,
    )

    close_issue(
        args.organization, args.repo, args.issue,
        "all subclauses implemented",
    )
