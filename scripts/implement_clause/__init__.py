"""LRM clause implementation orchestrator.

Discovers subclauses via Claude, syncs a GitHub issue checklist,
and invokes implement_subclause.
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
    close_issue,
    fetch_issue_body,
    next_unchecked,
    update_issue_body,
)


def discover_subclauses(
    lrm_path: Path, clause: str, *, model: str = "sonnet",
) -> dict[str, str]:
    """Discover implementable subclauses by asking Claude.

    Returns a dict of ``{subclause_number: title}`` for subclauses
    that Claude determines are implementable as software.
    """
    print(f"Discovering subclauses for clause {clause} via Claude ({model})...")
    prompt = (
        f"Read clause {clause} in the LRM at {lrm_path}. "
        "List all direct and indirect subclauses. For each, determine "
        "whether it describes functionality that can be implemented as "
        "software (e.g., parsing, simulation, synthesis, elaboration, "
        "scheduling).\n\n"
        "Return ONLY a JSON object where each key is a subclause "
        "number and each value is one of:\n"
        "- A string containing the subclause title if the subclause "
        "is implementable\n"
        "- false if it is not implementable\n\n"
        'Example: {"4.1": "General", "4.2": "Overview", "4.3": false}'
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

    implementable: dict[str, str] = {}
    for key, value in verdicts.items():
        if isinstance(value, str):
            implementable[key] = value
        elif value is True:
            implementable[key] = key

    print(f"Implementable: {list(implementable.keys())}")
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


def mark_master_complete(
    organization: str, repo: str, master_issue: int,
    sub_issue: int,
) -> None:
    """Mark a sub-issue's row as complete on the master issue table."""
    body = fetch_issue_body(organization, repo, master_issue)
    pattern = re.compile(
        r"^(\|[^|]+\|[^|]+\| #" + str(sub_issue) + r" \|)\s*[^|]*\|",
        re.MULTILINE,
    )
    new_body, count = pattern.subn(r"\1 :white_check_mark: |", body)
    if count == 0:
        print(f"WARNING: No table row found for #{sub_issue}"
              f" on issue #{master_issue}.", file=sys.stderr)
        return
    update_issue_body(organization, repo, master_issue, new_body)
    print(f"Marked #{sub_issue} complete on master issue #{master_issue}.")


def invoke_implement_subclause(
    args: argparse.Namespace,
    subclause: str,
    *,
    continue_session: bool = False,
) -> None:
    """Shell out to ``python -m implement_subclause``."""
    print(f"Invoking implement_subclause for {subclause}...")
    cmd = [
        sys.executable, "-m", "implement_subclause",
        "--lrm", args.lrm,
        "--subclause", subclause,
        "--issue", str(args.sub_issue),
    ]
    if continue_session:
        cmd.append("--continue")
    result = subprocess.run(cmd, check=False)
    if result.returncode != 0:
        sys.exit(result.returncode)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments for implement_clause."""
    parser = argparse.ArgumentParser(
        description="Orchestrate LRM clause implementation.",
    )
    parser.add_argument("--lrm", required=True, help="Path to LRM PDF")
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--clause", help="Numeric clause (e.g. 4)")
    group.add_argument("--annex", help="Annex letter (e.g. A)")
    parser.add_argument("--sub-issue", type=int, required=True)
    parser.add_argument("--master-issue", type=int, required=True)
    parser.add_argument("--organization", required=True)
    parser.add_argument("--repo", required=True)

    args = parser.parse_args(argv)

    lrm = Path(args.lrm)
    if not lrm.exists():
        parser.error(f"LRM file not found: {args.lrm}")

    return args


def _run_subclause_loop(
    args: argparse.Namespace,
    impl_items: dict[str, str],
) -> None:
    """Sync the issue checklist and implement subclauses one at a time."""
    first = True
    while True:
        body = fetch_issue_body(args.organization, args.repo, args.sub_issue)
        new_body = build_synced_body(body, impl_items)
        print(f"Synced issue body:\n{new_body}")
        update_issue_body(
            args.organization, args.repo, args.sub_issue, new_body,
        )

        subclause = next_unchecked(new_body)
        if subclause is None:
            print("All subclauses are done.")
            close_issue(
                args.organization, args.repo, args.sub_issue,
                "all subclauses are implemented",
            )
            mark_master_complete(
                args.organization, args.repo,
                args.master_issue, args.sub_issue,
            )
            return

        print(f"Next unchecked: {subclause}")
        invoke_implement_subclause(
            args, subclause, continue_session=not first,
        )
        commit_and_push(subclause)
        first = False


def main(argv: list[str] | None = None) -> None:
    """Orchestrate implementation of an LRM clause."""
    args = parse_args(argv)
    clause = args.clause or args.annex
    lrm = Path(args.lrm)

    impl_items = discover_subclauses(lrm, clause)

    if not impl_items:
        print(f"No subclauses for {clause}; invoking directly.")
        invoke_implement_subclause(args, clause)
        close_issue(
            args.organization, args.repo, args.sub_issue,
            "all subclauses are implemented",
        )
        mark_master_complete(
            args.organization, args.repo,
            args.master_issue, args.sub_issue,
        )
        return

    print(f"Found {len(impl_items)} subclauses for {clause}.")
    _run_subclause_loop(args, impl_items)
