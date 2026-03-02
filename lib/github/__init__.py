"""Shared GitHub issue utilities."""

import json
import re
import subprocess
import sys


def fetch_issue_body(organization: str, repo: str, issue: int) -> str:
    """Fetch the body of a GitHub issue using ``gh api``."""
    print(
        f"Fetching issue #{issue} from {organization}/{repo}...",
        file=sys.stderr,
    )
    result = subprocess.run(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "--jq", ".body"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to fetch issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    return result.stdout


def update_issue_body(
    organization: str, repo: str, issue: int, body: str,
) -> None:
    """Update the body of a GitHub issue using ``gh api``."""
    print(
        f"Updating issue #{issue} on {organization}/{repo}...",
        file=sys.stderr,
    )
    payload = json.dumps({"body": body})
    result = subprocess.run(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "-X", "PATCH", "--input", "-"],
        input=payload,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to update issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)


def build_synced_body(body: str, items: dict[str, str]) -> str:
    """Return issue body with subclauses checklist synced to *items*."""
    checked = {
        m.group(1)
        for m in re.finditer(r"^- \[x\] (\S+) ", body, re.MULTILINE)
    }
    lines = []
    for number, title in items.items():
        state = "x" if number in checked else " "
        lines.append(f"- [{state}] {number} {title}")
    return "## Subclauses\n\n" + "\n".join(lines) + "\n"


def sync_checklist(
    organization: str, repo: str, issue: int, items: dict[str, str],
) -> None:
    """Fetch, sync, and update the subclauses checklist on an issue."""
    body = fetch_issue_body(organization, repo, issue)
    new_body = build_synced_body(body, items)
    update_issue_body(organization, repo, issue, new_body)


def next_unchecked(body: str) -> str | None:
    """Return the first unchecked subclause number, or ``None``."""
    m = re.search(r"^- \[ \] (\S+) ", body, re.MULTILINE)
    return m.group(1) if m else None
