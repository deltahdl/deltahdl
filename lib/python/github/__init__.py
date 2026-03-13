"""Shared GitHub issue utilities."""

import json
import re
import subprocess
import sys


def fetch_issue_body(organization: str, repo: str, issue: int) -> str:
    """Fetch the body of a GitHub issue using ``gh api``."""
    print(f"Fetching issue #{issue} from {organization}/{repo}...")
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


def fetch_issue_title(organization: str, repo: str, issue: int) -> str:
    """Fetch the title of a GitHub issue using ``gh api``."""
    print(f"Fetching title for issue #{issue} from {organization}/{repo}...")
    result = subprocess.run(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "--jq", ".title"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to fetch issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    return result.stdout.strip()


def update_issue_body(
    organization: str, repo: str, issue: int, body: str,
) -> None:
    """Update the body of a GitHub issue using ``gh api``."""
    print(f"Updating issue #{issue} on {organization}/{repo}...")
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


def close_issue(
    organization: str, repo: str, issue: int, reason: str,
) -> None:
    """Close a GitHub issue using ``gh api``."""
    print(f"Closing issue #{issue} because {reason}...")
    result = subprocess.run(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "-X", "PATCH", "-f", "state=closed"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to close issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    print(f"Closed issue #{issue}.")


def build_synced_body(body: str, items: dict[str, str]) -> str:
    """Return issue body with subclauses checklist synced to *items*."""
    checked = {
        m.group(1)
        for m in re.finditer(r"^\s*- \[x\] (\S+) ", body, re.MULTILINE)
    }
    min_depth = min(k.count(".") for k in items)
    lines = []
    for number, title in items.items():
        state = "x" if number in checked else " "
        indent = "  " * (number.count(".") - min_depth)
        lines.append(f"{indent}- [{state}] {number} {title}")
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
    m = re.search(r"^\s*- \[ \] (\S+) ", body, re.MULTILINE)
    return m.group(1) if m else None


def remove_test_row(body: str, test_name: str) -> str:
    """Remove the table row for *test_name* from *body*."""
    row_re = re.compile(
        r"^\|[^|]*\| " + re.escape(test_name) + r" \|[^|]*\|[^|]*\|\n?",
        re.MULTILINE,
    )
    match = row_re.search(body)
    if not match:
        raise ValueError(
            f"Row for {test_name!r} not found in issue body",
        )
    return body[:match.start()] + body[match.end():]


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
