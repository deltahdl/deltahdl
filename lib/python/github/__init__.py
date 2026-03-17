"""Shared GitHub issue utilities."""

import json
import re
import subprocess
import sys


def format_subclause_label(subclause: str) -> str:
    """Return display label: ``§X.Y`` for numeric, ``X.Y`` for annexes."""
    if subclause[0].isalpha():
        return subclause
    return f"§{subclause}"


def build_subclause_table(items: dict[str, str]) -> str:
    """Build a 4-column markdown table for subclauses.

    All rows start as ``Unreviewed`` with an empty action.
    """
    header = (
        "| Label | Title | Status | Action |\n"
        "|-------|-------|--------|--------|\n"
    )
    rows = "\n".join(
        f"| {format_subclause_label(k)} | {v} | Unreviewed | |"
        for k, v in items.items()
    )
    return header + rows + "\n"


_SUBCLAUSE_ROW_RE = re.compile(
    r"^\| ([^|]+) \| ([^|]+) \| ([^|]+) \|([^|]*)\|$",
    re.MULTILINE,
)


def parse_subclause_rows(body: str) -> dict[str, tuple[str, str, str]]:
    """Parse subclause table rows into ``{label: (title, status, action)}``."""
    rows: dict[str, tuple[str, str, str]] = {}
    for m in _SUBCLAUSE_ROW_RE.finditer(body):
        label = m.group(1).strip()
        if label == "Label":
            continue
        title = m.group(2).strip()
        status = m.group(3).strip()
        action = m.group(4).strip()
        rows[label] = (title, status, action)
    return rows


def sync_subclause_table(body: str, items: dict[str, str]) -> str:
    """Rebuild the subclause table, preserving existing statuses."""
    existing = parse_subclause_rows(body)
    rows = []
    for subclause, title in items.items():
        label = format_subclause_label(subclause)
        if label in existing:
            _, status, action = existing[label]
            action_cell = f" {action} " if action else " "
            rows.append(f"| {label} | {title} | {status} |{action_cell}|")
        else:
            rows.append(f"| {label} | {title} | Unreviewed | |")
    header = (
        "| Label | Title | Status | Action |\n"
        "|-------|-------|--------|--------|\n"
    )
    return header + "\n".join(rows) + "\n"


def update_subclause_status(body: str, label: str, status: str, *,
                            action: str = "",
                            commit_url: str = "") -> str:
    """Update the Status and Action columns for *label* in the table."""
    row_re = re.compile(
        r"^(\| " + re.escape(label) + r" \|[^|]*)\|[^|]*\|[^|]*\|$",
        re.MULTILINE,
    )
    match = row_re.search(body)
    if not match:
        print(f"ERROR: Row for {label!r} not found in issue body",
              file=sys.stderr)
        sys.exit(1)
    if action and commit_url:
        action_text = f"[{action}]({commit_url})"
    else:
        action_text = action
    action_cell = f" {action_text} " if action_text else " "
    new_row = f"{match.group(1)}| {status} |{action_cell}|"
    return body[:match.start()] + new_row + body[match.end():]


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


_SUBCLAUSE_RE = re.compile(r"§(\d+(?:\.\d+)*)|(\b[A-Z](?:\.\d+)+)")


def extract_subclause_from_title(title: str) -> str:
    """Extract the subclause number from an issue title.

    Handles both ``§3.1`` and ``A.1`` formats.
    """
    m = _SUBCLAUSE_RE.search(title)
    if not m:
        return ""
    return m.group(1) or m.group(2)


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


def fetch_issue_state(organization: str, repo: str, issue: int) -> str:
    """Fetch the state of a GitHub issue using ``gh api``."""
    result = subprocess.run(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "--jq", ".state"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to fetch state for issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    return result.stdout.strip()


def find_issue_by_title(
    organization: str, repo: str, title: str,
) -> int | None:
    """Find an open issue by exact title. Returns number or None."""
    result = subprocess.run(
        ["gh", "issue", "list", "--repo", f"{organization}/{repo}",
         "--search", f'"{title}" in:title', "--state", "open",
         "--json", "number,title", "--limit", "10"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        return None
    for issue in json.loads(result.stdout):
        if issue["title"] == title:
            return issue["number"]
    return None


def create_issue(
    organization: str, repo: str, title: str, body: str,
) -> int:
    """Create a GitHub issue and return its number."""
    print(f"Creating issue on {organization}/{repo}...")
    payload = json.dumps({"title": title, "body": body})
    result = subprocess.run(
        ["gh", "api", f"repos/{organization}/{repo}/issues",
         "-X", "POST", "--input", "-"],
        input=payload,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to create issue:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    issue_number = json.loads(result.stdout)["number"]
    print(f"Created issue #{issue_number}")
    return issue_number


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


def delete_issue(issue: int) -> None:
    """Delete a GitHub issue using ``gh issue delete``."""
    print(f"Deleting issue #{issue}...")
    result = subprocess.run(
        ["gh", "issue", "delete", str(issue), "--yes"],
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to delete issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    print(f"Deleted issue #{issue}.")


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
