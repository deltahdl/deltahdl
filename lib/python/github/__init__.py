"""Shared GitHub issue utilities."""

import json
import re
import subprocess
import sys
from typing import Any

from lib.python.retry import (
    DEFAULT_MAX_ATTEMPTS,
    contains_transient_marker,
    sleep_before_retry,
)


_EOF_WORD_RE = re.compile(r"\beof\b")
_HTTP_5XX_RE = re.compile(r"\bhttp 5\d\d\b")
_TRANSIENT_SUBSTRINGS = (
    "i/o timeout",
    "dial tcp",
    "connection refused",
    "connection reset",
    "secondary rate limit",
    "bad gateway",
    "service unavailable",
    "gateway timeout",
    "temporary failure in name resolution",
)


def _is_transient(returncode: int, stderr: str) -> bool:
    """Classify a ``gh`` failure as a transport-layer transient error.

    Returns ``True`` only for errors worth retrying (network timeouts,
    5xx, secondary rate limits, DNS flakes). Logic errors (4xx, auth,
    validation) return ``False`` so the caller fails fast.
    """
    if returncode == 0:
        return False
    if contains_transient_marker(stderr, _TRANSIENT_SUBSTRINGS):
        return True
    lower = stderr.lower()
    if _EOF_WORD_RE.search(lower):
        return True
    if _HTTP_5XX_RE.search(lower):
        return True
    return False


def _run_gh(
    cmd: list[str], *, stdin_text: str | None = None,
) -> subprocess.CompletedProcess[str]:
    """Run a ``gh`` command with bounded exponential-backoff retries.

    Transient transport failures (see :func:`_is_transient`) are retried
    up to ``DEFAULT_MAX_ATTEMPTS`` total attempts with full-jitter
    exponential backoff (see :func:`lib.python.retry.sleep_before_retry`).
    Permanent failures and successes return immediately. The returned
    ``CompletedProcess`` lets the caller keep its existing returncode
    inspection and ``sys.exit(1)`` branch.
    """
    last = subprocess.run(
        cmd, input=stdin_text, capture_output=True, text=True, check=False,
    )
    for attempt in range(DEFAULT_MAX_ATTEMPTS - 1):
        if not _is_transient(last.returncode, last.stderr):
            return last
        sleep_before_retry(attempt)
        last = subprocess.run(
            cmd, input=stdin_text, capture_output=True, text=True, check=False,
        )
    return last


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


def _gh_api_jq(
    organization: str, repo: str, issue: int, *, jq: str, label: str,
) -> str:
    """Run ``gh api repos/.../issues/{issue} --jq <expr>`` and return stdout.

    Exits with a templated error message on non-zero gh exit. Returns
    the raw stdout — callers strip if their field is a single-line
    scalar.
    """
    result = _run_gh(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "--jq", jq],
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to fetch {label} for issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    return result.stdout


def fetch_issue_body(organization: str, repo: str, issue: int) -> str:
    """Fetch the body of a GitHub issue using ``gh api``."""
    print(f"Fetching issue #{issue} from {organization}/{repo}...")
    return _gh_api_jq(organization, repo, issue, jq=".body", label="body")


_SUBCLAUSE_RE = re.compile(
    r"§(\d+(?:\.\d+)*)"
    r"|(\b[A-Z](?:\.\d+)+)"
    r"|\bAnnex\s+([A-Z])\b"
)


def extract_subclause_from_title(title: str) -> str:
    """Extract the subclause number from an issue title.

    Handles ``§3.1`` numeric, ``A.1`` annex-subclause, and bare
    ``Annex B`` (top-level annex, no numbered subclause) formats.
    """
    m = _SUBCLAUSE_RE.search(title)
    if not m:
        return ""
    return m.group(1) or m.group(2) or m.group(3)


def fetch_issue_title(organization: str, repo: str, issue: int) -> str:
    """Fetch the title of a GitHub issue using ``gh api``."""
    print(f"Fetching title for issue #{issue} from {organization}/{repo}...")
    return _gh_api_jq(
        organization, repo, issue, jq=".title", label="title",
    ).strip()


def fetch_issue_state(organization: str, repo: str, issue: int) -> str:
    """Fetch the state of a GitHub issue using ``gh api``."""
    return _gh_api_jq(
        organization, repo, issue, jq=".state", label="state",
    ).strip()


def find_issue_by_title(
    organization: str, repo: str, title: str,
) -> int | None:
    """Find an open issue by exact title. Returns number or None."""
    result = _run_gh(
        ["gh", "issue", "list", "--repo", f"{organization}/{repo}",
         "--search", f'"{title}" in:title', "--state", "open",
         "--json", "number,title", "--limit", "10"],
    )
    if result.returncode != 0:
        return None
    for issue in json.loads(result.stdout):
        if issue["title"] == title:
            number: int = issue["number"]
            return number
    return None


def create_issue(
    organization: str, repo: str, title: str, body: str,
    *, labels: list[str] | None = None,
) -> int:
    """Create a GitHub issue and return its number."""
    print(f"Creating issue on {organization}/{repo}...")
    data: dict[str, object] = {"title": title, "body": body}
    if labels is not None:
        data["labels"] = labels
    payload = json.dumps(data)
    result = _run_gh(
        ["gh", "api", f"repos/{organization}/{repo}/issues",
         "-X", "POST", "--input", "-"],
        stdin_text=payload,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to create issue:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    issue_number: int = json.loads(result.stdout)["number"]
    print(f"Created issue #{issue_number}")
    return issue_number


def add_labels(
    organization: str, repo: str, issue: int, labels: list[str],
) -> None:
    """Add labels to a GitHub issue using ``gh api``."""
    print(f"Adding labels to issue #{issue} on {organization}/{repo}...")
    payload = json.dumps({"labels": labels})
    result = _run_gh(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}/labels",
         "-X", "POST", "--input", "-"],
        stdin_text=payload,
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to add labels to issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)


def update_issue_body(
    organization: str, repo: str, issue: int, body: str,
) -> None:
    """Update the body of a GitHub issue using ``gh api``."""
    print(f"Updating issue #{issue} on {organization}/{repo}...")
    payload = json.dumps({"body": body})
    result = _run_gh(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "-X", "PATCH", "--input", "-"],
        stdin_text=payload,
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
    result = _run_gh(
        ["gh", "api", f"repos/{organization}/{repo}/issues/{issue}",
         "-X", "PATCH", "-f", "state=closed"],
    )
    if result.returncode != 0:
        print(f"ERROR: Failed to close issue #{issue}:"
              f"\n{result.stderr}", file=sys.stderr)
        sys.exit(1)
    print(f"Closed issue #{issue}.")


def delete_issue(issue: int) -> None:
    """Delete a GitHub issue using ``gh issue delete``."""
    print(f"Deleting issue #{issue}...")
    result = _run_gh(
        ["gh", "issue", "delete", str(issue), "--yes"],
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


# ---------------------------------------------------------------------------
# Subclause-issue find-or-create
# ---------------------------------------------------------------------------
#
# Consumed by multiple satisfaction scripts (satisfy_subclause,
# satisfy_clause, satisfy_subclauses), so the find-or-create surface
# lives here rather than inside any one script.


def issue_title_for(subclause: str) -> str:
    """Return the canonical GitHub issue title for *subclause*."""
    return f"Satisfy IEEE 1800-2023 §{subclause}"


def _ensure_audit_title(subclause_marker: str) -> str:
    """Return the ``Ensure IEEE 1800-2023 …`` audit title for the given marker."""
    return (
        f"Ensure IEEE 1800-2023 {subclause_marker} functionalities and tests"
        " are implemented and properly named"
    )


def legacy_issue_title_for(subclause: str) -> str:
    """Return the legacy audit-style ``Ensure …`` title (numeric-form, with §)."""
    return _ensure_audit_title(f"§{subclause}")


def _legacy_audit_annex_title_for(subclause: str) -> str:
    """Return the legacy audit-style ``Ensure …`` title (annex-form, no §)."""
    return _ensure_audit_title(subclause)


def _title_matches(title: str, subclause: str) -> bool:
    """Return True if *title* matches any recognised shape for *subclause*."""
    master_prefix = f"Implement IEEE 1800-2023 §{subclause}"
    if title in {
        issue_title_for(subclause),
        f"Satisfy §{subclause}",
        legacy_issue_title_for(subclause),
        _legacy_audit_annex_title_for(subclause),
        master_prefix,
    }:
        return True
    return title.startswith(master_prefix + " ")


def parse_issue_number_from_create_output(output: str) -> int:
    """Extract the issue number from a ``gh issue create`` URL."""
    url = output.strip().splitlines()[-1].strip()
    return int(url.rsplit("/", 1)[-1])


def _list_issues_for(subclause: str) -> list[dict[str, Any]]:
    """Return the gh-issue-list payload for *subclause* (loud-fatal on error).

    ``gh issue list`` defaults to 30 results. A heavily-subdivided clause
    (e.g. §23 with §23.x.y.z descendants) easily exceeds that, pushing
    the master-list issue past the cutoff so the matcher can't see it
    and silently opens a duplicate. Raise the limit well above any
    realistic per-clause result count.
    """
    completed = _run_gh(
        [
            "gh", "issue", "list",
            "--state", "all",
            "--search", f"§{subclause}",
            "--json", "number,title,state",
            "--limit", "1000",
        ],
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    return json.loads(completed.stdout) if completed.stdout.strip() else []


def _label_create_args(labels: list[str]) -> list[str]:
    """Return ``["--label", L1, "--label", L2, …]`` for ``gh issue create``."""
    args: list[str] = []
    for label in labels:
        args.extend(["--label", label])
    return args


def _create_new_issue(subclause: str, labels: list[str]) -> int:
    """Create a fresh issue for *subclause* and return its number."""
    completed = _run_gh(
        [
            "gh", "issue", "create",
            "--title", issue_title_for(subclause),
            *_label_create_args(labels),
            "--body", (
                f"Track satisfying §{subclause} via the satisfaction"
                " pipeline (#1265)."
            ),
        ],
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    return parse_issue_number_from_create_output(completed.stdout)


def _apply_labels(number: int, labels: list[str]) -> None:
    """Add *labels* to issue *number*.

    ``gh issue edit --add-label`` accepts a comma-separated list and is
    idempotent, so this is safe to call on issues that already carry
    any of the labels.
    """
    _run_gh(
        [
            "gh", "issue", "edit", str(number),
            "--add-label", ",".join(labels),
        ],
    )


def find_or_create_issue(
    subclause: str, *, labels: list[str],
) -> tuple[int, str]:
    """Return ``(issue_number, state)`` for *subclause*.

    ``state`` is ``"OPEN"`` or ``"CLOSED"``. Callers decide what to do
    with a closed match — typically loud-skip; the historical
    automatic ``gh issue reopen`` is gone because the silent reopen
    was a source of accidental reruns over already-satisfied
    subclauses.

    Searches for any pre-existing issue whose title matches one of the
    recognised shapes — current canonical (``Satisfy IEEE 1800-2023
    §X``), deprecated short canonical (``Satisfy §X``), legacy audit
    forms (``Ensure IEEE 1800-2023 [§]X functionalities …``), or
    master-list form (``Implement IEEE 1800-2023 §X …``) — and reuses
    it. When multiple matches exist (e.g. a master-list issue plus a
    recently-created duplicate), the issue with the smallest number is
    retained and the others are hard-deleted via ``gh issue delete
    --yes``. The retained issue is renamed to the new canonical (and
    any descriptive trailing text from the master-list form is
    dropped) and tagged with every label in *labels*. Creates a fresh
    issue (carrying the same labels) when no match exists.
    """
    matches = [
        entry for entry in _list_issues_for(subclause)
        if _title_matches(entry.get("title", "") or "", subclause)
    ]
    if not matches:
        return _create_new_issue(subclause, labels), "OPEN"

    matches.sort(key=lambda entry: int(entry["number"]))
    oldest, *duplicates = matches
    for dup_entry in duplicates:
        _run_gh(
            [
                "gh", "issue", "delete",
                str(int(dup_entry["number"])), "--yes",
            ],
        )

    number = int(oldest["number"])
    canonical = issue_title_for(subclause)
    if oldest.get("title") != canonical:
        _run_gh(
            ["gh", "issue", "edit", str(number), "--title", canonical],
        )
    state = oldest.get("state", "OPEN").upper()
    _apply_labels(number, labels)
    return number, state
