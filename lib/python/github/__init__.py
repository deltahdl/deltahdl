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
    if subclause[0].isalpha():
        return subclause
    return f"§{subclause}"


def issue_title_for(subclause: str) -> str:
    return f"Satisfy IEEE 1800-2023 §{subclause}"


def _issue_list(selectors: list[str]) -> list[dict[str, Any]]:
    completed = _run_gh(["gh", "issue", "list", *selectors])
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    return json.loads(completed.stdout) if completed.stdout.strip() else []


def list_open_issues(*, limit: int = 5000) -> list[dict[str, Any]]:
    issues = _issue_list(
        ["--state", "open", "--json", "number,title", "--limit", str(limit)],
    )
    if len(issues) >= limit:
        print(
            f"WARNING: {len(issues)} open issues came back against a limit of"
            f" {limit}, so the listing is probably cut short. Raise the limit"
            " before reading anything into what is missing from it.",
            file=sys.stderr,
        )
    return issues
