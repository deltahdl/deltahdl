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


def issue_title_for(subclause: str) -> str:
    """Return the canonical GitHub issue title for *subclause*."""
    return f"Satisfy IEEE 1800-2023 §{subclause}"


def _issue_list(selectors: list[str]) -> list[dict[str, Any]]:
    """Return the ``gh issue list`` payload for *selectors*.

    Loud-fatal on a non-zero exit, because a listing that could not be
    taken is not an empty listing: reporting it as one would have the
    caller act on a repository it never saw.
    """
    completed = _run_gh(["gh", "issue", "list", *selectors])
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    return json.loads(completed.stdout) if completed.stdout.strip() else []


def list_open_issues(*, limit: int = 5000) -> list[dict[str, Any]]:
    """Return the number and title of every open issue in the repository.

    A caller wanting one issue searches for it; this is for a caller that
    has to decide something against the whole open set and therefore has
    to see all of it. That makes the result count the hazard rather than
    the query: a listing truncated at the limit is indistinguishable from
    a repository holding exactly that many issues, and a caller reading
    the short list would conclude something about issues it was never
    shown. So a result count reaching the limit is reported as the
    suspected truncation it is, and the limit is a parameter so that a
    caller meeting one can raise it.
    """
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
