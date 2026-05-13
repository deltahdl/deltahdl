"""Batch driver: invoke ``satisfy_subclause`` for each subclause.

Two surfaces:

* ``satisfy_subclauses(subclauses, …)`` loops a fixed list, invoking
  ``satisfy_subclause`` as a subprocess (``python -m satisfy_subclause
  --subclause X.Y …``) per entry. The script-to-script boundary is the
  CLI; no Python imports cross into ``satisfy_subclause``.
* ``satisfy_subclauses_from_issue(issue, …)`` walks a master tracking
  issue (e.g. #1, the IEEE 1800-2023 master list). Each numbered body
  entry is either a linked sub-issue reference (``N. #NNN``) or an
  unlinked subclause marker (``N. §X.Y``). Open linked entries dispatch
  ``satisfy_subclause`` after recovering the subclause from the title;
  closed linked entries are loud-skipped. Unlinked entries run
  ``find_or_create_issue`` (lib), patch the master body line in place
  (``N. §X.Y`` → ``N. #NNN`` — position preserved), PATCH the master,
  then dispatch ``satisfy_subclause``.

All status output (skips, dispatches, banners) goes to stdout. stderr
is reserved for errors that immediately precede ``sys.exit(rc)``.
"""

import json
import re
import subprocess
import sys

from lib.python.cli import SUBCLAUSE_RE
from lib.python.github import (
    extract_subclause_from_title,
    find_or_create_issue,
)


_ENTRY_LINE_RE = re.compile(r"^(\s*\d+\.\s+)(\S+)\s*$")
_HASH_RE = re.compile(r"^#(\d+)$")
_SECTION_RE = re.compile(r"^§(.+)$")


def _run_satisfy_subclause(
    subclause: str, lrm: str, *, model: str, labels: list[str],
) -> None:
    """Invoke ``satisfy_subclause`` as a subprocess for one subclause."""
    cmd = [
        sys.executable, "-m", "satisfy_subclause",
        "--subclause", subclause,
        "--lrm", lrm,
        "--model", model,
        "--labels", ",".join(labels),
    ]
    rc = subprocess.run(cmd, check=False).returncode
    if rc != 0:
        sys.exit(rc)


def satisfy_subclauses(
    subclauses: list[str], lrm: str, *,
    model: str, labels: list[str],
) -> None:
    """Run ``satisfy_subclause`` for each entry in *subclauses*."""
    for subclause in subclauses:
        _run_satisfy_subclause(
            subclause, lrm, model=model, labels=labels,
        )


def _classify_token(token: str) -> tuple[str, str]:
    """Classify a master-body entry token as ``("hash", N)`` or ``("section", X)``."""
    m_hash = _HASH_RE.fullmatch(token)
    if m_hash is not None:
        return "hash", m_hash.group(1)
    m_section = _SECTION_RE.fullmatch(token)
    if m_section is not None:
        subclause = m_section.group(1)
        if SUBCLAUSE_RE.fullmatch(subclause) is None:
            raise ValueError(
                f"satisfy_subclauses: unrecognised master-body token: {token!r}"
            )
        return "section", subclause
    raise ValueError(
        f"satisfy_subclauses: unrecognised master-body token: {token!r}"
    )


def _fetch_master(issue: int) -> list[str]:
    """Return the master issue's body split into lines (loud-fatal on gh error)."""
    completed = subprocess.run(
        ["gh", "issue", "view", str(issue), "--json", "body"],
        capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    body: str = json.loads(completed.stdout)["body"]
    lines = body.splitlines()
    print(
        f"satisfy_subclauses: fetched master body from issue #{issue}"
        f" ({len(lines)} lines)"
    )
    return lines


def _fetch_linked_issue(num: int) -> tuple[str, str]:
    """Return ``(state_upper, title)`` for a linked sub-issue."""
    completed = subprocess.run(
        ["gh", "issue", "view", str(num), "--json", "state,title"],
        capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    payload = json.loads(completed.stdout)
    state: str = payload["state"].upper()
    title: str = payload["title"]
    return state, title


def _resolve_linked(num: int, *, line_index: int) -> str | None:
    """Resolve a `#NNN` entry to its subclause string, or None if closed."""
    state, title = _fetch_linked_issue(num)
    if state == "CLOSED":
        print(
            f"satisfy_subclauses: skipping closed sub-issue #{num}"
            f" (line {line_index})"
        )
        return None
    subclause = extract_subclause_from_title(title)
    if not subclause:
        raise RuntimeError(
            f"satisfy_subclauses: unparseable title for issue #{num}"
            f" (line {line_index}): {title!r}"
        )
    return subclause


def _patch_master_body(master_issue: int, body: str) -> None:
    """PATCH the master issue body via ``gh issue edit --body-file -``."""
    completed = subprocess.run(
        ["gh", "issue", "edit", str(master_issue), "--body-file", "-"],
        input=body, capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)


def _resolve_unlinked(
    line_index: int, subclause: str, *,
    master_issue: int, body_lines: list[str], labels: list[str],
) -> str:
    """Find-or-create a sub-issue for ``§X.Y``; PATCH the master line in place."""
    number = find_or_create_issue(subclause, labels=labels)
    body_lines[line_index] = _ENTRY_LINE_RE.sub(
        rf"\g<1>#{number}", body_lines[line_index],
    )
    _patch_master_body(master_issue, "\n".join(body_lines))
    print(
        f"satisfy_subclauses: linked §{subclause} → #{number}"
        f" on line {line_index} of master"
    )
    return subclause


def satisfy_subclauses_from_issue(
    issue: int, lrm: str, *,
    model: str, labels: list[str],
) -> None:
    """Walk *issue*'s master body and satisfy each entry."""
    print(f"satisfy_subclauses: starting --issue {issue} run")
    body_lines = _fetch_master(issue)
    for i, line in enumerate(body_lines):
        m = _ENTRY_LINE_RE.fullmatch(line)
        if m is None:
            if line.strip() == "":
                continue
            print(
                f"satisfy_subclauses: ignoring non-entry line {i}: {line!r}"
            )
            continue
        kind, value = _classify_token(m.group(2))
        if kind == "hash":
            subclause = _resolve_linked(int(value), line_index=i)
            if subclause is None:
                continue
            print(
                f"satisfy_subclauses: dispatching #{value}"
                f" (§{subclause}, line {i})"
            )
            _run_satisfy_subclause(
                subclause, lrm, model=model, labels=labels,
            )
        else:
            print(f"satisfy_subclauses: resolving §{value} (line {i})")
            subclause = _resolve_unlinked(
                i, value, master_issue=issue,
                body_lines=body_lines, labels=labels,
            )
            _run_satisfy_subclause(
                subclause, lrm, model=model, labels=labels,
            )
