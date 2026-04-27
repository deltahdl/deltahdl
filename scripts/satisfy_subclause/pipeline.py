"""Recursive driver for the satisfaction pipeline.

``satisfy_subclause`` is the entry point: it finds-or-creates a
GitHub issue for the requested subclause, computes its dependencies,
recursively satisfies each dependency, and dispatches the appropriate
mutator. The mutator runs the eight-step audit-then-act pipeline once;
convergence is detected by the working tree (the mutator commits any
edits with a ``Closes #N`` trailer; an empty diff means the codebase
already satisfied §X — or now does — and nothing is committed).

Cycle detection is honest: ``in_progress`` threads through the
recursion as a frozen set of subclause identifiers. When the inner
function discovers a dependency that already appears in that set, it
returns a cycle marker rather than recursing into it. The marker
bubbles up through every cycle member's frame; the outermost frame
(whose ``in_progress`` does not yet contain it) dispatches the
cycle-set mutator.

There is no satisfaction oracle and no verdict. The audit lives in
steps 1-2 of the mutator pipeline, where Claude produces it free-form
and consumes it in steps 3-8 of the same session — never through a
Python-shaped contract.
"""

import json
import subprocess
import sys

from .mutators import (
    CycleMember,
    satisfy_unsatisfied_subclause_set_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_without_dependencies,
)
from .oracles import compute_subclause_dependencies


# ---------------------------------------------------------------------------
# GitHub issue handling
# ---------------------------------------------------------------------------

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


def _list_issues_for(subclause: str) -> list[dict]:
    """Return the gh-issue-list payload for *subclause* (loud-fatal on error).

    ``gh issue list`` defaults to 30 results. A heavily-subdivided clause
    (e.g. §23 with §23.x.y.z descendants) easily exceeds that, pushing
    the master-list issue past the cutoff so the matcher can't see it
    and silently opens a duplicate. Raise the limit well above any
    realistic per-clause result count.
    """
    completed = subprocess.run(
        [
            "gh", "issue", "list",
            "--state", "all",
            "--search", f"§{subclause}",
            "--json", "number,title,state",
            "--limit", "1000",
        ],
        capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    return json.loads(completed.stdout) if completed.stdout.strip() else []


def _create_new_issue(subclause: str) -> int:
    """Create a fresh issue for *subclause* and return its number."""
    completed = subprocess.run(
        [
            "gh", "issue", "create",
            "--title", issue_title_for(subclause),
            "--body", (
                f"Track satisfying §{subclause} via the satisfaction"
                " pipeline (#1265)."
            ),
        ],
        capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    return parse_issue_number_from_create_output(completed.stdout)


def find_or_create_issue(subclause: str) -> int:
    """Return the issue number for *subclause*.

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
    dropped) and reopened if closed. Creates a fresh issue when no
    match exists.
    """
    matches = [
        entry for entry in _list_issues_for(subclause)
        if _title_matches(entry.get("title", "") or "", subclause)
    ]
    if not matches:
        return _create_new_issue(subclause)

    matches.sort(key=lambda entry: int(entry["number"]))
    oldest, *duplicates = matches
    for dup_entry in duplicates:
        subprocess.run(
            [
                "gh", "issue", "delete",
                str(int(dup_entry["number"])), "--yes",
            ],
            check=False,
        )

    number = int(oldest["number"])
    canonical = issue_title_for(subclause)
    if oldest.get("title") != canonical:
        subprocess.run(
            ["gh", "issue", "edit", str(number), "--title", canonical],
            check=False,
        )
    if oldest.get("state", "").lower() == "closed":
        subprocess.run(
            ["gh", "issue", "reopen", str(number)],
            check=False,
        )
    return number


# ---------------------------------------------------------------------------
# Cycle dispatch
# ---------------------------------------------------------------------------

def _build_cycle_members(members: list[str]) -> list[CycleMember]:
    """Find or create issues for each cycle member."""
    return [
        CycleMember(subclause=member, issue=find_or_create_issue(member))
        for member in members
    ]


def dispatch_cycle(members: list[str], lrm: str, *, model: str) -> None:
    """Run the cycle-set mutator for *members*."""
    cycle = _build_cycle_members(members)
    satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
        cycle, lrm, satisfied_dependencies=[], model=model,
    )


# ---------------------------------------------------------------------------
# Inner orchestration
# ---------------------------------------------------------------------------

def _cycle_marker(subclause: str, members) -> dict:
    """Return a cycle status dict including ``subclause``."""
    combined = sorted(set(members) | {subclause})
    return {"status": "cycle", "members": combined}


def satisfy_unsatisfied_subclause(
    target: CycleMember, lrm: str, *,
    model: str, in_progress: frozenset,
) -> dict:
    """Compute deps, recurse, then dispatch the right mutator.

    Returns ``{"status": "satisfied"}`` on success or
    ``{"status": "cycle", "members": [...]}`` when a dependency cycle
    is detected. The caller is responsible for either propagating the
    cycle further up or dispatching the cycle-set mutator.
    """
    print(
        f"Inner orchestrator: §{target.subclause},"
        f" in-progress {sorted(in_progress)}, model {model}",
        file=sys.stderr,
    )

    deps = compute_subclause_dependencies(target.subclause, lrm, model=model)
    cycle_members = [d for d in deps if d in in_progress]
    if cycle_members:
        return _cycle_marker(target.subclause, cycle_members)

    satisfied: list[str] = []
    for dep in deps:
        result = satisfy_subclause(
            dep, lrm, model=model, in_progress=in_progress,
        )
        if result.get("status") == "cycle":
            return _cycle_marker(target.subclause, result.get("members", []))
        satisfied.append(dep)

    if satisfied:
        satisfy_unsatisfied_subclause_with_satisfied_dependencies(
            target, lrm, satisfied, model=model,
        )
    else:
        satisfy_unsatisfied_subclause_without_dependencies(
            target, lrm, model=model,
        )
    return {"status": "satisfied"}


# ---------------------------------------------------------------------------
# Outer orchestration
# ---------------------------------------------------------------------------

def satisfy_subclause(
    subclause: str, lrm: str, *,
    model: str, in_progress: frozenset = frozenset(),
) -> dict:
    """Idempotently satisfy ``subclause``.

    Runs one pass of the eight-step mutator pipeline. Returns
    ``{"status": "satisfied"}`` after the pass completes, or
    ``{"status": "cycle", "members": [...]}`` when a cycle bubbles up
    through this frame and an outer caller is responsible for
    dispatching the cycle-set mutator. The mutator's commit step is
    the convergence signal: empty diff means §X already satisfied (or
    now does), non-empty diff is committed with a ``Closes #N``
    trailer.
    """
    print(
        f"Outer orchestrator: §{subclause}, model {model},"
        f" in-progress {sorted(in_progress)}",
        file=sys.stderr,
    )

    issue = find_or_create_issue(subclause)
    new_in_progress = in_progress | {subclause}

    target = CycleMember(subclause=subclause, issue=issue)
    result = satisfy_unsatisfied_subclause(
        target, lrm, model=model, in_progress=new_in_progress,
    )
    if result.get("status") == "cycle":
        members = result.get("members", [])
        if subclause in members and in_progress:
            return result
        dispatch_cycle(members, lrm, model=model)
    return {"status": "satisfied"}
