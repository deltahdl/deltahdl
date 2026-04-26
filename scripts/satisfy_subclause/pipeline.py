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
    return f"Satisfy §{subclause}"


def legacy_issue_title_for(subclause: str) -> str:
    """Return the historical pre-pipeline GitHub issue title for *subclause*."""
    return (
        f"Ensure IEEE 1800-2023 §{subclause} functionalities and tests are"
        " implemented and properly named"
    )


def parse_issue_number_from_create_output(output: str) -> int:
    """Extract the issue number from a ``gh issue create`` URL."""
    url = output.strip().splitlines()[-1].strip()
    return int(url.rsplit("/", 1)[-1])


def find_or_create_issue(subclause: str) -> int:
    """Return the issue number for *subclause* (creating, reopening, or
    migrating a legacy-titled issue in place)."""
    title = issue_title_for(subclause)
    legacy_title = legacy_issue_title_for(subclause)
    completed = subprocess.run(
        [
            "gh", "issue", "list",
            "--state", "all",
            "--search", f"§{subclause}",
            "--json", "number,title,state",
        ],
        capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    matches = json.loads(completed.stdout) if completed.stdout.strip() else []
    for entry in matches:
        entry_title = entry.get("title")
        if entry_title not in (title, legacy_title):
            continue
        number = int(entry["number"])
        if entry_title == legacy_title:
            subprocess.run(
                ["gh", "issue", "edit", str(number), "--title", title],
                check=False,
            )
        if entry.get("state", "").lower() == "closed":
            subprocess.run(
                ["gh", "issue", "reopen", str(number)],
                check=False,
            )
        return number
    completed = subprocess.run(
        [
            "gh", "issue", "create",
            "--title", title,
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
