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
bubbles up through every cycle member's frame — only frames at or
below the cycle entry (those whose ``in_progress`` overlaps the
running members set) add themselves — and the cycle-entry frame
(the topmost frame whose own subclause is on the cycle) dispatches
the cycle-set mutator.

There is no satisfaction oracle and no verdict. The audit lives in
steps 1-2 of the mutator pipeline, where Claude produces it free-form
and consumes it in steps 3-8 of the same session — never through a
Python-shaped contract.
"""

import sys
from typing import Any

from lib.python.github import find_or_create_issue
from lib.python.lrm_subclause_dependencies import compute_subclause_dependencies

from .mutators import (
    CycleMember,
    satisfy_unsatisfied_subclause_set_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_without_dependencies,
)


# The dependency oracle is a read-only single-call judgment that maps
# §X's preamble onto a foundations-first list of subclauses. Sonnet at
# medium effort is enough; pinning here means the mutator's Opus budget
# is not spent on each recursion's dep query.
DEP_ORACLE_MODEL = "sonnet"
DEP_ORACLE_EFFORT = "medium"


# ---------------------------------------------------------------------------
# Cycle dispatch
# ---------------------------------------------------------------------------

def _build_cycle_members(
    members: list[str], *, labels: list[str],
) -> list[CycleMember]:
    """Find or create issues for each cycle member."""
    return [
        CycleMember(
            subclause=member,
            issue=find_or_create_issue(member, labels=labels)[0],
        )
        for member in members
    ]


def dispatch_cycle(
    members: list[str], lrm: str, *, model: str, labels: list[str],
) -> None:
    """Run the cycle-set mutator for *members*."""
    cycle = _build_cycle_members(members, labels=labels)
    satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
        cycle, lrm, satisfied_dependencies=[], model=model,
    )


# ---------------------------------------------------------------------------
# Inner orchestration
# ---------------------------------------------------------------------------

def _cycle_marker(
    subclause: str,
    members: list[str],
    *,
    in_progress: frozenset[str],
) -> dict[str, Any]:
    """Return a cycle status dict for a frame relaying the marker upward.

    Adds ``subclause`` to ``members`` only when this frame sits at or
    below the cycle entry — detected by ``members`` overlapping
    ``in_progress``, since the cycle entry is necessarily an ancestor
    in the call stack and therefore in ``in_progress``. Frames above
    the cycle entry are not on the cycle and must not pollute the
    members set.
    """
    members_set = set(members)
    if members_set & in_progress:
        members_set.add(subclause)
    return {"status": "cycle", "members": sorted(members_set)}


def satisfy_unsatisfied_subclause(
    target: CycleMember, lrm: str, *,
    model: str, labels: list[str], in_progress: frozenset[str],
) -> dict[str, Any]:
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

    deps = compute_subclause_dependencies(
        target.subclause, lrm,
        model=DEP_ORACLE_MODEL, effort=DEP_ORACLE_EFFORT,
    )
    cycle_members = [d for d in deps if d in in_progress]
    if cycle_members:
        return _cycle_marker(
            target.subclause, cycle_members, in_progress=in_progress,
        )

    satisfied: list[str] = []
    for dep in deps:
        result = satisfy_subclause(
            dep, lrm, model=model, labels=labels, in_progress=in_progress,
        )
        if result.get("status") == "cycle":
            return _cycle_marker(
                target.subclause, result.get("members", []),
                in_progress=in_progress,
            )
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
    model: str, labels: list[str],
    in_progress: frozenset[str] = frozenset(),
) -> dict[str, Any]:
    """Idempotently satisfy ``subclause``.

    Loud-skips when the tracking issue is already CLOSED — that
    state means §X has already been satisfied (or has no normative
    statements of its own). Reprocessing a closed issue requires the
    operator to deliberately reopen it on GitHub; the orchestrator
    no longer reopens silently.

    Otherwise runs one pass of the mutator pipeline. Returns
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

    issue, state = find_or_create_issue(subclause, labels=labels)
    if state == "CLOSED":
        print(
            f"satisfy_subclause: §{subclause} already satisfied"
            f" (issue #{issue} is CLOSED); nothing to do."
            " Reopen the issue on GitHub if reprocessing is intended.",
            file=sys.stderr,
        )
        return {"status": "satisfied"}

    new_in_progress = in_progress | {subclause}

    target = CycleMember(subclause=subclause, issue=issue)
    result = satisfy_unsatisfied_subclause(
        target, lrm, model=model, labels=labels,
        in_progress=new_in_progress,
    )
    if result.get("status") == "cycle":
        members = result.get("members", [])
        parents_in_members = bool(in_progress & set(members))
        if subclause not in members or parents_in_members:
            return result
        dispatch_cycle(members, lrm, model=model, labels=labels)
    return {"status": "satisfied"}
