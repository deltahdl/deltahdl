"""Recursive driver for the satisfaction pipeline.

``satisfy_subclause`` is the entry point: it runs the satisfaction
oracle, returns early on verdict yes, finds-or-creates a GitHub issue,
and recursively dispatches to ``satisfy_unsatisfied_subclause`` until
either the oracle flips to yes, the recursion bubbles up a cycle that
this frame is the outermost member of (and so dispatches the cycle-set
mutator), or the retry budget is exhausted (and the issue is labelled
``pipeline-stuck``).

Cycle detection is honest: ``in_progress`` threads through the
recursion as a frozen set of subclause identifiers. When the inner
function discovers a dependency that already appears in that set, it
returns a cycle marker rather than recursing into it. The marker
bubbles up through every cycle member's frame; the outermost frame
(whose ``in_progress`` does not yet contain it) dispatches the
cycle-set mutator.
"""

import json
import subprocess
import sys
from dataclasses import asdict

from .mutators import (
    CycleMember,
    satisfy_unsatisfied_subclause_set_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_with_satisfied_dependencies,
    satisfy_unsatisfied_subclause_without_dependencies,
)
from .oracles import (
    SubclauseDiagnostic,
    compute_subclause_dependencies,
    is_subclause_satisfied,
)


_MAX_RETRIES = 1


# ---------------------------------------------------------------------------
# GitHub issue handling
# ---------------------------------------------------------------------------

def issue_title_for(subclause: str) -> str:
    """Return the canonical GitHub issue title for *subclause*."""
    return f"Satisfy §{subclause}"


def parse_issue_number_from_create_output(output: str) -> int:
    """Extract the issue number from a ``gh issue create`` URL."""
    url = output.strip().splitlines()[-1].strip()
    return int(url.rsplit("/", 1)[-1])


def find_or_create_issue(subclause: str) -> int:
    """Return the issue number for *subclause* (creating or reopening)."""
    title = issue_title_for(subclause)
    completed = subprocess.run(
        [
            "gh", "issue", "list",
            "--state", "all",
            "--search", title,
            "--json", "number,title,state",
        ],
        capture_output=True, text=True, check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    matches = json.loads(completed.stdout) if completed.stdout.strip() else []
    for entry in matches:
        if entry.get("title") == title:
            number = int(entry["number"])
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


def label_issue_pipeline_stuck(
    issue: int, diagnostic: SubclauseDiagnostic,
) -> None:
    """Add the pipeline-stuck label and post the final diagnostic comment."""
    subprocess.run(
        ["gh", "issue", "edit", str(issue),
         "--add-label", "pipeline-stuck"],
        check=False,
    )
    body = "Pipeline stuck after retry. Final diagnostic:\n```json\n" \
        + json.dumps(asdict(diagnostic), indent=2) + "\n```\n"
    subprocess.run(
        ["gh", "issue", "comment", str(issue), "--body", body],
        check=False,
    )


# ---------------------------------------------------------------------------
# Cycle dispatch
# ---------------------------------------------------------------------------

def _build_cycle_members(
    members: list[str], lrm: str, *, model: str,
) -> list[CycleMember]:
    """Run the oracle and find/create issues for each cycle member."""
    return [
        CycleMember(
            subclause=member,
            diagnostic=is_subclause_satisfied(member, lrm, model=model),
            issue=find_or_create_issue(member),
        )
        for member in members
    ]


def dispatch_cycle(members: list[str], lrm: str, *, model: str) -> None:
    """Run the cycle-set mutator for *members*."""
    cycle = _build_cycle_members(members, lrm, model=model)
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

    Returns ``{"status": "satisfied"}`` if the subclause is satisfied
    on entry or after the pipeline runs. Returns
    ``{"status": "cycle", "members": [...]}`` when a cycle bubbles up
    through this frame and an outer caller is responsible for
    dispatching the cycle-set mutator. Exits non-zero (after labelling
    the issue ``pipeline-stuck``) when the retry budget is exhausted.
    """
    print(
        f"Outer orchestrator: §{subclause}, model {model},"
        f" in-progress {sorted(in_progress)}",
        file=sys.stderr,
    )

    diagnostic = is_subclause_satisfied(subclause, lrm, model=model)
    if diagnostic.verdict == "yes":
        print(f"§{subclause} already satisfied; nothing to do.",
              file=sys.stderr)
        return {"status": "satisfied"}

    issue = find_or_create_issue(subclause)
    new_in_progress = in_progress | {subclause}

    for attempt in range(_MAX_RETRIES + 1):
        target = CycleMember(
            subclause=subclause, diagnostic=diagnostic, issue=issue,
        )
        result = satisfy_unsatisfied_subclause(
            target, lrm, model=model, in_progress=new_in_progress,
        )
        if result.get("status") == "cycle":
            members = result.get("members", [])
            if subclause in members and in_progress:
                return result
            dispatch_cycle(members, lrm, model=model)
        diagnostic = is_subclause_satisfied(subclause, lrm, model=model)
        if diagnostic.verdict == "yes":
            return {"status": "satisfied"}
        if attempt < _MAX_RETRIES:
            print(
                f"Pass {attempt + 1} did not converge for §{subclause};"
                " retrying once with the fresh diagnostic.",
                file=sys.stderr,
            )

    label_issue_pipeline_stuck(issue, diagnostic)
    sys.exit(1)
