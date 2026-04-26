"""Mutators for the satisfaction pipeline.

Three mutator functions, each driving Claude (with edit permissions) to
move the codebase from oracle-says-no to oracle-says-yes for one or
more subclauses, then committing the resulting working-tree changes
with one ``Closes #N`` trailer per subclause:

  - ``satisfy_unsatisfied_subclause_without_dependencies``: §X has no
    deps left; Claude works against the diagnostic alone.
  - ``satisfy_unsatisfied_subclause_with_satisfied_dependencies``: §X
    has dependencies that are now satisfied; Claude is told they're in
    place and may reference their machinery.
  - ``satisfy_unsatisfied_subclause_set_with_satisfied_dependencies``:
    A 2- or 3-member dependency cycle co-implemented in one pass.
"""

import sys
from dataclasses import asdict, dataclass

from lib.python.git import commit_and_push, get_porcelain_changes
from lib.python.github import format_subclause_label
from lib.python.lrm import build_lrm_read_instruction

from .oracles import (
    SATISFACTION_CONDITIONS,
    SubclauseDiagnostic,
    build_env,
)
from .streaming import run_claude_streaming


# Mutators may edit source and test files but must never run git, gh,
# build tools, or destructive shell commands directly. The orchestrator
# owns the commit and the CI-equivalent gates.
MUTATOR_DISALLOWED_TOOLS = (
    "Bash(git *) Bash(gh *)"
    " Bash(rm *) Bash(mv *) Bash(cp *)"
    " Bash(cmake *) Bash(make *) Bash(ninja *)"
    " Bash(ctest *) Bash(pytest *)"
)


_MAX_CYCLE_MEMBERS = 3


@dataclass(frozen=True)
class CycleMember:
    """The (subclause, diagnostic, issue) triple a mutator drives.

    Named for its primary use as a member of a dependency cycle, but
    the same shape is used by the single-subclause mutators so the
    function signatures stay short.
    """

    subclause: str
    diagnostic: SubclauseDiagnostic
    issue: int


# ---------------------------------------------------------------------------
# Claude invocation
# ---------------------------------------------------------------------------

def run_mutator_call(prompt: str, *, model: str) -> None:
    """Invoke Claude with mutator tools enabled.

    Runs the CLI in stream-json mode so the streaming runner can
    decode events and print Claude's text/tool_use blocks live —
    mutator passes can take many minutes and the user needs to see
    progress. Loud-fatal on a non-zero exit code.
    """
    cmd = [
        "claude", "-p",
        "--model", model,
        "--verbose",
        "--output-format", "stream-json",
        "--dangerously-skip-permissions",
        "--disallowedTools", MUTATOR_DISALLOWED_TOOLS,
    ]
    run_claude_streaming(cmd, prompt, env=build_env())


# ---------------------------------------------------------------------------
# Diagnostic formatting
# ---------------------------------------------------------------------------

def format_diagnostic_summary(diagnostic: SubclauseDiagnostic) -> str:
    """Format a diagnostic as a bulleted human-readable section."""
    lines: list[str] = []
    payload = asdict(diagnostic)
    for condition in SATISFACTION_CONDITIONS:
        value = payload[condition]
        if value == "satisfied":
            lines.append(f"  - {condition}: satisfied")
            continue
        lines.append(f"  - {condition}:")
        for failure in value:
            lines.append(f"      * {failure}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
# Commit
# ---------------------------------------------------------------------------

_VALID_EXTENSIONS = (".cpp", ".h", ".py")
_VALID_NAMES = ("CMakeLists.txt",)


def is_valid_path(path: str) -> bool:
    """Return True if *path* has a valid source/build extension or name."""
    return (
        any(path.endswith(ext) for ext in _VALID_EXTENSIONS)
        or any(path.endswith(name) for name in _VALID_NAMES)
    )


def filter_changes(
    changes: tuple[list[str], list[str], list[str]],
) -> tuple[list[str], list[str], list[str]]:
    """Drop entries from a porcelain-changes tuple that are not source-y."""
    added, modified, deleted = changes
    return (
        [p for p in added if is_valid_path(p)],
        [p for p in modified if is_valid_path(p)],
        [p for p in deleted if is_valid_path(p)],
    )


def build_commit_message(
    subclauses: list[str], issues: list[int], summary: str,
) -> str:
    """Build a multi-line commit message for the mutator commit."""
    if len(subclauses) == 1:
        title = f"Satisfy {format_subclause_label(subclauses[0])}"
    else:
        labels = " + ".join(format_subclause_label(s) for s in subclauses)
        title = f"Satisfy {labels} (cycle co-implementation)"
    closes = "\n".join(f"Closes #{i}" for i in issues)
    return f"{title}\n\n{summary}\n\n{closes}\n"


def commit_mutator_result(
    subclauses: list[str], issues: list[int],
) -> bool:
    """Commit + push porcelain changes with a Closes trailer.

    Returns ``True`` if anything was committed, ``False`` if the working
    tree had no source-tree changes after the mutator run.
    """
    added, modified, deleted = filter_changes(get_porcelain_changes())
    changed = added + modified
    if not changed and not deleted:
        return False
    summary_lines = [f"- Added {p}" for p in sorted(added)] + \
                    [f"- Modified {p}" for p in sorted(modified)] + \
                    [f"- Deleted {p}" for p in sorted(deleted)]
    summary = "\n".join(summary_lines) or "- (no human-readable summary)"
    message = build_commit_message(subclauses, issues, summary)
    commit_and_push(changed, deleted, message)
    return True


# ---------------------------------------------------------------------------
# Shared prompt blocks
# ---------------------------------------------------------------------------

def build_failure_resolution_block() -> str:
    """Return the per-condition resolution recipe shared by all mutators."""
    return (
        "For every failing condition, take the smallest set of edits"
        " that resolves it:\n"
        "  - rule_coverage failures: write production code that applies"
        " the named normative rule.\n"
        "  - test_coverage failures: write a unit test for the named"
        " normative rule, exercising the production code path.\n"
        "  - test_placement failures: move tests into the canonical"
        " files named by the diagnostic.\n"
        "  - naming failures: rename suites/tests to PascalCase"
        " descriptive names with no clause numbers.\n"
        "  - deduplication failures: delete the redundant test, keeping"
        " the canonical one."
    )


def build_no_external_state_block() -> str:
    """Return the standard 'do not run git/gh/build' guard for mutators."""
    return (
        "Do not run git, gh, cmake, make, ctest, or pytest. Do not"
        " commit or push — the orchestrator script will commit your"
        " file edits after you finish."
    )


def short_circuit_if_satisfied(
    subclause: str, diagnostic: SubclauseDiagnostic,
) -> bool:
    """Return True (and print a notice) when ``diagnostic`` already passes."""
    if diagnostic.verdict == "yes":
        print(
            f"Diagnostic verdict for §{subclause} is already 'yes';"
            " nothing to do.",
            file=sys.stderr,
        )
        return True
    return False


# ---------------------------------------------------------------------------
# Single-subclause mutator core
# ---------------------------------------------------------------------------

def _run_single_subclause_mutator(
    target: CycleMember, prompt: str, *, model: str,
) -> None:
    """Run the Claude mutator and commit the resulting changes."""
    run_mutator_call(prompt, model=model)
    if not commit_mutator_result([target.subclause], [target.issue]):
        print(
            f"Mutator for §{target.subclause} produced no source-tree"
            " changes; nothing committed.",
            file=sys.stderr,
        )


# ---------------------------------------------------------------------------
# Mutator: no dependencies
# ---------------------------------------------------------------------------

def build_no_deps_prompt(
    subclause: str, lrm: str, diagnostic: SubclauseDiagnostic,
) -> str:
    """Return the no-deps mutator prompt for ``subclause``."""
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    summary = format_diagnostic_summary(diagnostic)
    return (
        f"You are the mutator for §{subclause}. The satisfaction oracle"
        " has already audited this subclause and produced the diagnostic"
        " below. Your job is to drive the codebase from"
        " oracle-says-no to oracle-says-yes.\n\n"
        f"{read_ctx}\n\n"
        f"DIAGNOSTIC for §{subclause}:\n{summary}\n\n"
        f"{build_failure_resolution_block()}\n\n"
        f"Act ONLY on requirements directly defined in §{subclause}'s"
        " LRM text. The oracle has confirmed that this subclause has no"
        " remaining dependencies, so every failing rule is implementable"
        " with the infrastructure already in the tree.\n\n"
        f"{build_no_external_state_block()}"
    )


def satisfy_unsatisfied_subclause_without_dependencies(
    target: CycleMember, lrm: str, *, model: str,
) -> None:
    """Mutate the codebase to satisfy ``target`` (no deps remaining)."""
    print(
        f"No-deps mutator: §{target.subclause}, issue #{target.issue},"
        f" model {model}",
        file=sys.stderr,
    )
    if short_circuit_if_satisfied(target.subclause, target.diagnostic):
        return
    prompt = build_no_deps_prompt(target.subclause, lrm, target.diagnostic)
    _run_single_subclause_mutator(target, prompt, model=model)


# ---------------------------------------------------------------------------
# Mutator: with satisfied dependencies
# ---------------------------------------------------------------------------

def build_with_deps_prompt(
    subclause: str,
    lrm: str,
    diagnostic: SubclauseDiagnostic,
    satisfied_dependencies: list[str],
) -> str:
    """Return the with-deps mutator prompt for ``subclause``."""
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    summary = format_diagnostic_summary(diagnostic)
    if satisfied_dependencies:
        deps_list = ", ".join(f"§{s}" for s in satisfied_dependencies)
        deps_block = (
            "DEPENDENCIES already satisfied earlier in the recursion:"
            f" {deps_list}.\n"
            "These subclauses are guaranteed to be in place — you may"
            " reference their machinery, syntax, and tests freely. Do"
            " NOT re-implement anything they already provide."
        )
    else:
        deps_block = (
            "No external dependencies needed to be satisfied first."
        )
    return (
        f"You are the mutator for §{subclause}. The satisfaction oracle"
        " has audited this subclause and produced the diagnostic below."
        " Your job is to drive the codebase from oracle-says-no to"
        " oracle-says-yes.\n\n"
        f"{read_ctx}\n\n"
        f"{deps_block}\n\n"
        f"DIAGNOSTIC for §{subclause}:\n{summary}\n\n"
        f"{build_failure_resolution_block()}\n\n"
        f"Act ONLY on requirements directly defined in §{subclause}'s"
        " LRM text. When a rule needs machinery from one of the"
        " dependencies above, reference that machinery rather than"
        " duplicating it.\n\n"
        f"{build_no_external_state_block()}"
    )


def satisfy_unsatisfied_subclause_with_satisfied_dependencies(
    target: CycleMember, lrm: str,
    satisfied_dependencies: list[str], *, model: str,
) -> None:
    """Mutate the codebase to satisfy ``target`` (deps already satisfied)."""
    print(
        f"With-deps mutator: §{target.subclause},"
        f" deps {satisfied_dependencies},"
        f" issue #{target.issue}, model {model}",
        file=sys.stderr,
    )
    if short_circuit_if_satisfied(target.subclause, target.diagnostic):
        return
    prompt = build_with_deps_prompt(
        target.subclause, lrm, target.diagnostic, satisfied_dependencies,
    )
    _run_single_subclause_mutator(target, prompt, model=model)


# ---------------------------------------------------------------------------
# Mutator: cycle set
# ---------------------------------------------------------------------------

def build_cycle_prompt(
    members: list[CycleMember],
    lrm: str,
    satisfied_dependencies: list[str],
) -> str:
    """Return the cycle-set mutator prompt for ``members``."""
    member_labels = ", ".join(f"§{m.subclause}" for m in members)
    read_instructions = "\n\n".join(
        build_lrm_read_instruction(m.subclause, lrm) for m in members
    )
    diagnostic_blocks = "\n\n".join(
        f"DIAGNOSTIC for §{m.subclause}:\n"
        f"{format_diagnostic_summary(m.diagnostic)}"
        for m in members
    )
    if satisfied_dependencies:
        deps_list = ", ".join(f"§{s}" for s in satisfied_dependencies)
        deps_block = (
            "EXTERNAL dependencies (outside the cycle) already satisfied:"
            f" {deps_list}."
        )
    else:
        deps_block = (
            "No external dependencies needed to be satisfied first."
        )
    return (
        f"You are the cycle co-implementation mutator for {member_labels}."
        " These subclauses form a dependency cycle: each one requires"
        " machinery from the others, so they must be implemented"
        " together in a single pass.\n\n"
        f"{read_instructions}\n\n"
        f"{deps_block}\n\n"
        f"{diagnostic_blocks}\n\n"
        f"{build_failure_resolution_block()}\n\n"
        "When fixing one member, you may freely reference syntax and"
        " machinery defined by another cycle member — that is the"
        " whole reason this is a co-implementation. Do not split the"
        " edits into separate passes.\n\n"
        f"{build_no_external_state_block()}"
    )


def satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
    members: list[CycleMember], lrm: str,
    satisfied_dependencies: list[str], *, model: str,
) -> None:
    """Mutate the codebase to co-implement a 2- or 3-member dependency cycle."""
    if not 2 <= len(members) <= _MAX_CYCLE_MEMBERS:
        raise ValueError(
            f"Cycle must have 2 or {_MAX_CYCLE_MEMBERS} members (got"
            f" {len(members)}). Larger cycles are surfaced to humans"
            " via the pipeline-cycle label.",
        )
    subclauses = [m.subclause for m in members]
    issues = [m.issue for m in members]
    print(
        f"Cycle-set mutator: subclauses {subclauses},"
        f" external deps {satisfied_dependencies}, issues {issues},"
        f" model {model}",
        file=sys.stderr,
    )
    if all(m.diagnostic.verdict == "yes" for m in members):
        print(
            "Every cycle member already has verdict 'yes'; nothing to do.",
            file=sys.stderr,
        )
        return
    prompt = build_cycle_prompt(members, lrm, satisfied_dependencies)
    run_mutator_call(prompt, model=model)
    if not commit_mutator_result(subclauses, issues):
        print(
            f"Cycle-set mutator for {subclauses} produced no source-tree"
            " changes; nothing committed.",
            file=sys.stderr,
        )
