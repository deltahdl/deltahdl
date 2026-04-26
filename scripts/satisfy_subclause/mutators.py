"""Mutators for the satisfaction pipeline.

Three dispatch shells, each driving Claude (with edit permissions)
through the eight-step audit-then-act pipeline ported from the
deleted ``implement_subclause`` script. Each shell runs the steps in
one ``--continue``d Claude session and then commits whatever changes
landed on disk with one ``Closes #N`` trailer per subclause:

  - ``satisfy_unsatisfied_subclause_without_dependencies``: §X has no
    deps left; the eight steps act on §X alone.
  - ``satisfy_unsatisfied_subclause_with_satisfied_dependencies``: §X
    has dependencies that are now satisfied; step 1 tells Claude they
    are in place and may be referenced rather than re-implemented.
  - ``satisfy_unsatisfied_subclause_set_with_satisfied_dependencies``:
    A 2- or 3-member dependency cycle co-implemented in one pass; the
    eight steps run once over the cycle set, with each step naming
    every member.

There is no diagnostic and no verdict. The audit lives in steps 1-2
of the eight-step pipeline; steps 3-8 act on what those audits found.
Convergence is detected by the orchestrator observing whether the
working tree changed — empty diff means §X already satisfied (or now
does); non-empty diff is committed with a ``Closes #N`` trailer.
"""

import sys
from dataclasses import dataclass

from lib.python.clause import STAGE_TO_PREFIX, clause_to_filename
from lib.python.git import commit_and_push, get_porcelain_changes
from lib.python.github import format_subclause_label
from lib.python.lrm import build_lrm_read_instruction

from .oracles import build_env
from .streaming import build_streaming_cmd, run_claude_streaming


# Mutators may edit source and test files but must never run git, gh,
# build tools, or destructive shell commands directly. The orchestrator
# owns the commit and the CI-equivalent gates.
MUTATOR_DISALLOWED_TOOLS = (
    "Bash(git *) Bash(gh *)"
    " Bash(rm *) Bash(mv *) Bash(cp *)"
    " Bash(cmake *) Bash(make *) Bash(ninja *)"
    " Bash(ctest *) Bash(pytest *)"
    " Bash(pdftotext *) Bash(pdfgrep *) Bash(pdftohtml *)"
    " Bash(pdftoppm *) Bash(mutool *)"
)


_MAX_CYCLE_MEMBERS = 3


@dataclass(frozen=True)
class CycleMember:
    """The (subclause, issue) pair a mutator drives.

    Named for its primary use as a member of a dependency cycle, but
    the same shape is used by the single-subclause mutators so the
    function signatures stay short.
    """

    subclause: str
    issue: int


# ---------------------------------------------------------------------------
# Claude invocation
# ---------------------------------------------------------------------------

def run_step(
    prompt: str, *, model: str, continue_session: bool,
) -> None:
    """Invoke Claude for one step of the eight-step pipeline.

    Runs the CLI in stream-json mode so the streaming runner can
    decode events and print Claude's text/tool_use blocks live —
    each step can take many minutes and the user needs to see
    progress. When ``continue_session`` is true the call resumes the
    most recent Claude session so the steps share an audit context;
    when false the call opens a fresh session. Loud-fatal on a
    non-zero exit code.
    """
    cmd = build_streaming_cmd(
        model=model,
        disallowed_tools=MUTATOR_DISALLOWED_TOOLS,
        continue_session=continue_session,
    )
    run_claude_streaming(cmd, prompt, env=build_env())


def run_steps(
    steps: list[tuple[str, str]], *, model: str,
) -> None:
    """Run each ``(description, prompt)`` step as a separate Claude call.

    The first step opens a fresh session; every later step continues
    the same session via ``--continue`` so the audit it produced in
    steps 1-2 is available to the action steps in 3-8.
    """
    total = len(steps)
    for i, (description, prompt) in enumerate(steps):
        print(f"\nStep {i + 1}/{total}: {description}", flush=True)
        run_step(prompt, model=model, continue_session=i > 0)


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
# Eight-step prompt construction
# ---------------------------------------------------------------------------

def _canonical_test_files(subclause: str) -> str:
    """Return a comma-separated list of canonical test files for ``subclause``."""
    examples = [
        clause_to_filename(prefix, subclause) + ".cpp"
        for _stage, prefix in sorted(STAGE_TO_PREFIX.items())
    ]
    return ", ".join(examples)


def _all_canonical_test_files(subclauses: list[str]) -> str:
    """Return a comma-separated list of canonical test files for every member."""
    parts: list[str] = []
    for subclause in subclauses:
        parts.append(_canonical_test_files(subclause))
    return ", ".join(parts)


def _scope_label(subclauses: list[str]) -> str:
    """Return ``§X`` for a single subclause or ``§X, §Y, §Z`` for a cycle."""
    return ", ".join(f"§{s}" for s in subclauses)


def _build_constraints(subclauses: list[str]) -> str:
    """Return the standard per-step constraints block.

    Reused verbatim by every action step. Names every member of the
    pipeline scope (one subclause for the single-subclause mutators,
    every cycle member for the cycle-set mutator) so Claude does not
    drift into satisfying neighbouring subclauses.
    """
    label = _scope_label(subclauses)
    return (
        f" Only act on requirements directly defined in the text of"
        f" {label} in the LRM — not requirements defined by"
        f" any descendant subclause of those subclauses."
        " A requirement belongs to the subclause whose LRM text defines it."
        " In this step your only action is creating, editing, or removing"
        " files on disk."
        " This step is complete when the file edits on disk"
        " land the step's deliverable."
        f" A normative statement in {label} is satisfied when"
        " production code applies the rule and a test at the same"
        " pipeline stage observes the rule being applied by that"
        " production code."
        " Pipeline stages come from the project's stage-to-file mapping;"
        " the stage where a rule applies is the stage whose source file"
        " carries the rule and whose test file covers it."
        f" When {label}'s own text requires a shared type or shared"
        " code path to change, edit those shared files in this run."
        " Requirement ownership is scoped by subclause; file editing"
        f" is scoped by what {label}'s text requires."
        " Write original comments; do not copy LRM prose into source files."
    )


def _build_dependencies_block(satisfied_dependencies: list[str]) -> str:
    """Return the dependency-status block prepended to step 1.

    For the no-deps mutator this is the no-deps notice; for the
    with-deps and cycle mutators this lists every external dependency
    already satisfied earlier in the recursion.
    """
    if not satisfied_dependencies:
        return (
            "No external dependencies needed to be satisfied first."
            " Every failing rule is implementable with the"
            " infrastructure already in the tree."
        )
    deps_list = ", ".join(f"§{s}" for s in satisfied_dependencies)
    return (
        "DEPENDENCIES already satisfied earlier in the recursion:"
        f" {deps_list}.\n"
        "These subclauses are guaranteed to be in place — you may"
        " reference their machinery, syntax, and tests freely. Do"
        " NOT re-implement anything they already provide."
    )


def _build_cycle_intro_block(subclauses: list[str]) -> str:
    """Return the cycle-relationship preface for step 1 of a cycle run."""
    if len(subclauses) == 1:
        return ""
    label = _scope_label(subclauses)
    return (
        f"You are co-implementing the dependency cycle {label}: each"
        " of these subclauses requires machinery from the others, so"
        " they must be implemented together in a single pass. When"
        " fixing one member, you may freely reference syntax and"
        " machinery defined by another cycle member.\n\n"
    )


def build_steps(
    subclauses: list[str],
    lrm: str,
    *,
    satisfied_dependencies: list[str],
) -> list[tuple[str, str]]:
    """Return the eight ``(description, prompt)`` step pairs.

    A list of one subclause produces the single-subclause pipeline; a
    list of 2-3 subclauses produces the cycle co-implementation
    pipeline (every step names every member). The
    ``satisfied_dependencies`` list seeds step 1 so Claude knows which
    machinery it may reference rather than re-implement.
    """
    label = _scope_label(subclauses)
    constraints = _build_constraints(subclauses)
    cycle_intro = _build_cycle_intro_block(subclauses)
    deps_block = _build_dependencies_block(satisfied_dependencies)
    read_instructions = "\n\n".join(
        build_lrm_read_instruction(s, lrm) for s in subclauses
    )
    canonical_files = _all_canonical_test_files(subclauses)

    return [
        ("Auditing src",
         f"{cycle_intro}{read_instructions}\n\n"
         f"{deps_block}\n\n"
         f"Then search src/ for existing code that handles {label}."
         " Report what aligns with the LRM and what is missing."
         + constraints),
        ("Auditing tests",
         f"Search all files in test/src/unit/ for any tests that cover"
         f" {label} requirements."
         " Tests may be misplaced in files belonging to other subclauses."
         " Report what is covered, what is missing, and any tests"
         f" found in the wrong files."
         f" The correct files for {label} tests are: {canonical_files}."
         + constraints),
        ("Deleting duplicate tests",
         f"Delete any duplicate tests that belong to {label}."
         " Do NOT delete tests that belong to other subclauses,"
         " even if they look similar."
         + constraints),
        ("Moving misplaced tests",
         f"Search ALL files in test/src/unit/ for tests that belong to"
         f" {label}. Move any that are in the wrong files"
         f" to the correct files: {canonical_files}."
         " Do NOT put tests in a parent clause file."
         " If moving tests leaves a file empty, delete that file"
         " and remove its entry from test/CMakeLists.txt."
         + constraints),
        ("Renaming test suites",
         f"Rename any test suites that test {label} requirements"
         " and have unintuitive names"
         " (e.g., containing clause numbers like Cl5_7_1_),"
         " regardless of which file they are in."
         " Use PascalCase names that describe what is being tested."
         " Do NOT include clause or annex numbers."
         " Do NOT rename or modify tests that belong to other subclauses."
         + constraints),
        ("Renaming test names",
         f"Rename any test names that test {label} requirements"
         " and have unintuitive names"
         " (e.g., containing clause numbers like Cl5_7_1_),"
         " regardless of which file they are in."
         " Use PascalCase names that describe what is being tested."
         " Do NOT include clause or annex numbers."
         " Do NOT rename or modify tests that belong to other subclauses."
         + constraints),
        ("Writing missing tests",
         f"Write missing unit tests for {label} requirements."
         f" Place them in: {canonical_files}."
         " Cover all affected pipeline stages."
         " Include error conditions and edge cases."
         " Each test exercises the production code path at the"
         " pipeline stage named by the normative statement it covers"
         " — a test is sufficient when running it would"
         " observe the rule being applied by production code, not by"
         " a reference model or helper."
         f" If a member of {label} defines no testable requirements"
         " of its own (only its descendants do), do NOT create test"
         " files for it."
         + constraints),
        ("Writing missing functionality",
         f"First, list every normative statement in the LRM text of"
         f" {label} (typically 'shall' sentences, plus unambiguous"
         " declarative requirements). For each,"
         " name the pipeline stage the rule applies to and the source"
         " file that will carry the rule. Then"
         " make the source-file edits so the production code applies"
         " each rule."
         f" Write or edit the source files to add any missing"
         f" functionality defined in {label}."
         f" Act only on {label}, no other subclauses."
         + constraints),
    ]


# ---------------------------------------------------------------------------
# Mutator: no dependencies
# ---------------------------------------------------------------------------

def satisfy_unsatisfied_subclause_without_dependencies(
    target: CycleMember, lrm: str, *, model: str,
) -> None:
    """Run the eight-step pipeline for ``target`` (no deps remaining)."""
    print(
        f"No-deps mutator: §{target.subclause}, issue #{target.issue},"
        f" model {model}",
        file=sys.stderr,
    )
    steps = build_steps(
        [target.subclause], lrm, satisfied_dependencies=[],
    )
    run_steps(steps, model=model)
    if not commit_mutator_result([target.subclause], [target.issue]):
        print(
            f"Mutator for §{target.subclause} produced no source-tree"
            " changes; nothing committed.",
            file=sys.stderr,
        )


# ---------------------------------------------------------------------------
# Mutator: with satisfied dependencies
# ---------------------------------------------------------------------------

def satisfy_unsatisfied_subclause_with_satisfied_dependencies(
    target: CycleMember, lrm: str,
    satisfied_dependencies: list[str], *, model: str,
) -> None:
    """Run the eight-step pipeline for ``target`` (deps already satisfied)."""
    print(
        f"With-deps mutator: §{target.subclause},"
        f" deps {satisfied_dependencies},"
        f" issue #{target.issue}, model {model}",
        file=sys.stderr,
    )
    steps = build_steps(
        [target.subclause], lrm,
        satisfied_dependencies=satisfied_dependencies,
    )
    run_steps(steps, model=model)
    if not commit_mutator_result([target.subclause], [target.issue]):
        print(
            f"Mutator for §{target.subclause} produced no source-tree"
            " changes; nothing committed.",
            file=sys.stderr,
        )


# ---------------------------------------------------------------------------
# Mutator: cycle set
# ---------------------------------------------------------------------------

def satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
    members: list[CycleMember], lrm: str,
    satisfied_dependencies: list[str], *, model: str,
) -> None:
    """Run the eight-step pipeline for a 2- or 3-member dependency cycle."""
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
    steps = build_steps(
        subclauses, lrm,
        satisfied_dependencies=satisfied_dependencies,
    )
    run_steps(steps, model=model)
    if not commit_mutator_result(subclauses, issues):
        print(
            f"Cycle-set mutator for {subclauses} produced no source-tree"
            " changes; nothing committed.",
            file=sys.stderr,
        )
