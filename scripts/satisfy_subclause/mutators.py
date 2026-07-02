"""Mutators for the satisfaction pipeline.

Three dispatch shells, each driving Claude (with edit permissions)
through the audit-then-act pipeline ported from the deleted
``implement_subclause`` script. Each shell runs the steps in one
``--continue``d Claude session and then commits whatever changes
landed on disk with one ``Closes #N`` trailer per subclause:

  - ``satisfy_unsatisfied_subclause_without_dependencies``: §X has no
    deps left; the steps act on §X alone.
  - ``satisfy_unsatisfied_subclause_with_satisfied_dependencies``: §X
    has dependencies that are now satisfied; step 1 tells Claude they
    are in place and may be referenced rather than re-implemented.
  - ``satisfy_unsatisfied_subclause_set_with_satisfied_dependencies``:
    A multi-member dependency cycle satisfied in one pass; the steps
    run once over the cycle set, with each step naming every member.

Every step scopes its edits to the named subclause's canonical files.
Cleanups inside those files (duplicate-deletion, non-normative
deletion, empty-file deletion) are local. A test misfiled into
another subclause's canonical file is that subclause's pass's problem
to remove; a missing observation in §X's canonical file is §X's
pass's problem to write. No subclause reaches into another's files.

There is no diagnostic and no verdict. The audit in steps 1-2 begins
by enumerating every normative claim in the subclause's LRM text
(BNF productions, "shall" sentences, declarative requirements), then
audits src/ and the canonical test files against the enumeration.
The action steps work that enumeration to completion.
Convergence is detected by the orchestrator observing whether the
working tree changed — empty diff means §X already satisfied (or now
does); non-empty diff is committed with a ``Closes #N`` trailer.
"""

import os
import subprocess
import sys
from dataclasses import dataclass

from lib.python.clause import STAGE_TO_PREFIX, clause_to_filename
from lib.python.claude_cli_streaming import (
    COPYRIGHT_REASON,
    build_env,
    build_streaming_cmd,
    run_claude_streaming_with_retry,
    write_deny_hook_settings,
)
from lib.python.git import commit_and_push, get_porcelain_changes
from lib.python.github import format_subclause_label
from lib.python.lrm import build_lrm_read_instruction


# Bare-command patterns the PreToolUse hook denies for both sub-Claude
# contexts. `git` and `gh` are the orchestrator's tools for committing,
# pushing, and closing issues; the build/test tools are the orchestrator's
# CI-equivalent gate; the PDF readers are unnecessary because the LRM is
# supplied through the read-instruction helper. The clang variants are
# listed individually because the deny hook matches on first-token equality,
# so `clang` alone would not block `clang-format` or `clang++`.
_SHARED_DENY_PATTERNS = [
    "git", "gh",
    "cmake", "make", "ninja",
    "ctest", "pytest",
    "clang", "clang++", "clang-format", "clang-tidy", "clangd",
    "pdftotext", "pdfgrep", "pdftohtml", "pdftoppm", "mutool",
]


# Mutators may edit, create, delete, and rename source and test files
# but must never run git, gh, or build/test tools directly. The
# orchestrator owns the commit and the CI-equivalent gates: it reads
# git status --porcelain after the eight-step pass and translates the
# deleted set into git rm at commit time, so on-disk rm/mv by the
# mutator is the supported path for Steps 4 and 6.
MUTATOR_DENY_PATTERNS = list(_SHARED_DENY_PATTERNS)


# The commit-body generator narrates what the eight-step session
# already did, working from the porcelain file list in the prompt plus
# the --continue session context. Allowing `git` once let a body
# session run `git add`/`git commit`/`git push` to land an unrelated
# "Dedup §X tests" follow-up commit, splitting one logical change
# across two SHAs — so `git` is denied here too.
COMMIT_BODY_DENY_PATTERNS = list(_SHARED_DENY_PATTERNS)


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
    when false the call opens a fresh session.

    A fresh ``settings.json`` is written for each call wiring the
    PreToolUse Bash deny hook with ``MUTATOR_DENY_PATTERNS``; the
    file is removed once the call returns. The hook is the only
    runtime enforcer of the deny list — ``--dangerously-skip-permissions``
    bypasses ``--disallowedTools`` and PreToolUse hooks are the
    documented way around that.

    Wraps each call in a content-filter retry loop (max two retries)
    using the recovery prompt from ``streaming``; the retry call
    appends ``--continue`` so it resumes the same Claude session.
    Loud-fatal on a non-zero exit code or after the retry budget is
    exhausted.
    """
    settings_path = write_deny_hook_settings(MUTATOR_DENY_PATTERNS)
    try:
        cmd = build_streaming_cmd(
            model=model,
            settings_path=settings_path,
            continue_session=continue_session,
        )
        retry_cmd = build_streaming_cmd(
            model=model,
            settings_path=settings_path,
            continue_session=True,
        )
        run_claude_streaming_with_retry(
            cmd, prompt, env=build_env(), retry_cmd=retry_cmd, role="Step",
        )
    finally:
        os.unlink(settings_path)


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
        title = f"Satisfy {labels} (multi-subclause pass)"
    closes = "\n".join(f"Closes #{i}" for i in issues)
    return f"{title}\n\n{summary}\n\n{closes}\n"


def build_action_summary(
    added: list[str], modified: list[str], deleted: list[str],
) -> str:
    """Return the porcelain-derived bullet list used as the body fallback."""
    lines = (
        [f"- Added {p}" for p in sorted(added)]
        + [f"- Modified {p}" for p in sorted(modified)]
        + [f"- Deleted {p}" for p in sorted(deleted)]
    )
    return "\n".join(lines)


def build_commit_prompt(
    subclauses: list[str],
    added: list[str], modified: list[str], deleted: list[str],
) -> str:
    """Return the prompt asking Claude to explain each file change.

    Mirrors the historical ``implement_subclause`` commit-body prompt:
    every porcelain entry must produce one bullet of the form
    ``- {Verb} `path` because reason.``. The prompt requests the bullet
    list only — no preamble, no trailing text — so the result can be
    dropped into the commit body verbatim.

    The copyright reason rides on this prompt (and only this prompt)
    because the commit body is the one Claude-authored artefact that
    quotes risk reproducing LRM prose; the eight-step source-code
    prompts deliberately omit it.
    """
    label = _scope_label(subclauses)
    lines = [
        f"You just finished satisfying {label}.",
        "Git reports these file changes:\n",
    ]
    for path in sorted(added):
        lines.append(f"  Added: {path}")
    for path in sorted(modified):
        lines.append(f"  Modified: {path}")
    for path in sorted(deleted):
        lines.append(f"  Deleted: {path}")
    lines.append(
        "\nWrite a commit message body as a bullet list."
        " For each change, write one bullet explaining WHY"
        " you made that change. Use this exact format:\n"
        "\n"
        "- Modified `path` because reason.\n"
        "- Added `path` because reason.\n"
        "- Deleted `path` because reason.\n"
        "\n"
        "If an added file and a deleted file represent a move,"
        " combine them into one bullet:\n"
        "\n"
        "- Moved `TestName` from `old_path` to `new_path`"
        " because reason.\n"
        "\n"
        "Output ONLY the bullet list."
        " No preamble, no summary, no trailing text."
        f" {COPYRIGHT_REASON}",
    )
    return "\n".join(lines)


def generate_commit_body(
    subclauses: list[str],
    added: list[str], modified: list[str], deleted: list[str],
    *, model: str,
) -> str:
    """Ask Claude (resuming the eight-step session) to explain each change.

    Issues a ``--continue`` Claude call so the model that just produced
    the source-tree edits writes the matching ``- {Verb} `path` because
    reason.`` bullet for each one. The audit context Claude built in
    steps 1-2 (BNF enumeration, normative-rule list, src/tests gap
    analysis) lives in that session, so resuming is the only way the
    bullets can name the real reason for each change rather than
    inventing one from the file path alone. Returns the raw ``.result``
    text; callers fall back to ``build_action_summary`` when the result
    is blank.
    """
    prompt = build_commit_prompt(subclauses, added, modified, deleted)
    settings_path = write_deny_hook_settings(COMMIT_BODY_DENY_PATTERNS)
    try:
        cmd = build_streaming_cmd(
            model=model,
            settings_path=settings_path,
            continue_session=True,
        )
        print("\nGenerating commit message", flush=True)
        return run_claude_streaming_with_retry(
            cmd, prompt, env=build_env(),
            retry_cmd=cmd, role="Commit body",
        )
    finally:
        os.unlink(settings_path)


def _close_satisfied_issue(subclause: str, issue: int) -> None:
    """Close the GitHub issue tracking *subclause*.

    Used when the mutator produced no commit-worthy edits, which means
    §X is already satisfied (or has no normative statements of its own
    to satisfy). Without this, an empty diff would never push a
    ``Closes #N`` trailer and the issue would stay open forever.
    """
    label = format_subclause_label(subclause)
    comment = (
        f"Mutator for {label} produced no source-tree changes."
        f" {label} is already satisfied, or has no normative"
        " statements of its own to implement."
    )
    subprocess.run(
        ["gh", "issue", "close", str(issue), "--comment", comment],
        check=False,
    )


_CLANG_FORMAT_EXTENSIONS = (".cpp", ".h")


def clang_format_changed(changed: list[str]) -> None:
    """Run ``clang-format -i --style=google`` on changed C++ sources.

    The CI static-analysis gate rejects any file that is not
    google-formatted (``clang-format --dry-run --Werror --style=google``),
    and the resumed mutator session is not guaranteed to have formatted
    the code it wrote. Formatting here — immediately before the commit —
    keeps every landed commit past that gate. Non-C++ paths (``.py``,
    ``CMakeLists.txt``) are left untouched; clang-format does not apply
    to them.
    """
    cpp = [p for p in changed if p.endswith(_CLANG_FORMAT_EXTENSIONS)]
    if not cpp:
        return
    subprocess.run(
        ["clang-format", "-i", "--style=google", *cpp], check=True,
    )


def commit_mutator_result(
    subclauses: list[str], issues: list[int], *, model: str,
) -> bool:
    """Commit + push porcelain changes with a Closes trailer.

    Returns ``True`` if anything was committed, ``False`` if the working
    tree had no source-tree changes after the mutator run. In the
    no-changes case, closes each tracking issue directly via ``gh issue
    close`` so the satisfaction state is recorded on GitHub even when
    no commit lands.

    When source-tree changes exist, asks Claude (via ``--continue``) to
    write a ``- {Verb} `path` because reason.`` bullet per change so the
    commit body explains *why* each file moved — matching the historical
    ``implement_subclause`` commit-message shape. The model is forwarded
    to ``generate_commit_body`` so the resumed session uses the same
    model the pipeline ran on. Falls back to a plain porcelain-derived
    bullet list when Claude's output is blank.
    """
    added, modified, deleted = filter_changes(get_porcelain_changes())
    changed = added + modified
    if not changed and not deleted:
        for subclause, issue in zip(subclauses, issues, strict=True):
            _close_satisfied_issue(subclause, issue)
        return False
    clang_format_changed(changed)
    summary = generate_commit_body(
        subclauses, added, modified, deleted, model=model,
    ).strip()
    if not summary:
        summary = (
            build_action_summary(added, modified, deleted)
            or "- (no human-readable summary)"
        )
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
    canonical_files = _all_canonical_test_files(subclauses)
    return (
        f" Only act on requirements directly defined in the text of"
        f" {label} in the LRM — not requirements defined by"
        f" any descendant subclause of those subclauses."
        " A requirement belongs to the subclause whose LRM text defines it."
        " In this step your only action is creating, editing, or removing"
        " files on disk."
        f" Test edits land only in {label}'s canonical test files:"
        f" {canonical_files}."
        " Production-code edits land only in the source files for"
        f" {label}'s pipeline stages."
        " Leave every other file untouched — including the canonical"
        " files of other subclauses. A misfiled test in another"
        " subclause's file is that subclause's pass's problem to clean"
        " up; never reach across."
        " This step is complete when the file edits on disk"
        " land the step's deliverable."
        f" A normative statement in {label} is satisfied when"
        " production code applies the rule and a test at the same"
        " pipeline stage observes the rule being applied by that"
        " production code."
        " Pipeline stages come from the project's stage-to-file mapping;"
        " the stage where a rule applies is the stage whose source file"
        " carries the rule and whose test file covers it."
        " When the rule's behavior depends on how its input is PRODUCED"
        " — a declaration, an initializer, or a construct from one of"
        " this pass's dependency subclauses — the test shall build that"
        " input from real source syntax and drive it through the full"
        " pipeline (parse, elaborate, and, for a runtime rule, run and"
        " observe the output), rather than hand-building an intermediate"
        " state or stubbing the input with a helper. Only a rule"
        " genuinely confined to a single stage, whose behavior does not"
        " depend on how its input was produced, may use a single-stage"
        " or synthetic-context test. Building the input from a"
        " dependency's real syntax does NOT violate the scoping rule:"
        " the test still observes THIS subclause's rule and still lives"
        f" only in {label}'s canonical test files."
        f" {COPYRIGHT_REASON}"
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
    """Return the multi-subclause preface for step 1 of a multi-member run."""
    if len(subclauses) == 1:
        return ""
    label = _scope_label(subclauses)
    return (
        f"You are satisfying {label} in one pass. As you read each"
        " subclause's LRM text, look for terms, functions, or"
        " syntactic constructs that one of these subclauses uses from"
        " another. Where you find such links, weave the implementations"
        " together so a term defined in one subclause is shared with"
        " the others that use it. Where you find none, satisfy each"
        " subclause's requirements on its own.\n\n"
    )


def build_steps(
    subclauses: list[str],
    lrm: str,
    *,
    satisfied_dependencies: list[str],
) -> list[tuple[str, str]]:
    """Return the eight ``(description, prompt)`` step pairs.

    A list of one subclause produces the single-subclause pipeline; a
    list of two or more subclauses produces the multi-subclause
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
         f"First, enumerate every normative claim in the LRM text of"
         f" {label}: every BNF production (the left-hand side of a"
         " `::=` rule), every 'shall' sentence, and every other"
         " declarative requirement. For each enumerated claim, name"
         " (a) the pipeline stage the rule applies to and (b) the"
         " source file that carries the rule.\n\n"
         "Then, for each enumerated claim, also enumerate its INPUT"
         " FORMS — the distinct kinds of input the rule must handle,"
         " NOT just the one the LRM's example happens to show. Include:"
         " every operand/element data type the rule admits; every"
         " syntactic position the construct can appear in (e.g. a"
         " declaration initializer vs. a procedural assignment vs. an"
         " expression operand); and, where the rule requires a"
         " 'constant expression', each constant form of 11.2.1 (a"
         " literal, a parameter, a localparam, a genvar, a constant"
         " function call). For each claim also name its NEGATIVE form —"
         " the closest input the rule must reject — so the error path is"
         " enumerated alongside the accepting path. Finally, for each"
         " claim, name which of this pass's dependency subclauses supply"
         " constructs the rule CONSUMES (the value it operates on, the"
         " way its variable is declared or initialized): those"
         " dependencies' real syntax is how the input must be built.\n\n"
         f"Then search src/ for existing code that handles each"
         " enumerated claim. Report what aligns with the LRM and what"
         " is missing, citing the enumerated item and its input forms."
         + constraints),
        ("Auditing tests",
         f"Search {label}'s canonical test files for tests that"
         " observe each enumerated claim from the prior step."
         f" The canonical test files for {label} are: {canonical_files}."
         " Report what is covered and what is missing, citing the"
         " enumerated item."
         + constraints),
        ("Deleting duplicate tests",
         f"Among {label}'s canonical test files ({canonical_files}),"
         " delete duplicate tests within the canonical files."
         " Leave every other subclause's tests untouched, even if"
         " they look similar."
         + constraints),
        ("Deleting tests for non-normative subclauses",
         f"Re-read the LRM text of {label}. If a subclause in"
         f" {label} defines no normative rules of its own — its"
         " requirements live entirely in descendants, as is the case"
         " for introductions, overviews, roadmaps, and other"
         " purely-descriptive subclauses — delete every test in that"
         f" subclause's canonical test files. The canonical files for"
         f" {label} are: {canonical_files}."
         + constraints),
        ("Deleting empty test files",
         f"Inspect {label}'s canonical test files: {canonical_files}."
         " For any file that has no TEST(...) blocks remaining after"
         " the prior deletion steps, delete the file and"
         " remove its add_unit_test(...) entry from test/CMakeLists.txt."
         + constraints),
        ("Renaming test suites",
         f"Rename only test suites that cover {label} requirements"
         " and have unintuitive names"
         " (e.g., containing clause numbers like Cl5_7_1_),"
         f" within {label}'s canonical test files."
         " Use PascalCase names that describe what is being tested"
         " (no clause or annex numbers)."
         " Leave every other subclause's test suites untouched."
         + constraints),
        ("Renaming test names",
         f"Rename only test names that cover {label} requirements"
         " and have unintuitive names"
         " (e.g., containing clause numbers like Cl5_7_1_),"
         f" within {label}'s canonical test files."
         " Use PascalCase names that describe what is being tested"
         " (no clause or annex numbers)."
         " Leave every other subclause's tests untouched."
         + constraints),
        ("Writing missing tests",
         f"Write missing unit tests for {label} requirements,"
         " using the enumeration from the audit-src step as the"
         " checklist of what must be observed."
         f" Place them in: {canonical_files}."
         " Cover all affected pipeline stages."
         " Write one test per enumerated INPUT FORM, not just one per"
         " rule: exercise each admitted operand/element type and each"
         " syntactic position, and — for a 'constant expression'"
         " requirement — cover a literal AND a parameter (and a"
         " localparam/genvar where the rule admits them), since these"
         " take different code paths. Include the enumerated NEGATIVE"
         " form of each rule as a test that asserts the input is"
         " rejected."
         " When the audit named dependency subclauses whose constructs"
         " the rule consumes, add at least one END-TO-END test per such"
         " dependency that builds the input from that dependency's real"
         " source syntax and drives it through the full pipeline (e.g. a"
         " reduction method over a dynamic array created with a `{...}`"
         " initializer, checked via the simulated result) — do not"
         " hand-build the array or stub the intermediate state."
         " Each test exercises the production code path at the"
         " pipeline stage named by the normative statement it covers"
         " — a test is sufficient when running it would"
         " observe the rule being applied by production code, not by"
         " a reference model or helper."
         f" Skip test creation for any member of {label} that has no"
         " testable rules of its own (only its descendants do)."
         + constraints),
        ("Writing missing functionality",
         f"Working from the enumeration produced in the audit-src"
         f" step, make the source-file edits so the production code"
         " applies every normative claim. For each claim still"
         " missing implementation, name the pipeline stage the rule"
         " applies to and the source file that carries the rule, then"
         " write the code."
         f" Write or edit the source files to add any missing"
         f" functionality defined in {label}."
         f" Act only on {label}, no other subclauses."
         + constraints),
    ]


# ---------------------------------------------------------------------------
# Mutator pipeline tail
# ---------------------------------------------------------------------------

def _run_pipeline_and_commit(
    members: list[CycleMember], lrm: str,
    satisfied_dependencies: list[str], *,
    model: str, no_change_label: str,
) -> None:
    """Run the eight-step pipeline over ``members`` and commit.

    Warns to stderr when the pipeline produced no source-tree changes
    so a downstream operator can tell convergence apart from a silent
    no-op. ``no_change_label`` is the leading phrase of that warning
    (e.g. ``Mutator for §X.Y`` or ``Cycle-set mutator for [...]``).
    """
    subclauses = [m.subclause for m in members]
    issues = [m.issue for m in members]
    steps = build_steps(
        subclauses, lrm, satisfied_dependencies=satisfied_dependencies,
    )
    run_steps(steps, model=model)
    if not commit_mutator_result(subclauses, issues, model=model):
        print(
            f"{no_change_label} produced no source-tree changes;"
            " nothing committed.",
            file=sys.stderr,
        )


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
    _run_pipeline_and_commit(
        [target], lrm, [],
        model=model,
        no_change_label=f"Mutator for §{target.subclause}",
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
    _run_pipeline_and_commit(
        [target], lrm, satisfied_dependencies,
        model=model,
        no_change_label=f"Mutator for §{target.subclause}",
    )


# ---------------------------------------------------------------------------
# Mutator: cycle set
# ---------------------------------------------------------------------------

def satisfy_unsatisfied_subclause_set_with_satisfied_dependencies(
    members: list[CycleMember], lrm: str,
    satisfied_dependencies: list[str], *, model: str,
) -> None:
    """Run the eight-step pipeline for a multi-member dependency cycle.

    The eight steps run once over every member in ``members``; the
    cycle-intro preface tells Claude to weave members that share terms
    and to satisfy independent members on their own. Any cycle of two
    or more members is accepted; the model is responsible for fitting
    the bundled LRM text and code surface in its context window.
    """
    if len(members) < 2:
        raise ValueError(
            f"Cycle must have at least 2 members (got {len(members)}).",
        )
    subclauses = [m.subclause for m in members]
    issues = [m.issue for m in members]
    print(
        f"Cycle-set mutator: subclauses {subclauses},"
        f" external deps {satisfied_dependencies}, issues {issues},"
        f" model {model}",
        file=sys.stderr,
    )
    _run_pipeline_and_commit(
        members, lrm, satisfied_dependencies,
        model=model,
        no_change_label=f"Cycle-set mutator for {subclauses}",
    )
