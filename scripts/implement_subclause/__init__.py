"""LRM subclause implementation prompt generator.

Builds an optimized prompt and invokes Claude CLI.
"""

import argparse
import os
import subprocess
import sys

from lib.python.clause import STAGE_TO_PREFIX, clause_to_filename
from lib.python.lrm import build_lrm_read_instruction
from lib.python.cli import (
    add_continue_arg,
    add_lrm_arg,
    add_model_arg,
    add_subclause_arg,
    parse_and_validate_subclause,
)
from lib.python.git import (
    commit_and_push,
    get_porcelain_changes,
)
from .streaming import ContentFilterError, run_claude_streaming


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

_MAX_CONTENT_FILTER_RETRIES = 2

_DISALLOWED_TOOLS = (
    "Bash(git commit *) Bash(git push *) Bash(cmake *) "
    "Bash(make *) Bash(ninja *) Bash(ctest *) Bash(pytest *)"
)

CONTENT_FILTER_RETRY_PROMPT = (
    "Your previous response was blocked by the API content filter."
    " Please try again. Avoid reproducing LRM text verbatim —"
    " paraphrase or summarize instead. Be concise."
)


# ---------------------------------------------------------------------------
# Prompt formatting
# ---------------------------------------------------------------------------

def build_steps(
    subclause: str,
    lrm: str,
    *,
    exclude: str = "",
) -> list[tuple[str, str]]:
    """Build the list of (description, prompt) tuples for each atomic step."""
    read_ctx = build_lrm_read_instruction(subclause, lrm)

    examples = [
        clause_to_filename(prefix, subclause) + ".cpp"
        for _stage, prefix in sorted(STAGE_TO_PREFIX.items())
    ]
    filenames = ", ".join(examples)

    exclude_note = ""
    if exclude:
        excluded = [f"§{s.strip()}" for s in exclude.split(",")]
        exclude_note = (
            f"\n\nOFF-LIMITS SUBCLAUSES: {', '.join(excluded)}."
            " These descendant subclauses are handled in separate runs."
            f" Requirements defined by them belong to them,"
            f" not to §{subclause}."
            " Leave their content exactly as-is — even if you find it"
            " misplaced in another file, it is not yours to touch in"
            " this run."
        )

    constraints = (
        f" Only act on requirements directly defined in the text of"
        f" §{subclause} in the LRM — not requirements defined by"
        f" any descendant subclause (§{subclause}.1, §{subclause}.2, etc.)."
        " A requirement belongs to the subclause whose LRM text defines it."
        " In this step your only action is creating, editing, or removing"
        " files on disk."
        " This step is complete when the file edits on disk"
        " land the step's deliverable."
        f" A normative statement in §{subclause} is satisfied when"
        " production code applies the rule and a test at the same"
        " pipeline stage observes the rule being applied by that"
        " production code."
        " Pipeline stages come from the project's stage-to-file mapping;"
        " the stage where a rule applies is the stage whose source file"
        " carries the rule and whose test file covers it."
        f" When §{subclause}'s own text requires a shared type or shared"
        " code path to change, edit those shared files in this run."
        " Requirement ownership is scoped by subclause; file editing"
        f" is scoped by what §{subclause}'s text requires."
        " Write original comments; do not copy LRM prose into source files."
    )

    return [
        ("Auditing src",
         f"{read_ctx}\n\n"
         f"Then search src/ for existing code that handles §{subclause}."
         " Report what aligns with the LRM and what is missing."
         + constraints),
        ("Auditing tests",
         f"Search all files in test/src/unit/ for any tests that cover"
         f" §{subclause} requirements."
         " Tests may be misplaced in files belonging to other subclauses."
         " Report what is covered, what is missing, and any tests"
         f" found in the wrong files."
         f" The correct files for §{subclause} tests are: {filenames}."
         + constraints),
        ("Deleting duplicate tests",
         f"Delete any duplicate tests that belong to §{subclause}."
         " Do NOT delete tests that belong to other subclauses,"
         " even if they look similar."
         + exclude_note + constraints),
        ("Moving misplaced tests",
         f"Search ALL files in test/src/unit/ for tests that belong to"
         f" §{subclause}. Move any that are in the wrong files"
         f" to the correct files: {filenames}."
         " Do NOT put tests in a parent clause file."
         " If moving tests leaves a file empty, delete that file"
         " and remove its entry from test/CMakeLists.txt."
         + exclude_note + constraints),
        ("Renaming test suites",
         f"Rename any test suites that test §{subclause} requirements"
         " and have unintuitive names"
         " (e.g., containing clause numbers like Cl5_7_1_),"
         " regardless of which file they are in."
         " Use PascalCase names that describe what is being tested."
         " Do NOT include clause or annex numbers."
         " Do NOT rename or modify tests that belong to other subclauses."
         + exclude_note + constraints),
        ("Renaming test names",
         f"Rename any test names that test §{subclause} requirements"
         " and have unintuitive names"
         " (e.g., containing clause numbers like Cl5_7_1_),"
         " regardless of which file they are in."
         " Use PascalCase names that describe what is being tested."
         " Do NOT include clause or annex numbers."
         " Do NOT rename or modify tests that belong to other subclauses."
         + exclude_note + constraints),
        ("Writing missing tests",
         f"Write missing unit tests for §{subclause} requirements."
         f" Place them in: {filenames}."
         " Cover all affected pipeline stages."
         " Include error conditions and edge cases."
         " Each test exercises the production code path at the"
         " pipeline stage named by the normative statement it covers"
         " — a test is sufficient when running it would"
         " observe the rule being applied by production code, not by"
         " a reference model or helper."
         f" If §{subclause} defines no testable requirements of its own"
         " (only its descendants do), do NOT create any test files."
         + exclude_note + constraints),
        ("Writing missing functionality",
         f"First, list every normative statement in §{subclause}'s LRM"
         " text (typically 'shall' sentences, plus unambiguous"
         " declarative requirements). For each,"
         " name the pipeline stage the rule applies to and the source"
         " file that will carry the rule. Then"
         " make the source-file edits so the production code applies"
         " each rule."
         f" Write or edit the source files to add any missing functionality"
         f" defined in §{subclause}."
         f" Act only on §{subclause}, no other subclauses."
         + exclude_note + constraints),
    ]


# ---------------------------------------------------------------------------
# Claude CLI invocation
# ---------------------------------------------------------------------------

def _format_subclause_label(subclause):
    """Return display label: '§X.Y' for numeric, 'Annex X.Y' for annexes."""
    if subclause[0].isalpha():
        return f"Annex {subclause}"
    return f"§{subclause}"


def _build_env() -> dict:
    """Build a clean environment for Claude CLI subprocesses."""
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)
    return env


def run_steps(steps, *, model="opus", continue_session=False) -> list[str]:
    """Run each step as a separate Claude call.

    Streams each step's events live to the user's terminal and
    returns the list of per-step ``.result`` texts.
    """
    env = _build_env()

    total = len(steps)
    step_results: list[str] = []

    for i, (description, prompt) in enumerate(steps):
        step_num = i + 1

        cmd = [
            "claude", "-p",
            "--model", model,
            "--verbose",
            "--output-format", "stream-json",
            "--dangerously-skip-permissions",
            "--disallowedTools", _DISALLOWED_TOOLS,
        ]
        if i > 0 or continue_session:
            cmd.append("--continue")

        print(f"\nStep {step_num}/{total}: {description}", flush=True)

        retry_prompt = prompt
        attempt = 0
        while True:
            try:
                result = run_claude_streaming(cmd, retry_prompt, env=env)
                break
            except ContentFilterError:
                if attempt >= _MAX_CONTENT_FILTER_RETRIES:
                    print(
                        f"ERROR: Step {step_num} blocked by content"
                        f" filter after"
                        f" {_MAX_CONTENT_FILTER_RETRIES + 1} attempts.",
                        file=sys.stderr,
                    )
                    sys.exit(1)
                print(
                    f"WARNING: Content filter triggered on step"
                    f" {step_num} (attempt {attempt + 1}), retrying...",
                    file=sys.stderr,
                )
                if "--continue" not in cmd:
                    cmd.append("--continue")
                retry_prompt = CONTENT_FILTER_RETRY_PROMPT
                attempt += 1

        step_results.append(result)

    return step_results


_VALID_EXTENSIONS = (".cpp", ".h", ".py")
_VALID_NAMES = ("CMakeLists.txt",)


def _is_valid_path(path):
    """Return True if the path has a valid source extension."""
    return (any(path.endswith(ext) for ext in _VALID_EXTENSIONS)
            or any(path.endswith(name) for name in _VALID_NAMES))


def build_action_summary(added, modified, deleted) -> str:
    """Build a deterministic bullet list from filtered git changes."""
    bullets: list[str] = []
    for path in sorted(added):
        bullets.append(f"- Added {path}")
    for path in sorted(modified):
        bullets.append(f"- Modified {path}")
    for path in sorted(deleted):
        bullets.append(f"- Deleted {path}")
    return "\n".join(bullets)


def build_commit_prompt(subclause, added, modified, deleted) -> str:
    """Build a prompt that asks Claude to explain each file change."""
    lines = [
        f"You just finished editing source files for §{subclause}.",
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
    )
    return "\n".join(lines)


def generate_commit_body(
    subclause, changes, *, model, env,
) -> str:
    """Ask Claude to generate a commit body with 'because' explanations."""
    added, modified, deleted = changes
    prompt = build_commit_prompt(subclause, added, modified, deleted)
    cmd = [
        "claude", "-p",
        "--model", model,
        "--verbose",
        "--output-format", "stream-json",
        "--dangerously-skip-permissions",
        "--disallowedTools", _DISALLOWED_TOOLS,
        "--continue",
    ]
    print("\nGenerating commit message", flush=True)
    return run_claude_streaming(cmd, prompt, env=env)


def commit_implementation(
    subclause, issue, *, changed, deleted, action,
):
    """Commit, push, and close the issue via the commit message."""
    if not changed and not deleted:
        subprocess.run(
            ["gh", "issue", "close", str(issue), "--comment", action],
            check=True,
        )
        return

    label = _format_subclause_label(subclause)
    message = (
        f"Implement {label}\n\n{action}\n\nCloses #{issue}\n"
    )
    commit_and_push(changed, deleted, message)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args(argv=None):
    """Parse command-line arguments for clause implementation."""
    parser = argparse.ArgumentParser(
        description="Generate an implementation prompt for a given LRM clause.",
    )
    add_lrm_arg(parser)
    add_subclause_arg(parser)
    parser.add_argument(
        "--issue",
        type=int,
        required=True,
        help="GitHub Issue number to close via commit message.",
    )
    parser.add_argument(
        "--exclude",
        type=str,
        default="",
        help="Comma-separated child subclauses to exclude (handled separately).",
    )
    add_model_arg(parser)
    add_continue_arg(parser)
    return parse_and_validate_subclause(parser, argv)


def clause_depth(clause: str) -> int:
    """Return the nesting depth of a clause string."""
    return clause.count(".") + 1


def main(argv=None):
    """Parse args, run steps, and commit."""
    args = parse_args(argv)
    depth = clause_depth(args.subclause)
    print(
        f"Clause {args.subclause} (depth {depth}),"
        f" issue #{args.issue}, model {args.model}",
    )

    steps = build_steps(
        args.subclause, str(args.lrm), exclude=args.exclude,
    )
    step_results = run_steps(
        steps, model=args.model,
        continue_session=args.continue_session,
    )
    added, modified, deleted = get_porcelain_changes()
    added = [p for p in added if _is_valid_path(p)]
    modified = [p for p in modified if _is_valid_path(p)]
    deleted = [p for p in deleted if _is_valid_path(p)]
    if added or modified or deleted:
        env = _build_env()
        action = generate_commit_body(
            args.subclause, (added, modified, deleted),
            model=args.model, env=env,
        )
        if not action.strip():
            action = build_action_summary(added, modified, deleted)
    else:
        action = step_results[-1]
    print(f"Action summary:\n{action}")
    commit_implementation(
        args.subclause, args.issue,
        changed=added + modified, deleted=deleted,
        action=action,
    )
