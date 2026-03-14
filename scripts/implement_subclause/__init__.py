"""LRM subclause implementation prompt generator.

Builds an optimized prompt and invokes Claude CLI.
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path

from lib.python.classify import STAGE_TO_PREFIX, clause_to_filename
from lib.python.cli import (
    add_continue_arg,
    add_lrm_arg,
    add_model_arg,
    run_claude_cli,
    run_with_dots,
    validate_lrm,
)
from lib.python.git import (
    commit_and_push,
    get_porcelain_changes,
)


# ---------------------------------------------------------------------------
# Constants
# ---------------------------------------------------------------------------

CLAUSE_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")


# ---------------------------------------------------------------------------
# Hierarchy computation
# ---------------------------------------------------------------------------

def build_hierarchy(clause: str) -> dict:
    """Derive template variables from a clause string.

    Returns a dict with keys:
    - is_annex, subclause (always present)
    - Numeric: clause_number, ancestors
    - Annex: collection, letter, ancestors
    """
    parts = clause.split(".")
    is_annex = parts[0][0].isalpha() and parts[0][0].isupper()
    depth = len(parts)

    result = {"is_annex": is_annex, "subclause": clause}

    if is_annex:
        letter = parts[0]
        result["collection"] = f"Annex {letter}"
        result["letter"] = letter
        ancestors = []
        for k in range(2, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors
    else:
        result["clause_number"] = parts[0]
        ancestors = []
        for k in range(2, depth):
            ancestors.append(".".join(parts[:k]))
        result["ancestors"] = ancestors

    return result


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
    h = build_hierarchy(subclause)
    if h["ancestors"]:
        ancestors_str = ", ".join(f"§{a}" for a in h["ancestors"])
        read_ctx = (
            f"Read §{subclause} and its ancestor subclauses"
            f" ({ancestors_str}) in the LRM at {lrm}."
            " Also read any General or Overview subclauses at each level."
        )
    else:
        read_ctx = (
            f"Read §{subclause} in the LRM at {lrm}."
            " Also read any General or Overview sibling subclauses."
        )

    examples = [
        clause_to_filename(prefix, subclause) + ".cpp"
        for _stage, prefix in sorted(STAGE_TO_PREFIX.items())
    ]
    filenames = ", ".join(examples)

    exclude_note = ""
    if exclude:
        excluded = [f"§{s.strip()}" for s in exclude.split(",")]
        exclude_note = (
            f" {', '.join(excluded)} will be implemented separately."
            " Do NOT touch their tests or functionality."
        )

    constraints = (
        " Do not make git commits or push."
        " Do not copy LRM prose into source comments."
        " Do not build or run tests."
    )

    return [
        ("Reading LRM", read_ctx),
        ("Auditing src",
         f"Search src/ for existing code that implements §{subclause}."
         " Report what aligns with the LRM and what is missing."
         + constraints),
        ("Auditing tests",
         f"Search test/src/unit/ for existing tests that cover §{subclause}."
         f" The correct test files are: {filenames}."
         " Report what is covered and what is missing."
         + constraints),
        ("Deleting duplicate tests",
         f"Delete any duplicate tests related to §{subclause}."
         " Only delete exact duplicates."
         + constraints),
        ("Moving misplaced tests",
         f"Move any tests for §{subclause} that are in the wrong files"
         f" to the correct files: {filenames}."
         " Do NOT put tests in a parent clause file."
         + exclude_note + constraints),
        ("Renaming test suites",
         f"Rename any test suites that test §{subclause} requirements"
         " and have unintuitive names"
         " (e.g., containing clause numbers like Cl5_7_1_),"
         " regardless of which file they are in."
         " Use PascalCase names that describe what is being tested."
         " Do NOT include clause or annex numbers."
         " Do NOT rename or modify tests that belong to other subclauses."
         + constraints),
        ("Renaming test names",
         f"Rename any test names that test §{subclause} requirements"
         " and have unintuitive names"
         " (e.g., containing clause numbers like Cl5_7_1_),"
         " regardless of which file they are in."
         " Use PascalCase names that describe what is being tested."
         " Do NOT include clause or annex numbers."
         " Do NOT rename or modify tests that belong to other subclauses."
         + constraints),
        ("Implementing missing tests",
         f"Write missing unit tests for §{subclause} requirements."
         f" Place them in: {filenames}."
         " Cover all affected pipeline stages."
         " Include error conditions and edge cases."
         + exclude_note + constraints),
        ("Implementing missing functionality",
         f"Implement any missing functionality for §{subclause}."
         f" Only implement §{subclause}, no other subclauses."
         + exclude_note + constraints),
        ("Summarizing actions",
         "Output an action summary of everything you did."
         " Every line MUST include 'because' with a categorical rationale.\n"
         "ACTION_SUMMARY_START\n"
         "- Added <file> because <what was missing or needed>\n"
         "- Moved <TestName> from <file> because <why it was misplaced>\n"
         "- Deleted <file> because <why it was no longer needed>\n"
         "- Modified <file> because <what capability was missing>\n"
         "ACTION_SUMMARY_END"),
    ]


_ACTION_SUMMARY_RE = re.compile(
    r"ACTION_SUMMARY_START\n(.*?)\nACTION_SUMMARY_END",
    re.DOTALL,
)


def _extract_action_summary(text: str) -> str:
    """Extract the action summary block from Claude's response text."""
    m = _ACTION_SUMMARY_RE.search(text)
    return m.group(1).strip() if m else ""


def _parse_action_summary(stdout: str) -> str:
    """Search raw stdout and the JSON envelope result for ACTION_SUMMARY."""
    summary = _extract_action_summary(stdout)
    if not summary:
        summary = _extract_action_summary(stdout.replace("\\n", "\n"))
    if not summary:
        try:
            envelope = json.loads(stdout)
            if isinstance(envelope, list):
                for item in reversed(envelope):
                    if isinstance(item, dict) and "result" in item:
                        envelope = item
                        break
            if isinstance(envelope, dict) and "result" in envelope:
                summary = _extract_action_summary(envelope["result"])
        except (json.JSONDecodeError, TypeError):
            pass
    return summary


# ---------------------------------------------------------------------------
# Claude CLI invocation
# ---------------------------------------------------------------------------

def _format_subclause_label(subclause):
    """Return display label: '§X.Y' for numeric, 'Annex X.Y' for annexes."""
    if subclause[0].isalpha():
        return f"Annex {subclause}"
    return f"§{subclause}"


def run_steps(steps, *, model="opus",
              continue_session=False) -> str:
    """Run each step as a separate Claude call, return ACTION_SUMMARY."""
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    total = len(steps)
    summary = ""

    for i, (description, prompt) in enumerate(steps):
        step_num = i + 1
        use_continue = continue_session if i == 0 else True

        cmd = [
            "claude", "-p",
            "--model", model,
            "--effort", "high",
            "--verbose",
            "--output-format", "json",
            "--dangerously-skip-permissions",
        ]
        if use_continue:
            cmd.append("--continue")

        print(f"Step {step_num}/{total}: {description}...",
              end="", flush=True)

        result = run_with_dots(run_claude_cli, cmd, prompt, env=env)

        if result.returncode != 0:
            print(
                f"\nERROR: Step {step_num} failed"
                f" (code {result.returncode})",
                file=sys.stderr,
            )
            sys.exit(1)

        if step_num == total:
            summary = _parse_action_summary(result.stdout)
            if not summary:
                print("ERROR: Final step did not produce"
                      " an ACTION_SUMMARY.", file=sys.stderr)
                sys.exit(1)

    return summary


def commit_implementation(subclause, issue, *, action=""):
    """Commit, push, and close the issue via the commit message."""
    added, modified, deleted = get_porcelain_changes()
    label = _format_subclause_label(subclause)

    parts = [f"Implement {label}"]
    if action:
        parts.append(action)
    parts.append(f"Closes #{issue}")
    message = "\n\n".join(parts) + "\n"
    commit_and_push(added + modified, deleted, message)


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args(argv=None):
    """Parse command-line arguments for clause implementation."""
    parser = argparse.ArgumentParser(
        description="Generate an implementation prompt for a given LRM clause.",
    )
    add_lrm_arg(parser)
    parser.add_argument(
        "--subclause",
        type=str,
        required=True,
        help="LRM subclause number (V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z).",
    )
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
    args = parser.parse_args(argv)

    validate_lrm(parser, args)

    if not CLAUSE_RE.match(args.subclause):
        parser.error(
            f"Invalid subclause format '{args.subclause}'. "
            "Expected V, V.W, V.W.X, V.W.X.Y, or V.W.X.Y.Z "
            "(V is a number or uppercase letter; remaining parts are numbers)."
        )

    return args


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
    action = run_steps(
        steps, model=args.model,
        continue_session=args.continue_session,
    )
    print(f"Action summary:\n{action}")
    commit_implementation(args.subclause, args.issue, action=action)
