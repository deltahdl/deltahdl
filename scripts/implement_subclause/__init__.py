"""LRM subclause implementation prompt generator.

Builds an optimized prompt and invokes Claude CLI.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import threading
from pathlib import Path

from lib.python.classify import STAGE_TO_PREFIX, clause_to_filename
from lib.python.cli import (
    add_continue_arg,
    add_lrm_arg,
    add_model_arg,
    run_claude_cli,
    validate_lrm,
)
from lib.python.git import commit_and_push, get_remote_repo, run_git
from lib.python.github import mark_subclause_complete


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

def format_prompt(
    subclause: str,
    lrm: str,
    *,
    exclude: str = "",
) -> str:
    """Assemble the implementation prompt from structured inputs."""
    h = build_hierarchy(subclause)
    lines = [f"Implement §{subclause} from the LRM at {lrm}.\n"]

    if h["ancestors"]:
        ancestors_str = ", ".join(f"§{a}" for a in h["ancestors"])
        lines.append(
            f"Read §{subclause} and its ancestor subclauses"
            f" ({ancestors_str}) for context."
            " Also read any General or Overview subclauses"
            " at each level.",
        )
    else:
        lines.append(
            f"Read §{subclause} for context."
            " Also read any General or Overview sibling subclauses.",
        )

    lines.append(
        "Search the codebase for existing related code"
        " before writing anything new.",
    )

    lines.append(
        "Search test/src/unit/ for any existing tests"
        f" that cover §{subclause} requirements."
        " If found in files other than the ones listed below,"
        " move them to the correct file.",
    )

    lines.append(
        "If any pre-existing tests have unintuitive suite or test names"
        " (e.g., names containing clause numbers like Cl5_7_1_),"
        " rename them to PascalCase names that intuitively describe"
        " what the test exercises."
        " Do NOT include clause or annex numbers in test names.",
    )

    lines.append(
        "Use strict test-driven development:"
        f" for each requirement in §{subclause},"
        " write a failing unit test, then implement."
        " Cover all affected pipeline stages."
        " Include error conditions and edge cases.",
    )

    lines.append(
        f"Only implement §{subclause}."
        " Do not implement any other subclauses.",
    )

    if exclude:
        excluded = [f"§{s.strip()}" for s in exclude.split(",")]
        lines.append(
            f"{', '.join(excluded)} will be implemented separately."
            " Do NOT implement their requirements."
            " Do NOT place tests for them in your files."
            f" Only implement requirements stated directly in §{subclause}.",
        )

    examples = [
        clause_to_filename(prefix, subclause) + ".cpp"
        for _stage, prefix in sorted(STAGE_TO_PREFIX.items())
    ]
    lines.append(
        "Place tests in the subclause-specific test file."
        f" The correct filenames by stage are: {', '.join(examples)}."
        " Do NOT put tests in a parent clause file.",
    )

    lines.append("Do not make git commits or push.")
    lines.append("Do not copy LRM prose into source comments.")
    lines.append("Do not build or run tests.")

    lines.append(
        "At the very end of your response, output an action summary"
        " describing all actions you took and why, using this format:\n"
        "ACTION_SUMMARY_START\n"
        "- Added <file> with <N> new tests for <feature>\n"
        "- Moved <TestName> from <source_file> (belongs under this subclause)\n"
        "- Deleted <file> (tests consolidated into <target_file>)\n"
        "- Modified <file> to support <feature>\n"
        "ACTION_SUMMARY_END",
    )

    return "\n".join(lines) + "\n"


def build_prompt(
    clause: str,
    lrm: str,
    *,
    exclude: str = "",
) -> str:
    """Build the implementation prompt for any clause depth."""
    return format_prompt(clause, lrm, exclude=exclude)


_ACTION_SUMMARY_RE = re.compile(
    r"ACTION_SUMMARY_START\n(.*?)\nACTION_SUMMARY_END",
    re.DOTALL,
)


def _extract_action_summary(text: str) -> str:
    """Extract the action summary block from Claude's response text."""
    m = _ACTION_SUMMARY_RE.search(text)
    return m.group(1).strip() if m else ""


# ---------------------------------------------------------------------------
# Claude CLI invocation
# ---------------------------------------------------------------------------

_DOT_INTERVAL_SECONDS = 5


def invoke_claude(
    prompt: str, *, subclause: str,
    model: str = "opus", continue_session: bool = False,
) -> str:
    """Invoke Claude CLI and return the extracted action summary.

    Uses ``--output-format json`` so the response can be parsed for the
    ACTION_SUMMARY block.  Returns the action summary string, or ``""``
    if none was found.
    """
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    cmd = [
        "claude", "-p",
        "--model", model,
        "--effort", "high",
        "--verbose",
        "--output-format", "json",
        "--dangerously-skip-permissions",
    ]

    if continue_session:
        cmd.append("--continue")

    prefix = f"Annex {subclause}" if subclause[0].isalpha() else f"§{subclause}"
    print(f"Implementing {prefix} via Claude...", end="", flush=True)

    stop = threading.Event()

    def _print_dots():
        while not stop.wait(_DOT_INTERVAL_SECONDS):
            print(".", end="", flush=True)

    dot_thread = threading.Thread(target=_print_dots, daemon=True)
    dot_thread.start()
    result = run_claude_cli(cmd, prompt, env=env)
    stop.set()
    dot_thread.join()
    print()  # newline after dots

    if result.returncode != 0:
        print(
            f"\nERROR: Claude exited with code {result.returncode}",
            file=sys.stderr,
        )
        sys.exit(1)

    text = ""
    try:
        envelope = json.loads(result.stdout)
        if isinstance(envelope, dict) and "result" in envelope:
            text = envelope["result"]
    except (json.JSONDecodeError, TypeError):
        pass

    return _extract_action_summary(text)


def get_unstaged_files():
    """Return (changed, deleted) file lists from git status --porcelain."""
    result = run_git(["git", "status", "--porcelain"])
    changed = []
    deleted = []
    for line in result.stdout.splitlines():
        if not line:
            continue
        status = line[:2]
        path = line[3:]
        if status.strip() == "D":
            deleted.append(path)
        else:
            changed.append(path)
    return changed, deleted


def commit_implementation(subclause, issue, *, action=""):
    """Commit, push, and mark the subclause complete on the issue."""
    changed, deleted = get_unstaged_files()
    trailer = "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>"
    if action:
        message = f"Implement §{subclause}\n\n{action}\n\n{trailer}\n"
    else:
        message = f"Implement §{subclause}\n\n{trailer}\n"
    sha = commit_and_push(changed, deleted, message)
    if sha:
        organization, repo = get_remote_repo()
        mark_subclause_complete(organization, repo, issue, subclause, sha)


def run_prompt(build_fn, args: argparse.Namespace) -> str:
    """Build a prompt via *build_fn*, invoke Claude, return action summary."""
    prompt = build_fn(
        args.subclause, str(args.lrm), exclude=args.exclude,
    )
    print(f"Built prompt ({len(prompt)} characters)")
    return invoke_claude(
        prompt, subclause=args.subclause,
        model=args.model,
        continue_session=args.continue_session,
    )


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
        help="GitHub Issue number to read and correct after implementation.",
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
    """Parse args, build prompt, and invoke Claude."""
    args = parse_args(argv)
    depth = clause_depth(args.subclause)
    print(
        f"Clause {args.subclause} (depth {depth}),"
        f" issue #{args.issue}, model {args.model}",
    )

    action = run_prompt(build_prompt, args)
    if action:
        print(f"Action summary:\n{action}")
    commit_implementation(args.subclause, args.issue, action=action)
