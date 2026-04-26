"""Shared infrastructure for the satisfaction-pipeline mutators.

Mutator scripts read a ``SubclauseDiagnostic`` from disk (the JSON the
oracle emitted), invoke Claude with the editing tools enabled, and
commit any working-tree changes with a ``Closes #N`` trailer. The three
mutator variants (no deps, with satisfied deps, cycle-set) differ only
in what context they hand to Claude — the diagnostic loading, Claude
invocation, porcelain-change scan, and commit are all shared here.
"""

import argparse
import json
import subprocess
import sys
from dataclasses import asdict
from pathlib import Path

from lib.python.cli import (
    add_lrm_arg,
    add_model_arg,
    add_subclause_arg,
)
from lib.python.git import commit_and_push, get_porcelain_changes
from lib.python.github import format_subclause_label
from lib.python.satisfy import SATISFACTION_CONDITIONS, SubclauseDiagnostic
from lib.python.satisfy.oracle import build_env


# Mutators may edit source and test files but must never run git, gh,
# build tools, or destructive shell commands directly. The orchestrator
# owns the commit and the CI-equivalent gates.
MUTATOR_DISALLOWED_TOOLS = (
    "Bash(git *) Bash(gh *)"
    " Bash(rm *) Bash(mv *) Bash(cp *)"
    " Bash(cmake *) Bash(make *) Bash(ninja *)"
    " Bash(ctest *) Bash(pytest *)"
)


# ---------------------------------------------------------------------------
# CLI helpers
# ---------------------------------------------------------------------------

def add_diagnostic_file_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--diagnostic-file`` argument to *parser*."""
    parser.add_argument(
        "--diagnostic-file",
        type=Path,
        required=True,
        help="Path to the SubclauseDiagnostic JSON file from the oracle.",
    )


def add_issue_arg(parser: argparse.ArgumentParser) -> None:
    """Add the ``--issue`` argument to *parser*."""
    parser.add_argument(
        "--issue",
        type=int,
        required=True,
        help="GitHub issue number for the commit's Closes trailer.",
    )


def add_dependencies_arg(parser: argparse.ArgumentParser) -> None:
    """Add the optional ``--satisfied-dependencies`` argument."""
    parser.add_argument(
        "--satisfied-dependencies",
        type=str,
        default="",
        help=(
            "Comma-separated list of subclauses already satisfied earlier"
            " in the recursion (passed by the orchestrator)."
        ),
    )


# ---------------------------------------------------------------------------
# Diagnostic loading
# ---------------------------------------------------------------------------

def load_diagnostic(path: Path) -> SubclauseDiagnostic:
    """Load a ``SubclauseDiagnostic`` JSON document from *path*."""
    payload = json.loads(path.read_text(encoding="utf-8"))
    fields = {}
    for condition in SATISFACTION_CONDITIONS:
        if condition not in payload:
            raise ValueError(
                f"Diagnostic file missing condition: {condition}",
            )
        fields[condition] = payload[condition]
    return SubclauseDiagnostic(**fields)


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


def parse_satisfied_dependencies(raw: str) -> list[str]:
    """Split a comma-separated list of subclause identifiers."""
    if not raw:
        return []
    return [item.strip() for item in raw.split(",") if item.strip()]


# ---------------------------------------------------------------------------
# Claude invocation
# ---------------------------------------------------------------------------

def run_mutator_call(prompt: str, *, model: str) -> None:
    """Invoke Claude with mutator tools enabled.

    Streams Claude's stdout/stderr to the user's terminal directly
    rather than capturing them — the user wants to see file edits as
    they happen. Loud-fatal on a non-zero exit code.
    """
    cmd = [
        "claude", "-p",
        "--model", model,
        "--dangerously-skip-permissions",
        "--disallowedTools", MUTATOR_DISALLOWED_TOOLS,
    ]
    completed = subprocess.run(
        cmd, input=prompt, text=True,
        env=build_env(), check=False,
    )
    if completed.returncode != 0:
        print(
            f"Mutator Claude call exited with code {completed.returncode}",
            file=sys.stderr,
        )
        sys.exit(completed.returncode)


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
# Single-subclause mutator entry point
# ---------------------------------------------------------------------------

def build_mutator_parser(description: str) -> argparse.ArgumentParser:
    """Return a parser pre-wired with all single-subclause mutator args."""
    parser = argparse.ArgumentParser(description=description)
    add_lrm_arg(parser)
    add_subclause_arg(parser)
    add_diagnostic_file_arg(parser)
    add_issue_arg(parser)
    add_model_arg(parser)
    return parser
