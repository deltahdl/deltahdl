"""LRM subclause implementation prompt generator.

Builds an optimized prompt and invokes Claude CLI.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

from lib.python.classify import (
    STAGE_TO_PREFIX, build_lrm_read_instruction, clause_to_filename,
)
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

_RATIONALE_RE = re.compile(
    r"RATIONALE:\s*(.*?)\s*IMPLEMENTABLE:\s*(yes|no)\b",
    re.IGNORECASE | re.DOTALL,
)


@dataclass
class NotImplementable:
    """Sentinel returned by run_steps when Step 2 verdicts a subclause as
    not implementable. Carries the rationale Claude was forced to articulate
    so the close-issue comment can preserve it for human review."""

    rationale: str




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
            " These are descendant subclauses that will be implemented"
            f" separately. Requirements defined by these subclauses"
            f" belong to THEM, not to §{subclause}."
            " Do NOT implement, move, delete, rename, or otherwise"
            " act on their content — even if you find it misplaced"
            " in other files. Leave it exactly as-is."
        )

    constraints = (
        f" Only act on requirements directly defined in the text of"
        f" §{subclause} in the LRM — not requirements defined by"
        f" any descendant subclause (§{subclause}.1, §{subclause}.2, etc.)."
        " A requirement belongs to the subclause whose LRM text defines it."
        " Do not make git commits or push."
        " Do not copy LRM prose into source comments."
        " Do not build or run tests."
    )

    return [
        ("Reading LRM", read_ctx),
        ("Checking implementability",
         f"Does §{subclause} define any requirements that can be"
         " implemented as software (syntax to parse, semantics to"
         " simulate, behavior to enforce, constraints to check)?"
         " A subclause that merely introduces a topic or provides"
         " a general overview without any concrete requirements"
         " is NOT implementable. A subclause that defines concrete"
         " items (e.g., which methods exist, which formats are valid)"
         " IS implementable even if it references other sections"
         " for additional details."
         " A subclause that makes concrete statements — not merely"
         " introducing a topic for its child subclauses — IS"
         " implementable."
         " A subclause that defines classifications, properties, or"
         " distinctions (e.g., 'X is a Y', 'X has property Z') IS"
         " implementable — those are testable definitional claims"
         " even if the text is short."
         " If existing tests under test/src/unit/ already cover"
         f" §{subclause}, that is by itself sufficient evidence"
         " the subclause is implementable.\n\n"
         "Respond in EXACTLY this format and nothing else:\n\n"
         "RATIONALE: <2-6 sentences citing specific language from"
         f" §{subclause} that does or does not impose testable"
         " requirements. If you claim the section is overview-only,"
         " you must quote the wording that convinces you of that.>\n"
         "IMPLEMENTABLE: yes\n\n"
         "(or `IMPLEMENTABLE: no` after the rationale).\n\n"
         "Writing the rationale is mandatory — a response missing"
         " the RATIONALE: line will be rejected. Use the rationale"
         " to check your own answer: if you cannot articulate why,"
         " you do not yet know the answer."),
        ("Auditing src",
         f"Search src/ for existing code that implements §{subclause}."
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
        ("Implementing missing tests",
         f"Write missing unit tests for §{subclause} requirements."
         f" Place them in: {filenames}."
         " Cover all affected pipeline stages."
         " Include error conditions and edge cases."
         f" If §{subclause} defines no testable requirements of its own"
         " (only its descendants do), do NOT create any test files."
         + exclude_note + constraints),
        ("Implementing missing functionality",
         f"Implement any missing functionality for §{subclause}."
         f" Only implement §{subclause}, no other subclauses."
         + exclude_note + constraints),
        ("Auditing scope",
         f"Run git diff and review every change you made."
         f" For each change, verify it acts on content defined by"
         f" §{subclause} in the LRM — not content defined by any"
         f" descendant subclause."
         f" If you find any change that acts on descendant content,"
         f" revert it with git checkout."
         + exclude_note + constraints),
        ("Summarizing actions",
         "Summarize everything you did as a self-contained bullet list."
         " Do NOT say 'see above' or refer to prior responses —"
         " produce the full list here."
         " Every line MUST include 'because' with a categorical"
         " rationale. Example format:\n"
         "- Added <file> because <reason>\n"
         "- Moved <TestName> from <file> because <reason>\n"
         "- Deleted <file> because <reason>\n"
         "- Modified <file> because <reason>\n\n"
         "Before finalizing, run git diff --stat and only include"
         " actions that correspond to actual file changes."
         " Remove any claims not backed by the diff."),
    ]


def _extract_result_text(stdout: str) -> str:
    """Extract the result text from Claude's JSON envelope."""
    try:
        envelope = json.loads(stdout)
        if isinstance(envelope, list):
            for item in reversed(envelope):
                if isinstance(item, dict) and "result" in item:
                    return item["result"]
        if isinstance(envelope, dict) and "result" in envelope:
            return envelope["result"]
    except (json.JSONDecodeError, TypeError):
        pass
    return stdout.strip()


# ---------------------------------------------------------------------------
# Claude CLI invocation
# ---------------------------------------------------------------------------

def _format_subclause_label(subclause):
    """Return display label: '§X.Y' for numeric, 'Annex X.Y' for annexes."""
    if subclause[0].isalpha():
        return f"Annex {subclause}"
    return f"§{subclause}"


def _parse_implementability(stdout: str) -> tuple[str, str]:
    """Parse a Step 2 response into (verdict, rationale).

    The verdict is the lowercase 'yes' or 'no' value of the IMPLEMENTABLE
    field. The rationale is the RATIONALE field text. Raises ValueError
    when either field is missing — Step 2 has a strict contract and a
    malformed response must not silently degrade into a 'no' verdict.
    """
    text = _extract_result_text(stdout)
    match = _RATIONALE_RE.search(text)
    if not match:
        raise ValueError(
            "Step 2 response is missing the required"
            " 'RATIONALE: <text>\\nIMPLEMENTABLE: yes|no' format."
            f" Got: {text!r}"
        )
    rationale = match.group(1).strip()
    verdict = match.group(2).strip().lower()
    if not rationale:
        raise ValueError("Step 2 response had an empty RATIONALE.")
    return verdict, rationale


def run_steps(steps, *, model="opus",
              continue_session=False) -> "str | NotImplementable":
    """Run each step as a separate Claude call, return summary text."""
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    total = len(steps)
    summary = ""
    skip_to_summary = False
    not_implementable_rationale: str | None = None

    for i, (description, prompt) in enumerate(steps):
        step_num = i + 1

        if skip_to_summary and step_num < total:
            continue

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

        if step_num == 2:
            try:
                verdict, rationale = _parse_implementability(result.stdout)
            except ValueError as exc:
                print(f"\nERROR: {exc}", file=sys.stderr)
                sys.exit(1)
            if verdict == "no":
                print(f"Not implementable — {rationale}")
                not_implementable_rationale = rationale
                skip_to_summary = True

        if step_num == total:
            summary = _extract_result_text(result.stdout)

    if not_implementable_rationale is not None:
        return NotImplementable(rationale=not_implementable_rationale)
    return summary


_VALID_EXTENSIONS = (".cpp", ".h", ".py")
_VALID_NAMES = ("CMakeLists.txt",)


def _is_valid_path(path):
    """Return True if the path has a valid source extension."""
    return (any(path.endswith(ext) for ext in _VALID_EXTENSIONS)
            or any(path.endswith(name) for name in _VALID_NAMES))


def commit_implementation(subclause, issue, *, action=""):
    """Commit, push, and close the issue via the commit message."""
    added, modified, deleted = get_porcelain_changes()
    added = [p for p in added if _is_valid_path(p)]
    modified = [p for p in modified if _is_valid_path(p)]
    deleted = [p for p in deleted if _is_valid_path(p)]

    if not added and not modified and not deleted:
        subprocess.run(
            ["gh", "issue", "close", str(issue),
             "--comment", action or "No changes needed."],
            check=True,
        )
        return

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
    if isinstance(action, NotImplementable):
        print("Not implementable — closing issue.")
        comment = (
            "Deemed not implementable.\n\n"
            f"Rationale:\n{action.rationale}"
        )
        subprocess.run(
            ["gh", "issue", "close", str(args.issue), "--comment", comment],
            check=True,
        )
        return
    print(f"Action summary:\n{action}")
    commit_implementation(args.subclause, args.issue, action=action)
