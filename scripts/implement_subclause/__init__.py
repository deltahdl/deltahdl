"""LRM subclause implementation prompt generator.

Builds an optimized prompt and invokes Claude CLI.
"""

import argparse
import json
import os
import re
import subprocess
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
    get_remote_repo,
)
from lib.python.github import (
    fetch_issue_body,
    format_subclause_label,
    update_issue_body,
    update_subclause_status,
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
        " rename BOTH the suite name AND the test name to PascalCase"
        " names that intuitively describe what is being tested."
        " Do NOT include clause or annex numbers in suite or test names.",
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
        "If existing tests already cover this subclause, do NOT pick"
        " 'Deemed not implementable'. A subclause with existing tests"
        " was already implemented.",
    )

    lines.append(
        "At the very end of your response, output an action summary."
        " Every line MUST include 'because' with a categorical rationale"
        " explaining why the action was necessary"
        " (what was missing, wrong, or misplaced).\n"
        "ACTION_SUMMARY_START\n"
        "- Added <file> because <what was missing or needed>\n"
        "- Moved <TestName> from <file> because <why it was misplaced>\n"
        "- Deleted <file> because <why it was no longer needed>\n"
        "- Modified <file> because <what capability was missing>\n"
        "ACTION_SUMMARY_END\n"
        "Then pick EXACTLY ONE of these predefined actions:\n"
        "- Added tests only because the functionality was already"
        " implemented but its tests were missing\n"
        "- Deemed not implementable\n"
        "- Did nothing because the functionality and its tests"
        " were already implemented\n"
        "- Implemented the functionality and its tests"
        " because both were missing\n"
        "- Only deleted tests because the subclause's functionalities"
        " and its tests were already implemented but some tests"
        " were duplicated\n"
        "- Only reclassified tests because the subclause's"
        " functionalities and its tests were already implemented"
        " but the tests were misclassified\n"
        "- Only renamed tests because the subclause's functionalities"
        " and its tests were already implemented but the tests"
        " were improperly named\n"
        "- Performed a non-predefined action\n"
        "Output your choice as:\n"
        "ONE_LINE_PREDEFINED_ACTION: <your choice>",
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


_PREDEFINED_ACTIONS = [
    "Added tests only because the functionality was already"
    " implemented but its tests were missing",
    "Deferred via --exclude",
    "Deemed not implementable",
    "Did nothing because the functionality and its tests"
    " were already implemented",
    "Implemented the functionality and its tests"
    " because both were missing",
    "Only deleted tests because the subclause's functionalities"
    " and its tests were already implemented but some tests"
    " were duplicated",
    "Only reclassified tests because the subclause's"
    " functionalities and its tests were already implemented"
    " but the tests were misclassified",
    "Only renamed tests because the subclause's functionalities"
    " and its tests were already implemented but the tests"
    " were improperly named",
    "Performed a non-predefined action",
]


def _extract_predefined_action(text: str) -> str:
    """Extract the ONE_LINE_PREDEFINED_ACTION from Claude's response."""
    for action in _PREDEFINED_ACTIONS:
        if action in text:
            return action
    return ""


def _parse_action_summary(stdout: str) -> str:
    """Search raw stdout and the JSON envelope result for ACTION_SUMMARY."""
    summary = _extract_action_summary(stdout)
    if not summary:
        try:
            envelope = json.loads(stdout)
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


def invoke_claude(
    prompt: str, *, subclause: str,
    model: str = "opus", continue_session: bool = False,
) -> tuple[str, str]:
    """Invoke Claude CLI and return ``(action_summary, predefined_action)``.

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

    label = _format_subclause_label(subclause)
    print(f"Implementing {label} via Claude...", end="", flush=True)

    result = run_with_dots(run_claude_cli, cmd, prompt, env=env)

    if result.returncode != 0:
        print(
            f"\nERROR: Claude exited with code {result.returncode}",
            file=sys.stderr,
        )
        sys.exit(1)

    summary = _parse_action_summary(result.stdout)
    retry_result = None
    if not summary:
        print("Retrying for ACTION_SUMMARY...", file=sys.stderr)
        retry_cmd = ["claude", "-p", "--model", model,
                     "--output-format", "json",
                     "--dangerously-skip-permissions", "--continue"]
        retry_result = run_claude_cli(
            retry_cmd,
            "You did not provide an ACTION_SUMMARY block."
            " Output one now using this exact format:\n"
            "ACTION_SUMMARY_START\n"
            "- <action> because <rationale>\n"
            "ACTION_SUMMARY_END\n"
            "ONE_LINE_PREDEFINED_ACTION: <one of the predefined actions>",
            env=env,
        )
        if retry_result.returncode == 0:
            summary = _parse_action_summary(retry_result.stdout)
    if not summary:
        print("ERROR: Claude did not provide an ACTION_SUMMARY"
              " after retry.", file=sys.stderr)
        sys.exit(1)

    predefined = _extract_predefined_action(result.stdout)
    if not predefined and retry_result:
        predefined = _extract_predefined_action(retry_result.stdout)
    if not predefined:
        predefined = "Performed a non-predefined action"

    return summary, predefined


def commit_implementation(subclause, issue, *,
                          action="", predefined_action=""):
    """Commit, push, and mark the subclause complete on the issue."""
    added, modified, deleted = get_porcelain_changes()
    label = _format_subclause_label(subclause)

    if action:
        message = f"Implement {label}\n\n{action}\n"
    else:
        message = f"Implement {label}\n"
    sha = commit_and_push(added + modified, deleted, message)
    if predefined_action:
        organization, repo = get_remote_repo()
        commit_url = ""
        if sha:
            commit_url = (
                f"https://github.com/{organization}/{repo}/commit/{sha}"
            )
        body = fetch_issue_body(organization, repo, issue)
        table_label = format_subclause_label(subclause)
        body = update_subclause_status(
            body, table_label, "Reviewed",
            action=predefined_action, commit_url=commit_url,
        )
        update_issue_body(organization, repo, issue, body)


def run_prompt(build_fn, args: argparse.Namespace) -> tuple[str, str]:
    """Build a prompt via *build_fn*, invoke Claude, return (summary, predefined_action)."""
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

    action, predefined_action = run_prompt(build_prompt, args)
    print(f"Action summary:\n{action}")
    print(f"Predefined action: {predefined_action}")
    commit_implementation(
        args.subclause, args.issue,
        action=action, predefined_action=predefined_action,
    )
