"""LRM subclause implementation prompt generator.

Builds an optimized prompt and invokes Claude CLI.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
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

_FENCE_RE = re.compile(r"```(?:json)?\s*\n?(.*?)\n?```", re.DOTALL)


@dataclass
class NotImplementable:
    """Sentinel returned by run_steps when Step 2 verdicts a subclause as
    not implementable. Carries the rationale Claude was forced to articulate
    plus the (empty) evidence list so the close-issue comment can preserve
    both for human review."""

    rationale: str
    evidence: list[dict[str, str]] = field(default_factory=list)




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

    step2_prompt = (
        f"{read_ctx}\n\n"
        f"Then find every passage in §{subclause} that"
        " imposes a constraint, defines a structure, classifies an"
        " entity, specifies a syntax, prescribes a behavior, or"
        " otherwise makes a concrete claim that software could be"
        " written to check or implement against. Each such passage"
        " is a piece of testable evidence.\n\n"
        "Respond with EXACTLY this JSON object and nothing else"
        " (no markdown fence, no surrounding prose):\n\n"
        "{\n"
        '  "evidence": [\n'
        '    {\n'
        '      "quote": "<verbatim sentence or passage from the spec>",\n'
        '      "why_testable": "<one sentence: what software could'
        ' check or implement against this>"\n'
        '    }\n'
        '  ],\n'
        '  "verdict": "yes",\n'
        '  "rationale": "<2-6 sentences>"\n'
        "}\n\n"
        "Rules:\n"
        "- The schema is taxonomy-free. Whatever shape the"
        " specification takes — `shall` clauses, MUST/SHOULD in RFC"
        " 2119 terms, formal grammar productions, state machines,"
        " type rules, timing diagrams, packet layouts — qualifying"
        " passages all land in the same `evidence` list.\n"
        "- Quote each passage verbatim from the spec.\n"
        "- Do NOT dismiss concrete language as 'merely introductory'"
        " or 'merely definitional'. A definition is itself a testable"
        " claim if software can be written to recognize the entity"
        " it defines.\n"
        "- If `evidence` is non-empty, `verdict` MUST be `yes`.\n"
        "- Form the verdict only AFTER enumerating evidence, never"
        " before.\n"
        "- If existing tests under test/src/unit/ already cover"
        f" §{subclause}, that alone is sufficient: add an evidence"
        " entry quoting the LRM line or block they exercise and set"
        " `verdict` to `yes`.\n"
        "- `verdict` must be the literal string `yes` or `no`.\n"
        "- `rationale` must be a non-empty string."
    )
    return [
        ("Checking implementability", step2_prompt),
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


def _strip_fence(text: str) -> str:
    """Strip a single Markdown fenced code block, if present."""
    match = _FENCE_RE.search(text)
    if match:
        return match.group(1).strip()
    return text.strip()


def _validate_evidence_item(item: object) -> None:
    """Raise ValueError unless ``item`` is a valid evidence object."""
    if not isinstance(item, dict):
        raise ValueError(
            "Step 2 evidence items must be JSON objects with"
            " 'quote' and 'why_testable' fields."
        )
    for key in ("quote", "why_testable"):
        if key not in item:
            raise ValueError(
                f"Step 2 evidence item missing required key {key!r}."
            )


def _validate_step2_envelope(data: object) -> None:
    """Raise ValueError unless ``data`` matches the Step 2 schema."""
    if not isinstance(data, dict):
        raise ValueError("Step 2 response must be a JSON object.")
    for key in ("evidence", "verdict", "rationale"):
        if key not in data:
            raise ValueError(
                f"Step 2 response missing required key {key!r}."
            )
    if not isinstance(data["evidence"], list):
        raise ValueError("Step 2 'evidence' must be a list.")
    for item in data["evidence"]:
        _validate_evidence_item(item)
    if data["verdict"] not in ("yes", "no"):
        raise ValueError(
            "Step 2 'verdict' must be 'yes' or 'no';"
            f" got {data['verdict']!r}."
        )
    if (not isinstance(data["rationale"], str)
            or not data["rationale"].strip()):
        raise ValueError(
            "Step 2 'rationale' must be a non-empty string."
        )


def _parse_implementability(
    stdout: str,
) -> tuple[str, str, list[dict[str, str]]]:
    """Parse a Step 2 JSON response into ``(verdict, rationale, evidence)``.

    Applies the deterministic override: if ``evidence`` is non-empty and
    the model's ``verdict`` is ``"no"``, the verdict is flipped to
    ``"yes"`` and the rationale is annotated with the override and the
    model's original rationale. Raises ``ValueError`` on any schema
    violation — Step 2 has a strict contract and a malformed response
    must not silently degrade into a ``"no"`` verdict.
    """
    text = _strip_fence(_extract_result_text(stdout))
    try:
        data = json.loads(text)
    except json.JSONDecodeError as exc:
        raise ValueError(
            f"Step 2 response is not valid JSON: {exc.msg}"
        ) from exc
    _validate_step2_envelope(data)
    evidence = data["evidence"]
    verdict = data["verdict"]
    rationale = data["rationale"]
    if evidence and verdict == "no":
        verdict = "yes"
        rationale = (
            f"OVERRIDE: model returned 'no' but enumerated"
            f" {len(evidence)} testable evidence item(s);"
            f" verdict flipped to 'yes'."
            f" Original rationale: {rationale}"
        )
    return verdict, rationale, evidence


def _handle_step2(stdout: str) -> "NotImplementable | None":
    """Parse the step 2 response; return a sentinel if not implementable."""
    try:
        verdict, rationale, evidence = _parse_implementability(stdout)
    except ValueError as exc:
        print(f"\nERROR: {exc}", file=sys.stderr)
        print(
            f"Raw Step 2 stdout (verbatim, for debugging):\n{stdout}",
            file=sys.stderr,
        )
        sys.exit(1)
    else:
        if verdict == "no":
            print(f"Not implementable — {rationale}")
            return NotImplementable(rationale=rationale, evidence=evidence)
    return None


def run_steps(steps, *, model="opus",
              continue_session=False) -> "NotImplementable | None":
    """Run each step as a separate Claude call.

    Returns ``None`` on success, or a ``NotImplementable`` sentinel
    as soon as the Step 1 implementability gate produces a
    not-implementable verdict.
    """
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)

    total = len(steps)

    for i, (description, prompt) in enumerate(steps):
        step_num = i + 1

        cmd = [
            "claude", "-p",
            "--model", model,
            "--effort", "high",
            "--verbose",
            "--output-format", "json",
            "--dangerously-skip-permissions",
        ]
        if i > 0 or continue_session:
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

        if step_num == 1:
            not_implementable = _handle_step2(result.stdout)
            if not_implementable is not None:
                return not_implementable

    return None


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
    result = run_steps(
        steps, model=args.model,
        continue_session=args.continue_session,
    )
    if isinstance(result, NotImplementable):
        print("Not implementable — closing issue.")
        comment = (
            "Deemed not implementable.\n\n"
            f"Rationale:\n{result.rationale}"
        )
        subprocess.run(
            ["gh", "issue", "close", str(args.issue), "--comment", comment],
            check=True,
        )
        return
    added, modified, deleted = get_porcelain_changes()
    added = [p for p in added if _is_valid_path(p)]
    modified = [p for p in modified if _is_valid_path(p)]
    deleted = [p for p in deleted if _is_valid_path(p)]
    action = build_action_summary(added, modified, deleted)
    print(f"Action summary:\n{action}")
    commit_implementation(args.subclause, args.issue, action=action)
