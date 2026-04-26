"""Read-only satisfaction oracle for a single LRM subclause.

Issues a single Claude call that reads the LRM text for a subclause,
surveys both the source tree and the test tree, and returns a structured
``SubclauseDiagnostic`` against the (a)-(e) satisfaction predicate from
#1265. Prints the diagnostic as JSON to stdout. Read-only: never moves,
renames, edits, or deletes anything.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import asdict

from lib.python.cli import (
    add_lrm_arg,
    add_model_arg,
    add_subclause_arg,
    validate_lrm,
    validate_subclause,
)
from lib.python.clause import STAGE_TO_PREFIX, clause_to_filename
from lib.python.lrm import build_lrm_read_instruction
from lib.python.satisfy import (
    SATISFACTION_CONDITIONS,
    SATISFIED,
    ConditionStatus,
    SubclauseDiagnostic,
)


_DISALLOWED_TOOLS = (
    "Write Edit MultiEdit NotebookEdit"
    " Bash(git commit *) Bash(git push *)"
    " Bash(git rm *) Bash(git mv *)"
    " Bash(rm *) Bash(mv *) Bash(cp *) Bash(touch *) Bash(mkdir *)"
)


# ---------------------------------------------------------------------------
# Prompt construction
# ---------------------------------------------------------------------------

def build_prompt(subclause: str, lrm: str) -> str:
    """Return the single-call oracle prompt for ``subclause``."""
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    examples = [
        clause_to_filename(prefix, subclause) + ".cpp"
        for _stage, prefix in sorted(STAGE_TO_PREFIX.items())
    ]
    canonical_files = ", ".join(examples)

    return (
        f"You are the read-only satisfaction oracle for §{subclause}.\n\n"
        f"{read_ctx}\n\n"
        "Then survey both src/ and test/src/unit/ for any code or tests"
        f" covering §{subclause}. The canonical test files for"
        f" §{subclause} are: {canonical_files}.\n\n"
        "Judge the codebase against the five-part satisfaction predicate"
        f" for §{subclause}:\n"
        "  (a) rule_coverage: every normative rule of the subclause is"
        " realised by production code;\n"
        "  (b) test_coverage: the test suite exercises every normative"
        " rule of the subclause;\n"
        "  (c) test_placement: those tests live in the canonical files"
        " above (not scattered across files belonging to other"
        " subclauses);\n"
        "  (d) naming: test suite and individual test names are"
        " PascalCase descriptive names, not clause-number-encoded"
        " labels like Cl5_7_1_;\n"
        "  (e) deduplication: there are no duplicate tests for the"
        " subclause.\n\n"
        "You are READ-ONLY. Do not move, rename, edit, create, or"
        " delete anything. Judge and report.\n\n"
        "For a parent subclause, the survey naturally rolls up over"
        " its children: the parent is satisfied iff its own intro rules"
        " are satisfied AND every child subclause is satisfied. Do not"
        " invoke yourself recursively; reach child-area files directly.\n\n"
        "Output ONLY a single JSON object with these five keys, no"
        " preamble or trailing text. Each value is either the literal"
        ' string "satisfied" or a non-empty list of concrete failure'
        " description strings. Example:\n"
        "{\n"
        '  "rule_coverage": ["rule 7 has no production code"],\n'
        '  "test_coverage": "satisfied",\n'
        '  "test_placement": ["test for rule 5 lives in'
        ' test_parser_clause_33_04_01.cpp"],\n'
        '  "naming": "satisfied",\n'
        '  "deduplication": "satisfied"\n'
        "}"
    )


# ---------------------------------------------------------------------------
# Response parsing
# ---------------------------------------------------------------------------

def extract_json_object(text: str) -> str:
    """Extract a JSON object substring from ``text``.

    Handles bare objects and ```json``` fenced blocks. Raises
    ``ValueError`` if no ``{...}`` substring is present.
    """
    fenced = re.search(
        r"```(?:json)?\s*(\{.*?\})\s*```", text, re.DOTALL,
    )
    if fenced:
        return fenced.group(1)
    obj = re.search(r"\{.*\}", text, re.DOTALL)
    if obj:
        return obj.group(0)
    raise ValueError("No JSON object found in oracle output")


def _parse_condition(condition: str, value: object) -> ConditionStatus:
    """Validate one condition value; return it normalised."""
    if value == SATISFIED:
        return SATISFIED
    if isinstance(value, list) and value:
        if not all(isinstance(item, str) for item in value):
            raise ValueError(
                f"Condition {condition} must be a list of strings",
            )
        return list(value)
    raise ValueError(
        f"Condition {condition} must be 'satisfied' or a non-empty"
        " list of failure strings",
    )


def parse_diagnostic(text: str) -> SubclauseDiagnostic:
    """Parse the oracle's response text into a ``SubclauseDiagnostic``."""
    body = extract_json_object(text)
    payload = json.loads(body)
    fields: dict[str, ConditionStatus] = {}
    for condition in SATISFACTION_CONDITIONS:
        if condition not in payload:
            raise ValueError(f"Missing condition: {condition}")
        fields[condition] = _parse_condition(condition, payload[condition])
    return SubclauseDiagnostic(**fields)


def diagnostic_to_payload(diag: SubclauseDiagnostic) -> dict:
    """Return a JSON-serialisable dict including the rolled-up verdict."""
    payload = asdict(diag)
    payload["verdict"] = diag.verdict
    return payload


# ---------------------------------------------------------------------------
# Claude CLI invocation
# ---------------------------------------------------------------------------

def _build_env() -> dict:
    """Return a clean environment for Claude CLI subprocesses."""
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)
    return env


def run_oracle(prompt: str, *, model: str = "opus") -> str:
    """Invoke Claude in JSON mode; return the ``.result`` text.

    Loud-fatal on non-zero exit, non-JSON stdout, or missing result.
    """
    cmd = [
        "claude", "-p",
        "--model", model,
        "--output-format", "json",
        "--dangerously-skip-permissions",
        "--disallowedTools", _DISALLOWED_TOOLS,
    ]
    env = _build_env()
    completed = subprocess.run(
        cmd,
        input=prompt,
        capture_output=True,
        text=True,
        env=env,
        check=False,
    )
    if completed.returncode != 0:
        print(completed.stderr, file=sys.stderr)
        sys.exit(completed.returncode)
    try:
        payload = json.loads(completed.stdout)
    except json.JSONDecodeError:
        print(
            f"Claude CLI did not return JSON:\n{completed.stdout}",
            file=sys.stderr,
        )
        sys.exit(1)
    text = payload.get("result")
    if not isinstance(text, str) or not text:
        print("Claude CLI did not return a result string", file=sys.stderr)
        sys.exit(1)
    return text


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def parse_args(argv=None) -> argparse.Namespace:
    """Parse and validate CLI arguments."""
    parser = argparse.ArgumentParser(
        description=(
            "Read-only satisfaction oracle for an LRM subclause."
            " Prints a SubclauseDiagnostic JSON object to stdout."
        ),
    )
    add_lrm_arg(parser)
    add_subclause_arg(parser)
    add_model_arg(parser)
    args = parser.parse_args(argv)
    validate_lrm(parser, args)
    validate_subclause(parser, args)
    return args


def main(argv=None) -> None:
    """Run the oracle and print the diagnostic JSON to stdout."""
    args = parse_args(argv)
    print(
        f"Oracle: §{args.subclause}, model {args.model}",
        file=sys.stderr,
    )
    prompt = build_prompt(args.subclause, str(args.lrm))
    text = run_oracle(prompt, model=args.model)
    diag = parse_diagnostic(text)
    payload = diagnostic_to_payload(diag)
    print(json.dumps(payload, indent=2))
