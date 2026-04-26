"""Shared Claude-CLI plumbing for the satisfaction-pipeline oracles.

The oracles are read-only single-call Claude invocations whose output
is a JSON literal: a ``SubclauseDiagnostic`` for ``is_subclause_satisfied``
and a ``SubclauseDependencies`` list for ``compute_subclause_dependencies``.
This module owns the parts they share — the disallowed-tools list that
makes the call read-only, the environment scrub, the subprocess call,
the JSON-literal extractor that handles fenced code blocks, and the
common argparse setup.
"""

import argparse
import json
import os
import re
import subprocess
import sys

from lib.python.cli import (
    add_lrm_arg,
    add_model_arg,
    add_subclause_arg,
    parse_and_validate_subclause,
)


DISALLOWED_TOOLS = (
    "Write Edit MultiEdit NotebookEdit"
    " Bash(git commit *) Bash(git push *)"
    " Bash(git rm *) Bash(git mv *)"
    " Bash(rm *) Bash(mv *) Bash(cp *) Bash(touch *) Bash(mkdir *)"
)


def build_env() -> dict:
    """Return a Claude-safe copy of the current environment."""
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)
    return env


_FENCED_OBJ_RE = re.compile(r"```(?:json)?\s*(\{.*?\})\s*```", re.DOTALL)
_FENCED_ARR_RE = re.compile(r"```(?:json)?\s*(\[.*?\])\s*```", re.DOTALL)
_BARE_OBJ_RE = re.compile(r"\{.*\}", re.DOTALL)
_BARE_ARR_RE = re.compile(r"\[.*\]", re.DOTALL)


def extract_json_literal(text: str) -> str:
    """Return a JSON object or array substring from ``text``.

    Handles bare literals and ```json``` code fences. Raises
    ``ValueError`` if no ``{...}`` or ``[...]`` substring is present.
    """
    for pattern in (_FENCED_OBJ_RE, _FENCED_ARR_RE):
        match = pattern.search(text)
        if match:
            return match.group(1)
    for pattern in (_BARE_OBJ_RE, _BARE_ARR_RE):
        match = pattern.search(text)
        if match:
            return match.group(0)
    raise ValueError("No JSON literal found in oracle output")


def build_oracle_args(
    description: str, argv: list[str] | None = None,
) -> argparse.Namespace:
    """Return parsed CLI args for an oracle script.

    Wires up ``--lrm``, ``--subclause`` and ``--model`` and runs the
    standard validation. Both oracles use the same argument set, so this
    helper keeps their CLI surfaces in lockstep without duplicating the
    parser-construction boilerplate.
    """
    parser = argparse.ArgumentParser(description=description)
    add_lrm_arg(parser)
    add_subclause_arg(parser)
    add_model_arg(parser)
    return parse_and_validate_subclause(parser, argv)


def run_oracle_call(prompt: str, *, model: str) -> str:
    """Invoke Claude in JSON mode; return the oracle's ``.result`` text.

    Loud-fatal on non-zero exit, non-JSON stdout, or missing/empty
    result. The command line forces ``--output-format json`` and
    blocks every mutating tool via ``--disallowedTools``.
    """
    cmd = [
        "claude", "-p",
        "--model", model,
        "--output-format", "json",
        "--dangerously-skip-permissions",
        "--disallowedTools", DISALLOWED_TOOLS,
    ]
    completed = subprocess.run(
        cmd,
        input=prompt,
        capture_output=True,
        text=True,
        env=build_env(),
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
