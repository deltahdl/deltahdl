"""Read-only oracles for the satisfaction pipeline.

A single oracle: ``compute_subclause_dependencies`` returns a
``SubclauseDependencies`` list of subclause identifiers ordered
dependencies-first.

The invocation is read-only: the disallowed-tools list blocks every
mutating tool and ``run_oracle_call`` exits non-zero on any failure.
"""

import json
import os
import re
import sys
from typing import TypeAlias

from lib.python.lrm import build_lrm_read_instruction

from .streaming import build_streaming_cmd, run_claude_streaming


SubclauseDependencies: TypeAlias = list[str]


# ---------------------------------------------------------------------------
# Claude-CLI plumbing
# ---------------------------------------------------------------------------

DISALLOWED_TOOLS = (
    "Write Edit MultiEdit NotebookEdit"
    " Bash(git commit *) Bash(git push *)"
    " Bash(git rm *) Bash(git mv *)"
    " Bash(rm *) Bash(mv *) Bash(cp *) Bash(touch *) Bash(mkdir *)"
    " Bash(pdftotext *) Bash(pdfgrep *) Bash(pdftohtml *)"
    " Bash(pdftoppm *) Bash(mutool *)"
)


def build_env() -> dict:
    """Return a Claude-safe copy of the current environment."""
    env = os.environ.copy()
    env.pop("CLAUDECODE", None)
    return env


def run_oracle_call(prompt: str, *, model: str) -> str:
    """Invoke Claude with read-only tools; return the oracle's ``.result``.

    Runs the CLI in stream-json mode so the streaming runner can decode
    events and print Claude's text/tool_use blocks live — oracle passes
    can take many minutes and the user needs to see progress. The
    streaming runner extracts the terminal ``.result`` text and is
    loud-fatal on a non-zero exit code or a missing result event.
    """
    cmd = build_streaming_cmd(
        model=model, disallowed_tools=DISALLOWED_TOOLS,
    )
    return run_claude_streaming(cmd, prompt, env=build_env())


# ---------------------------------------------------------------------------
# compute_subclause_dependencies
# ---------------------------------------------------------------------------

_DEP_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")
_FENCED_ARR_RE = re.compile(r"```(?:json)?\s*(\[.*?\])\s*```", re.DOTALL)
_BARE_ARR_RE = re.compile(r"\[.*\]", re.DOTALL)


def _extract_dependency_array(text: str) -> str:
    """Return a JSON array substring from the dependency oracle's output."""
    match = _FENCED_ARR_RE.search(text)
    if match:
        return match.group(1)
    match = _BARE_ARR_RE.search(text)
    if match:
        return match.group(0)
    raise ValueError("No JSON array found in oracle output")


def build_dependency_prompt(subclause: str, lrm: str) -> str:
    """Return the single-call dependency-oracle prompt for ``subclause``."""
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    return (
        f"You are the read-only dependency oracle for §{subclause}.\n\n"
        f"{read_ctx}\n\n"
        "Identify every OTHER subclause whose satisfaction is REQUIRED"
        f" before §{subclause} can be satisfied. A subclause §Y is a"
        f" dependency of §{subclause} when:\n"
        f"  - §{subclause} reuses machinery defined by §Y (binding,"
        " elaboration, configuration, etc.); OR\n"
        f"  - §{subclause} is a parent and §Y is one of its child"
        " subclauses (a parent's satisfaction rolls up over its"
        " children); OR\n"
        f"  - §{subclause}'s normative rules cannot be tested without"
        " syntax or semantics defined in §Y.\n\n"
        "Do NOT include §{subclause} itself. Do NOT include subclauses"
        " whose satisfaction is merely related, only those whose"
        " satisfaction is REQUIRED first. Order the list dependencies-"
        "first (children before parents, foundations before consumers)."
        "\n\n"
        "You are READ-ONLY. Do not move, rename, edit, create, or"
        " delete anything. Judge and report.\n\n"
        "Output ONLY a single JSON array of subclause-identifier"
        " strings, no preamble or trailing text. Each identifier is the"
        " same shape as --subclause input (digit-or-letter heads,"
        ' dotted decimal parts), e.g. ["33.6.1", "33.4.1.5"]. If there'
        " are no dependencies, output []."
    )


def parse_dependencies(text: str) -> SubclauseDependencies:
    """Parse the dependency oracle's response into a list of subclause strings."""
    body = _extract_dependency_array(text)
    payload = json.loads(body)
    result: SubclauseDependencies = []
    for item in payload:
        if not isinstance(item, str):
            raise ValueError(
                f"Dependency entry must be a string, got {type(item).__name__}",
            )
        if not _DEP_RE.match(item):
            raise ValueError(
                f"Dependency entry '{item}' is not a valid subclause"
                " identifier",
            )
        result.append(item)
    return result


def compute_subclause_dependencies(
    subclause: str, lrm: str, *, model: str,
) -> SubclauseDependencies:
    """Run the dependency oracle for ``subclause``."""
    print(
        f"Dependency oracle: §{subclause}, model {model}",
        file=sys.stderr,
    )
    prompt = build_dependency_prompt(subclause, lrm)
    text = run_oracle_call(prompt, model=model)
    return parse_dependencies(text)
