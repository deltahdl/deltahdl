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

from .streaming import (
    build_streaming_cmd,
    run_claude_streaming_with_retry,
)


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
    can take many minutes and the user needs to see progress. Wraps
    each call in a content-filter retry loop (max two retries) using
    the recovery prompt from ``streaming``; the retry call appends
    ``--continue`` so it resumes the same Claude session. Loud-fatal
    on a non-zero exit code, a missing result event, or after the
    retry budget is exhausted.
    """
    cmd = build_streaming_cmd(
        model=model, disallowed_tools=DISALLOWED_TOOLS,
    )
    retry_cmd = build_streaming_cmd(
        model=model, disallowed_tools=DISALLOWED_TOOLS,
        continue_session=True,
    )
    return run_claude_streaming_with_retry(
        cmd, prompt, env=build_env(), retry_cmd=retry_cmd, role="Oracle",
    )


# ---------------------------------------------------------------------------
# compute_subclause_dependencies
# ---------------------------------------------------------------------------

_DEP_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")
_FENCED_ARR_RE = re.compile(r"```(?:json)?\s*(\[.*?\])\s*```", re.DOTALL)
_BARE_ARR_RE = re.compile(r"\[[^\[\]]*\]", re.DOTALL)


def _extract_dependency_array(text: str) -> str:
    """Return a JSON array substring from the dependency oracle's output."""
    match = _FENCED_ARR_RE.search(text)
    if match:
        return match.group(1)
    # Pick the LAST bare-array group: the oracle's reasoning prose can
    # contain bracketed examples (e.g. "[example with typedef struct,
    # function]") earlier in the response, so a greedy match would span
    # from the first prose bracket to the actual final answer.
    matches = _BARE_ARR_RE.findall(text)
    if matches:
        return matches[-1]
    raise ValueError("No JSON array found in oracle output")


def build_dependency_prompt(subclause: str, lrm: str) -> str:
    """Return the single-call dependency-oracle prompt for ``subclause``."""
    read_ctx = build_lrm_read_instruction(subclause, lrm)
    return (
        f"You are the read-only dependency oracle for §{subclause}.\n\n"
        f"{read_ctx}\n\n"
        f"List the subclauses §{subclause}'s implementation builds on"
        f" top of. A subclause §Y belongs on the list when"
        f" §{subclause} states a normative rule whose implementation"
        " needs §Y's machinery to already be in place. For each"
        " subclause you list, you can quote the sentence in"
        f" §{subclause} that states the rule and name the §Y"
        " machinery the rule needs.\n\n"
        "Order the list foundations-first: subclauses that define the"
        " most general machinery come before subclauses that build on"
        " those.\n\n"
        "Read-only role: judge and report.\n\n"
        "Output a single JSON array of subclause-identifier strings"
        " in the same shape as --subclause input (digit-or-letter"
        ' heads, dotted decimal parts), e.g. ["33.6.1", "33.4.1.5"].'
        f" An empty array [] means §{subclause}'s normative rules"
        " implement on top of code already in the tree."
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
