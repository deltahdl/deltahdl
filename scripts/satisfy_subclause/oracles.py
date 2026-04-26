"""Read-only oracles for the satisfaction pipeline.

Two single-call Claude invocations whose outputs are JSON literals:

  - ``is_subclause_satisfied`` returns a ``SubclauseDiagnostic`` against
    the (a)-(e) satisfaction predicate from #1265.
  - ``compute_subclause_dependencies`` returns a ``SubclauseDependencies``
    list of subclause identifiers ordered dependencies-first.

Both invocations are read-only: the disallowed-tools list blocks every
mutating tool and ``run_oracle_call`` exits non-zero on any failure.
"""

import json
import os
import re
import sys
from dataclasses import dataclass
from typing import Literal, TypeAlias

from lib.python.clause import STAGE_TO_PREFIX, clause_to_filename
from lib.python.lrm import build_lrm_read_instruction

from .streaming import build_streaming_cmd, run_claude_streaming


SATISFACTION_CONDITIONS: tuple[str, ...] = (
    "rule_coverage",
    "test_coverage",
    "test_placement",
    "naming",
    "deduplication",
)


SATISFIED: Literal["satisfied"] = "satisfied"


ConditionStatus: TypeAlias = Literal["satisfied"] | list[str]
Verdict: TypeAlias = Literal["yes", "no"]
SubclauseDependencies: TypeAlias = list[str]


@dataclass(frozen=True)
class SubclauseDiagnostic:
    """Structured diagnostic returned by ``is_subclause_satisfied``.

    Each of the five satisfaction conditions is either ``SATISFIED`` (the
    condition is met) or a non-empty list of concrete failure descriptions
    (the condition is not met).  The ``verdict`` property is ``"yes"`` iff
    every condition is satisfied, else ``"no"``.
    """

    rule_coverage: ConditionStatus
    test_coverage: ConditionStatus
    test_placement: ConditionStatus
    naming: ConditionStatus
    deduplication: ConditionStatus

    @property
    def verdict(self) -> Verdict:
        """``"yes"`` iff every condition is satisfied, else ``"no"``."""
        for condition in SATISFACTION_CONDITIONS:
            if getattr(self, condition) != SATISFIED:
                return "no"
        return "yes"


# ---------------------------------------------------------------------------
# Claude-CLI plumbing
# ---------------------------------------------------------------------------

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
# is_subclause_satisfied
# ---------------------------------------------------------------------------

def build_satisfaction_prompt(subclause: str, lrm: str) -> str:
    """Return the single-call satisfaction-oracle prompt for ``subclause``."""
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


def parse_satisfaction_diagnostic(text: str) -> SubclauseDiagnostic:
    """Parse the satisfaction oracle's response into a ``SubclauseDiagnostic``."""
    body = extract_json_literal(text)
    payload = json.loads(body)
    fields: dict[str, ConditionStatus] = {}
    for condition in SATISFACTION_CONDITIONS:
        if condition not in payload:
            raise ValueError(f"Missing condition: {condition}")
        fields[condition] = _parse_condition(condition, payload[condition])
    return SubclauseDiagnostic(**fields)


def is_subclause_satisfied(
    subclause: str, lrm: str, *, model: str,
) -> SubclauseDiagnostic:
    """Run the satisfaction oracle for ``subclause``."""
    print(
        f"Satisfaction oracle: §{subclause}, model {model}",
        file=sys.stderr,
    )
    prompt = build_satisfaction_prompt(subclause, lrm)
    text = run_oracle_call(prompt, model=model)
    return parse_satisfaction_diagnostic(text)


# ---------------------------------------------------------------------------
# compute_subclause_dependencies
# ---------------------------------------------------------------------------

_DEP_RE = re.compile(r"^(\d+|[A-Z])(\.\d+){0,4}$")


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
    body = extract_json_literal(text)
    payload = json.loads(body)
    if not isinstance(payload, list):
        raise ValueError("Dependency oracle output must be a JSON array")
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
