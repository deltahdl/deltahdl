"""Prompts and schemas for test classification."""

import json
from typing import Any

CLAUSE_PROMPT_TEMPLATE = """What IEEE 1800-2023 clause does this test exercise?

Return exactly one clause — the single most relevant subclause.
Use the most specific subclause possible (e.g., 9.2.2.2.2 not 9.2, or A.6.3 for Annex A).
Read the LRM to verify — do not guess from titles.
If no LRM clause applies, respond with "non-lrm".

Also return a suite_name and test_name: PascalCase names that intuitively
describe what the test exercises. Both must be valid C++ identifiers. The suite_name groups related tests (e.g.,
BinaryOperators, SpecifyBlocks, AlwaysCombLatch). The test_name describes
what this specific test case verifies (e.g., AdditionOverflow,
EmptyPattern, NestedReplication). Do NOT include clause or annex numbers.

LRM: {lrm_path}

TEST({suite}, {test_name}):
{test_body}
"""

CLAUSE_AGAINST_PROMPT_TEMPLATE = \
    """Does this test exercise any of these IEEE 1800-2023 subclauses: {against}?

Read the LRM to verify — do not guess from titles.
If the test exercises one of those subclauses, return that clause.
If it does not exercise any of them, return "none".

Also return a suite_name and test_name: PascalCase names that intuitively
describe what the test exercises. Both must be valid C++ identifiers.
The suite_name groups related tests (e.g., BinaryOperators,
SpecifyBlocks, AlwaysCombLatch). The test_name describes what this
specific test case verifies (e.g., AdditionOverflow, EmptyPattern,
NestedReplication). Do NOT include clause or annex numbers.

LRM: {lrm_path}

TEST({suite}, {test_name}):
{test_body}
"""

TOPIC_PROMPT_TEMPLATE = """What non-LRM topic does this test belong to?

Return a short snake_case topic name (e.g., "aig", "arena", "dpi_helpers").

Also return a suite_name and test_name: PascalCase names that intuitively
describe what the test exercises. Both must be valid C++ identifiers. The suite_name groups related tests (e.g.,
AigGraph, ArenaAllocator, DpiHelpers). The test_name describes what this
specific test case verifies. Do NOT include clause or annex numbers.

{topics}
TEST({suite}, {test_name}):
{test_body}
"""

CLAUSE_SCHEMA = json.dumps({
    "type": "object",
    "properties": {
        "clause": {"type": "string"},
        "rationale": {"type": "string"},
        "suite_name": {"type": "string"},
        "test_name": {"type": "string"},
    },
    "required": ["clause", "rationale", "suite_name", "test_name"],
    "additionalProperties": False,
})

TOPIC_SCHEMA = json.dumps({
    "type": "object",
    "properties": {
        "non_lrm_topic": {"type": "string"},
        "rationale": {"type": "string"},
        "suite_name": {"type": "string"},
        "test_name": {"type": "string"},
    },
    "required": ["non_lrm_topic", "rationale", "suite_name", "test_name"],
    "additionalProperties": False,
})

PREFIX_PROMPT_TEMPLATE = """Which pipeline stage does this test belong to?

The DeltaHDL compiler has six pipeline stages:
- preprocessor: macro expansion, `include, `ifdef, `timescale
- lexer: tokenization, keyword recognition
- parser: recursive-descent parsing, AST construction
- elaborator: type resolution, constant evaluation, sensitivity analysis, RTLIR
- simulator: scheduling, process execution, expression evaluation, VPI, DPI,
  clocking, assertions, coverage, gate/switch primitives, specify, timing checks
- synthesizer: AIG construction, optimization, LUT/cell mapping, netlist output

Here is the LRM. The LRM is the source of truth for determining which
pipeline stage implements the functionality this test exercises.

LRM: {lrm_path}

TEST({suite}, {test_name}):
{test_body}
"""

PREFIX_SCHEMA = json.dumps({
    "type": "object",
    "properties": {
        "pipeline_stage": {
            "type": "string",
            "enum": ["preprocessor", "lexer", "parser",
                     "elaborator", "simulator", "synthesizer"],
        },
        "rationale": {"type": "string"},
    },
    "required": ["pipeline_stage", "rationale"],
    "additionalProperties": False,
})


def build_clause_prompt(test: Any, lrm_path: str, against: str = "") -> str:
    """Build the clause-only classification prompt."""
    body = "\n".join(test.preceding_comments + test.lines)
    template = (
        CLAUSE_AGAINST_PROMPT_TEMPLATE if against
        else CLAUSE_PROMPT_TEMPLATE
    )
    return template.format(
        lrm_path=lrm_path,
        suite=test.suite_name,
        test_name=test.test_name,
        test_body=body,
        against=against,
    )


def build_topic_prompt(test: Any, topics_hint: str) -> str:
    """Build the topic classification prompt for non-LRM tests."""
    body = "\n".join(test.preceding_comments + test.lines)
    return TOPIC_PROMPT_TEMPLATE.format(
        topics=topics_hint,
        suite=test.suite_name,
        test_name=test.test_name,
        test_body=body,
    )
