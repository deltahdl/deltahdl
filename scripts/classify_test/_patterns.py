"""Patterns, prompts, and schemas for test classification.

Only obviously-named helpers are listed in ``PREFIX_PATTERNS``.  When
no pattern matches, ``_detect_prefix`` falls back to a Claude call
using ``PREFIX_PROMPT_TEMPLATE`` and ``PREFIX_SCHEMA``.
"""

import json

PREFIX_PATTERNS: list[tuple[str, str]] = [
    ("Preprocess", "test_preprocessor_"),
    ("SynthLower", "test_synthesizer_"),
    ("Aig", "test_synthesizer_"),
    ("Elaborate", "test_elaborator_"),
    ("Parse", "test_parser_"),
    ("Lex", "test_lexer_"),
    ("Scheduler", "test_simulator_"),
    ("SimContext", "test_simulator_"),
]

STAGE_TO_PREFIX: dict[str, str] = {
    "preprocessor": "test_preprocessor_",
    "lexer": "test_lexer_",
    "parser": "test_parser_",
    "elaborator": "test_elaborator_",
    "simulator": "test_simulator_",
    "synthesizer": "test_synthesizer_",
}

CLAUSE_PROMPT_TEMPLATE = """What IEEE 1800-2023 clause does this test exercise?

Return exactly one clause — the single most relevant subclause.
Use the most specific subclause possible (e.g., 9.2.2.2.2 not 9.2).
Read the LRM to verify — do not guess from titles.
If no LRM clause applies, respond with "non-lrm".

LRM: {lrm_path}

TEST({suite}, {test_name}):
{test_body}
"""

TOPIC_PROMPT_TEMPLATE = """What non-LRM topic does this test belong to?

Return a short snake_case topic name (e.g., "aig", "arena", "dpi_helpers").
{topics}
TEST({suite}, {test_name}):
{test_body}
"""

CLAUSE_SCHEMA = json.dumps({
    "type": "object",
    "properties": {
        "clause": {"type": "string"},
        "rationale": {"type": "string"},
    },
    "required": ["clause", "rationale"],
    "additionalProperties": False,
})

TOPIC_SCHEMA = json.dumps({
    "type": "object",
    "properties": {
        "non_lrm_topic": {"type": "string"},
        "rationale": {"type": "string"},
    },
    "required": ["non_lrm_topic", "rationale"],
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
