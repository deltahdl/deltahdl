"""Output and summary formatting for classify_test."""

import textwrap
from typing import Any


def _format_clause(clause: str | None) -> str:
    """Format a clause for display."""
    if clause is None:
        return "(parse error)"
    if clause.startswith("non-lrm:"):
        tag = clause[len("non-lrm:"):].upper().replace("_", " ")
        return f"Non-LRM {tag}"
    return f"\u00a7{clause}"


def _wrap(label: str, value: str) -> str:
    """Wrap a labeled line to 80 chars with 2-space continuation indent."""
    return textwrap.fill(
        value, width=80,
        initial_indent=f"  {label}: ",
        subsequent_indent="  ",
    )


_PREFIX_TO_STAGE = {
    "test_preprocessor_": "preprocessor",
    "test_lexer_": "lexer",
    "test_parser_": "parser",
    "test_elaborator_": "elaborator",
    "test_simulator_": "simulator",
    "test_synthesizer_": "synthesizer",
}


def print_classification_table(tests: list[Any]) -> None:
    """Print the classification results as sub-reports."""
    for i, t in enumerate(tests):
        c = t.classification
        print(_wrap("Test", f"{t.test_name}()"))
        print(_wrap("Clause", _format_clause(c.clause)))
        print(_wrap("Rationale", c.rationale or ""))
        stage = _PREFIX_TO_STAGE.get(c.prefix, c.prefix or "") if c.prefix else ""
        print(_wrap("Stage", stage))
        print(_wrap("Stage rationale", c.prefix_rationale or ""))
        if i < len(tests) - 1:
            print("  ----")
