"""Output and summary formatting for classify_test."""

import textwrap


def _format_clause(clause):
    """Format a clause for display."""
    if clause is None:
        return "(parse error)"
    if clause.startswith("non-lrm:"):
        tag = clause[len("non-lrm:"):].upper().replace("_", " ")
        return f"Non-LRM {tag}"
    return f"\u00a7{clause}"


def _wrap(label, value):
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


def print_classification_table(tests):
    """Print the classification results as sub-reports."""
    for i, t in enumerate(tests):
        print(_wrap("Test", f"{t.test_name}()"))
        print(_wrap("Clause", _format_clause(t.clause)))
        print(_wrap("Rationale", t.rationale or ""))
        stage = _PREFIX_TO_STAGE.get(t.prefix, t.prefix or "")
        print(_wrap("Stage", stage))
        print(_wrap("Stage rationale",
                     getattr(t, "prefix_rationale", "") or ""))
        if i < len(tests) - 1:
            print("  ----")
