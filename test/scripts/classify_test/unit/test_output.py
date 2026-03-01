"""Unit tests for output formatting in classify_test."""

from classify_test._output import (
    _format_clause,
    print_classification_table as _print_classification_table,
)
from helpers import make_test_block as _tb


# ---- _format_clause --------------------------------------------------------


def test_format_clause_non_lrm():
    """Non-LRM clause formats as 'Non-LRM TAG'."""
    assert _format_clause("non-lrm:aig") == "Non-LRM AIG"


def test_format_clause_non_lrm_underscore():
    """Non-LRM clause with underscore converts to space."""
    assert _format_clause("non-lrm:aig_opt") == "Non-LRM AIG OPT"


def test_format_clause_regular():
    """Regular clause formats with section sign."""
    assert _format_clause("6.1") == "\u00a76.1"


# ---- _print_classification_table -------------------------------------------


def test_print_classification_test_line(capsys):
    """Prints 'Test: Name()' for each test."""
    t = _tb("Foo", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "Test: Foo()" in capsys.readouterr().out


def test_print_classification_clause_line(capsys):
    """Prints 'Clause:' with formatted clause."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "Clause: \u00a76.1" in capsys.readouterr().out


def test_print_classification_rationale_line(capsys):
    """Prints 'Rationale:' with rationale text."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "AIG stuff"
    _print_classification_table([t])
    assert "Rationale: AIG stuff" in capsys.readouterr().out


def test_print_classification_non_lrm_clause(capsys):
    """Non-LRM clause displays as 'Non-LRM AIG'."""
    t = _tb("T", prefix="test_non_lrm_", clause="non-lrm:aig")
    _print_classification_table([t])
    assert "Clause: Non-LRM AIG" in capsys.readouterr().out


def test_print_classification_none_clause(capsys):
    """None clause displays as '(parse error)'."""
    t = _tb("T", prefix="test_non_lrm_", clause=None)
    _print_classification_table([t])
    assert "Clause: (parse error)" in capsys.readouterr().out


def test_print_classification_separator_between(capsys):
    """Multi-test output has ---- separator between sub-reports."""
    t1 = _tb("A", prefix="test_parser_", clause="6.1")
    t2 = _tb("B", prefix="test_parser_", clause="6.1")
    _print_classification_table([t1, t2])
    assert "----" in capsys.readouterr().out


def test_print_classification_no_trailing_separator(capsys):
    """No ---- after the last sub-report."""
    t1 = _tb("A", prefix="test_parser_", clause="6.1")
    t2 = _tb("B", prefix="test_parser_", clause="6.1")
    _print_classification_table([t1, t2])
    out = capsys.readouterr().out
    assert out.count("----") == 1


def test_print_classification_single_no_separator(capsys):
    """Single test has no ---- separator."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "----" not in capsys.readouterr().out


def test_print_classification_no_line_over_80(capsys):
    """No output line exceeds 80 characters."""
    long_rationale = "word " * 20  # 100 chars, will need wrapping
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = long_rationale.strip()
    _print_classification_table([t])
    out = capsys.readouterr().out
    assert all(len(line) <= 80 for line in out.splitlines())


def test_print_classification_wrap_aligns(capsys):
    """Wrapped continuation lines align with 2-space indent."""
    long_rationale = "word " * 20
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = long_rationale.strip()
    _print_classification_table([t])
    lines = capsys.readouterr().out.splitlines()
    # Find continuation lines (after Rationale: line, before next label/sep)
    rationale_idx = next(
        i for i, l in enumerate(lines) if l.startswith("  Rationale:")
    )
    cont = lines[rationale_idx + 1]
    assert cont.startswith("  ") and not cont.startswith("  ----")


def test_print_classification_prefix_rationale(capsys):
    """Prints prefix rationale when set on test block."""
    t = _tb("T", prefix="test_simulator_", clause="5.12")
    t.prefix_rationale = "attributes affect elaboration"
    _print_classification_table([t])
    assert "Stage: simulator" in capsys.readouterr().out


def test_print_classification_prefix_rationale_reason(capsys):
    """Prints the stage rationale text."""
    t = _tb("T", prefix="test_simulator_", clause="5.12")
    t.prefix_rationale = "attributes affect elaboration"
    _print_classification_table([t])
    assert "attributes affect elaboration" in capsys.readouterr().out


def test_print_classification_pattern_match_stage(capsys):
    """Prints stage line for pattern-matched prefix."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.prefix_rationale = "body contains 'Parse'"
    _print_classification_table([t])
    assert "Stage: parser" in capsys.readouterr().out
