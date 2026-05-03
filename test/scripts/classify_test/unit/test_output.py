"""Unit tests for output formatting in classify_test."""


# ---- _format_clause --------------------------------------------------------


def test_format_clause_non_lrm(ct_output):
    """Non-LRM clause formats as 'Non-LRM TAG'."""
    _format_clause = getattr(ct_output, "_format_clause")
    assert _format_clause("non-lrm:aig") == "Non-LRM AIG"


def test_format_clause_non_lrm_underscore(ct_output):
    """Non-LRM clause with underscore converts to space."""
    _format_clause = getattr(ct_output, "_format_clause")
    assert _format_clause("non-lrm:aig_opt") == "Non-LRM AIG OPT"


def test_format_clause_regular(ct_output):
    """Regular clause formats with section sign."""
    _format_clause = getattr(ct_output, "_format_clause")
    assert _format_clause("6.1") == "\u00a76.1"


# ---- _print_classification_table -------------------------------------------


def test_print_classification_test_line(capsys, ct_output, ct_helpers):
    """Prints 'Test: Name()' for each test."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t = _tb("Foo", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "Test: Foo()" in capsys.readouterr().out


def test_print_classification_clause_line(capsys, ct_output, ct_helpers):
    """Prints 'Clause:' with formatted clause."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t = _tb("T", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "Clause: \u00a76.1" in capsys.readouterr().out


def test_print_classification_rationale_line(capsys, ct_output, ct_helpers):
    """Prints 'Rationale:' with rationale text."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.classification.rationale = "AIG stuff"
    _print_classification_table([t])
    assert "Rationale: AIG stuff" in capsys.readouterr().out


def test_print_classification_non_lrm_clause(capsys, ct_output, ct_helpers):
    """Non-LRM clause displays as 'Non-LRM AIG'."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t = _tb("T", prefix="test_non_lrm_", clause="non-lrm:aig")
    _print_classification_table([t])
    assert "Clause: Non-LRM AIG" in capsys.readouterr().out


def test_print_classification_none_clause(capsys, ct_output, ct_helpers):
    """None clause displays as '(parse error)'."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t = _tb("T", prefix="test_non_lrm_", clause=None)
    _print_classification_table([t])
    assert "Clause: (parse error)" in capsys.readouterr().out


def test_print_classification_separator_between(capsys, ct_output, ct_helpers):
    """Multi-test output has ---- separator between sub-reports."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t1 = _tb("A", prefix="test_parser_", clause="6.1")
    t2 = _tb("B", prefix="test_parser_", clause="6.1")
    _print_classification_table([t1, t2])
    assert "----" in capsys.readouterr().out


def test_print_classification_no_trailing_separator(capsys, ct_output, ct_helpers):
    """No ---- after the last sub-report."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t1 = _tb("A", prefix="test_parser_", clause="6.1")
    t2 = _tb("B", prefix="test_parser_", clause="6.1")
    _print_classification_table([t1, t2])
    out = capsys.readouterr().out
    assert out.count("----") == 1


def test_print_classification_single_no_separator(capsys, ct_output, ct_helpers):
    """Single test has no ---- separator."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t = _tb("T", prefix="test_parser_", clause="6.1")
    _print_classification_table([t])
    assert "----" not in capsys.readouterr().out


def test_print_classification_no_line_over_80(capsys, ct_output, ct_helpers):
    """No output line exceeds 80 characters."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    long_rationale = "word " * 20  # 100 chars, will need wrapping
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.classification.rationale = long_rationale.strip()
    _print_classification_table([t])
    out = capsys.readouterr().out
    assert all(len(line) <= 80 for line in out.splitlines())


def test_print_classification_wrap_aligns(capsys, ct_output, ct_helpers):
    """Wrapped continuation lines align with 2-space indent."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    long_rationale = "word " * 20
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.classification.rationale = long_rationale.strip()
    _print_classification_table([t])
    lines = capsys.readouterr().out.splitlines()
    # Find continuation lines (after Rationale: line, before next label/sep)
    rationale_idx = next(
        i for i, l in enumerate(lines) if l.startswith("  Rationale:")
    )
    cont = lines[rationale_idx + 1]
    assert cont.startswith("  ") and not cont.startswith("  ----")


def test_print_classification_prefix_rationale(capsys, ct_output, ct_helpers):
    """Prints prefix rationale when set on test block."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t = _tb("T", prefix="test_simulator_", clause="5.12")
    t.classification.prefix_rationale = "attributes affect elaboration"
    _print_classification_table([t])
    assert "Stage: simulator" in capsys.readouterr().out


def test_print_classification_prefix_rationale_reason(capsys, ct_output, ct_helpers):
    """Prints the stage rationale text."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t = _tb("T", prefix="test_simulator_", clause="5.12")
    t.classification.prefix_rationale = "attributes affect elaboration"
    _print_classification_table([t])
    assert "attributes affect elaboration" in capsys.readouterr().out


def test_print_classification_pattern_match_stage(capsys, ct_output, ct_helpers):
    """Prints stage line for pattern-matched prefix."""
    _tb = ct_helpers.make_test_block
    _print_classification_table = ct_output.print_classification_table
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.classification.prefix_rationale = "body contains 'Parse'"
    _print_classification_table([t])
    assert "Stage: parser" in capsys.readouterr().out
