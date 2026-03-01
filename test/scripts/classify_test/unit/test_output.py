"""Unit tests for output formatting in classify_test."""

from classify_test._output import (
    _format_clause,
    print_classification_table as _print_classification_table,
    print_summary as _print_summary,
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


# ---- _print_summary --------------------------------------------------------


def test_print_summary_created(capsys):
    """Live summary prints '- Created'."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False)
    assert "- Created `test_parser_clause_06_01.cpp`" in capsys.readouterr().out


def test_print_summary_moved(capsys):
    """Live summary prints '- Moved'."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False)
    assert "- Moved 1 test" in capsys.readouterr().out


def test_print_summary_deleted(capsys):
    """Live summary prints 'Deleted' when source_is_target is False."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False)
    out = capsys.readouterr().out
    assert "- Deleted `test_input.cpp`" in out


def test_print_summary_kept(capsys):
    """Live summary prints 'Kept' when source_is_target with n_kept."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", True, n_kept=3)
    out = capsys.readouterr().out
    assert "- Kept 3 tests" in out


def test_print_summary_all_correct_kept(capsys):
    """All-correct path still prints 'Kept' bullet."""
    _print_summary([], [], "test_input", True, n_kept=9)
    assert "- Kept 9 tests" in capsys.readouterr().out


def test_print_summary_has_summary_header(capsys):
    """Summary section starts with 'SUMMARY'."""
    _print_summary([], [], "test_input", True, n_kept=9)
    assert "SUMMARY" in capsys.readouterr().out


def test_print_summary_all_correct_zero_kept(capsys):
    """All-correct path with n_kept=0 skips Kept bullet."""
    _print_summary([], [], "test_input", True, n_kept=0)
    assert "Kept" not in capsys.readouterr().out


def test_print_summary_not_source_zero_moved(capsys):
    """Non-source path with empty lists has Deleted bullet."""
    _print_summary([], [], "test_input", False)
    assert "Deleted" in capsys.readouterr().out


def test_print_summary_singular_verb_belongs(capsys):
    """Singular test uses 'belongs' in created line."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False)
    assert "1 test belongs there" in capsys.readouterr().out


def test_print_summary_singular_pronoun(capsys):
    """Singular test uses 'it belongs' in moved line."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False)
    assert "it belongs" in capsys.readouterr().out


def test_print_summary_plural_verb_belong(capsys):
    """Multiple tests use 'belong' in created line."""
    t1 = _tb("T1", prefix="test_parser_", clause="6.1")
    t2 = _tb("T2", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t1, t2])]
    _print_summary(to_create, [], "test_input", False)
    assert "2 tests belong there" in capsys.readouterr().out


def test_print_summary_plural_pronoun(capsys):
    """Multiple tests use 'they belong' in moved line."""
    t1 = _tb("T1", prefix="test_parser_", clause="6.1")
    t2 = _tb("T2", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t1, t2])]
    _print_summary(to_create, [], "test_input", False)
    assert "they belong" in capsys.readouterr().out


def test_print_summary_not_deleted_when_others(capsys):
    """No 'Deleted' bullet when source file still has other tests."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False, n_others=5)
    assert "Deleted" not in capsys.readouterr().out


def test_print_summary_deleted_when_no_others(capsys):
    """'Deleted' bullet appears when n_others=0."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(to_create, [], "test_input", False, n_others=0)
    assert "Deleted" in capsys.readouterr().out


def test_print_dry_run_summary_moved(tmp_path, capsys):
    """Dry-run prints '- Would have moved'."""
    t = _tb("M", prefix="test_parser_", clause="6.1")
    merge_path = tmp_path / "test_parser_clause_06_01.cpp"
    _print_summary(
        [], [(merge_path, [t])], "test_input", False,
        dry_run=True,
    )
    assert "- Would have moved" in capsys.readouterr().out


def test_print_dry_run_summary_no_bare_moved(tmp_path, capsys):
    """Dry-run does not contain bare 'Moved' without 'Would have'."""
    t = _tb("M", prefix="test_parser_", clause="6.1")
    merge_path = tmp_path / "test_parser_clause_06_01.cpp"
    _print_summary(
        [], [(merge_path, [t])], "test_input", False,
        dry_run=True,
    )
    out = capsys.readouterr().out
    assert "Moved" not in out.replace("Would have moved", "")


def _dry_run_create_output(capsys):
    """Run a dry-run summary with one create entry and return stdout."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(
        to_create, [], "test_input", False,
        dry_run=True,
    )
    return capsys.readouterr().out


def test_print_dry_run_summary_create(capsys):
    """Dry-run prints 'Would have created'."""
    assert "- Would have created" in _dry_run_create_output(capsys)


def test_print_dry_run_summary_deleted(capsys):
    """Dry-run prints 'Would have deleted'."""
    assert "- Would have deleted `test_input.cpp`" in \
        _dry_run_create_output(capsys)


def test_print_dry_run_summary_updated(capsys):
    """Dry-run prints 'Would have updated CMakeLists.txt'."""
    assert "- Would have updated `CMakeLists.txt`" in \
        _dry_run_create_output(capsys)


def test_print_dry_run_summary_kept(capsys):
    """Dry-run prints 'Would have kept'."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    to_create = [("test_parser_clause_06_01", "6.1", [t])]
    _print_summary(
        to_create, [], "test_input", True, n_kept=3,
        dry_run=True,
    )
    out = capsys.readouterr().out
    assert "- Would have kept 3 tests" in out


def test_print_dry_run_summary_nothing_kept(capsys):
    """Dry-run all-correct path prints 'Would have kept' bullet."""
    _print_summary([], [], "test_input", True, n_kept=13, dry_run=True)
    assert "- Would have kept 13 tests" in capsys.readouterr().out


def test_print_dry_run_summary_nothing_no_removals(capsys):
    """Dry-run all-correct with no removals has SUMMARY header."""
    _print_summary([], [], "test_input", True, n_kept=13, dry_run=True)
    assert "SUMMARY" in capsys.readouterr().out


def test_print_dry_run_summary_nothing_with_removals(capsys):
    """Dry-run all-correct with removals has kept and removed bullets."""
    _print_summary(
        [], [], "test_input", True, n_kept=9, n_removed=4,
        dry_run=True,
    )
    out = capsys.readouterr().out
    assert "Would have kept 9 tests" in out
