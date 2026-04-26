"""Tests for lib.python.satisfy."""

from typing import Any

from lib.python.satisfy import (
    SATISFACTION_CONDITIONS,
    SATISFIED,
    SubclauseDiagnostic,
)


def _diagnostic(**overrides: Any) -> SubclauseDiagnostic:
    """Build a diagnostic with all conditions satisfied except the overrides."""
    fields = {condition: SATISFIED for condition in SATISFACTION_CONDITIONS}
    fields.update(overrides)
    return SubclauseDiagnostic(**fields)


# --- SATISFACTION_CONDITIONS ---


def test_satisfaction_conditions_match_predicate() -> None:
    """The five conditions correspond to the (a)-(e) satisfaction predicate."""
    assert SATISFACTION_CONDITIONS == (
        "rule_coverage", "test_coverage", "test_placement",
        "naming", "deduplication",
    )


# --- SATISFIED ---


def test_satisfied_is_the_string_satisfied() -> None:
    """The SATISFIED sentinel is the string 'satisfied'."""
    assert SATISFIED == "satisfied"


# --- SubclauseDiagnostic.verdict ---


def test_verdict_yes_when_all_conditions_satisfied() -> None:
    """Verdict is 'yes' when every condition is satisfied."""
    assert _diagnostic().verdict == "yes"


def test_verdict_no_when_rule_coverage_fails() -> None:
    """Verdict is 'no' when rule_coverage reports failures."""
    diag = _diagnostic(rule_coverage=["rule 7 has no production code"])
    assert diag.verdict == "no"


def test_verdict_no_when_test_coverage_fails() -> None:
    """Verdict is 'no' when test_coverage reports failures."""
    diag = _diagnostic(test_coverage=["rule 5 has no test"])
    assert diag.verdict == "no"


def test_verdict_no_when_test_placement_fails() -> None:
    """Verdict is 'no' when test_placement reports failures."""
    diag = _diagnostic(
        test_placement=["test for rule 5 lives in test_..._33_04_01.cpp"],
    )
    assert diag.verdict == "no"


def test_verdict_no_when_naming_fails() -> None:
    """Verdict is 'no' when naming reports failures."""
    diag = _diagnostic(
        naming=["suite name 'Cl33_4_1_5_Inheritance' violates convention"],
    )
    assert diag.verdict == "no"


def test_verdict_no_when_deduplication_fails() -> None:
    """Verdict is 'no' when deduplication reports failures."""
    diag = _diagnostic(
        deduplication=["tests FooA and FooB cover the same rule"],
    )
    assert diag.verdict == "no"


# --- SubclauseDiagnostic field access ---


def test_diagnostic_preserves_failure_list() -> None:
    """A failure list is stored verbatim and accessible by attribute."""
    failures = ["rule 7 has no production code", "rule 9 has no production code"]
    diag = _diagnostic(rule_coverage=failures)
    assert diag.rule_coverage == failures
