"""Tests for lib.github."""

from lib.python.github import (
    format_subclause_label,
    issue_title_for,
)


# ---- format_subclause_label ------------------------------------------------


def test_format_subclause_label_numeric() -> None:
    """Numeric subclauses get the section sign prefix."""
    assert format_subclause_label("3.14.1") == "§3.14.1"


def test_format_subclause_label_annex() -> None:
    """Annex subclauses use bare identifiers without section sign."""
    assert format_subclause_label("A.1.1") == "A.1.1"


# ---- issue_title_for -------------------------------------------------------


def test_issue_title_for_is_the_title_next_subclause_matches_on() -> None:
    """The title is the exact string the resolver looks an issue up by."""
    assert issue_title_for("18.16") == "Satisfy IEEE 1800-2023 §18.16"
