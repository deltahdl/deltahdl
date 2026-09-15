"""Tests for lib.github."""

from lib.python.github import (
    format_subclause_label,
)


# ---- format_subclause_label ------------------------------------------------


def test_format_subclause_label_numeric() -> None:
    """Numeric subclauses get the section sign prefix."""
    assert format_subclause_label("3.14.1") == "§3.14.1"


def test_format_subclause_label_annex() -> None:
    """Annex subclauses use bare identifiers without section sign."""
    assert format_subclause_label("A.1.1") == "A.1.1"
