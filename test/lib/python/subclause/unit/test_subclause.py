"""Tests for lib.python.subclause."""

from lib.python.subclause import (
    build_hierarchy,
)


# --- build_hierarchy ---


def test_build_hierarchy_numeric_depth_1() -> None:
    """Clause '4' produces depth-1 numeric hierarchy."""
    assert build_hierarchy("4")["clause_number"] == "4"


def test_build_hierarchy_numeric_no_ancestors() -> None:
    """Depth-2 subclause '4.1' has no ancestors."""
    assert build_hierarchy("4.1")["ancestors"] == []


def test_build_hierarchy_numeric_ancestors() -> None:
    """Depth-3 subclause '6.24.1' has one ancestor."""
    assert build_hierarchy("6.24.1")["ancestors"] == ["6.24"]


def test_build_hierarchy_annex_letter() -> None:
    """Annex 'B' sets letter to 'B'."""
    assert build_hierarchy("B")["letter"] == "B"


def test_build_hierarchy_annex_is_annex() -> None:
    """Annex 'A.8' is flagged as annex."""
    assert build_hierarchy("A.8")["is_annex"] is True


def test_build_hierarchy_numeric_not_annex() -> None:
    """Numeric '4' is not flagged as annex."""
    assert build_hierarchy("4")["is_annex"] is False


def test_build_hierarchy_annex_ancestors() -> None:
    """Annex 'A.8.1' has one ancestor."""
    assert build_hierarchy("A.8.1")["ancestors"] == ["A.8"]
