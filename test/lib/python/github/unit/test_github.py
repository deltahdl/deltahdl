"""Tests for lib.github."""

from lib.python.github import (
    extract_subclause_from_title,
    format_subclause_label,
)


# --- extract_subclause_from_title ---


def test_extract_subclause_numeric() -> None:
    """Extracts numeric subclause from title."""
    assert extract_subclause_from_title("... §3.12.1 ...") == "3.12.1"


def test_extract_subclause_annex() -> None:
    """Extracts annex subclause from title."""
    assert extract_subclause_from_title("... A.1.1 ...") == "A.1.1"


def test_extract_subclause_bare_annex() -> None:
    """Extracts a top-level annex letter from an ``Annex B`` title."""
    assert extract_subclause_from_title(
        "Implement IEEE 1800-2023 Annex B — Keywords"
    ) == "B"


def test_extract_subclause_bare_annex_not_from_acronym() -> None:
    """A stray capital (e.g. ``IEEE``) is not mistaken for an annex letter."""
    assert extract_subclause_from_title("Implement IEEE spec") == ""


def test_extract_subclause_not_found() -> None:
    """Returns empty string when no subclause found."""
    assert extract_subclause_from_title("Random title") == ""


# ---- format_subclause_label ------------------------------------------------


def test_format_subclause_label_numeric() -> None:
    """Numeric subclauses get the section sign prefix."""
    assert format_subclause_label("3.14.1") == "§3.14.1"


def test_format_subclause_label_annex() -> None:
    """Annex subclauses use bare identifiers without section sign."""
    assert format_subclause_label("A.1.1") == "A.1.1"
