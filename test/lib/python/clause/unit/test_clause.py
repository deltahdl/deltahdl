"""Tests for lib.clause."""

from lib.python.clause import (
    STAGE_TO_PREFIX,
    build_hierarchy,
    clause_to_filename,
)


# --- STAGE_TO_PREFIX ---


def test_stage_to_prefix_has_all_stages() -> None:
    """Contains all six pipeline stages."""
    assert set(STAGE_TO_PREFIX) == {
        "preprocessor", "lexer", "parser",
        "elaborator", "simulator", "synthesizer",
    }


def test_stage_to_prefix_values_are_test_prefixes() -> None:
    """Every value starts with test_ and ends with _."""
    assert all(
        v.startswith("test_") and v.endswith("_")
        for v in STAGE_TO_PREFIX.values()
    )


# --- clause_to_filename ---


def test_clause_to_filename_regular() -> None:
    """Regular clause becomes padded clause filename."""
    assert clause_to_filename("test_parser_", "6.1") == "test_parser_clause_06_01"


def test_clause_to_filename_non_lrm_with_topic() -> None:
    """Non-LRM with topic uses the topic."""
    assert clause_to_filename("test_non_lrm_", "non-lrm:aig") == "test_non_lrm_aig"


def test_clause_to_filename_non_lrm_no_topic() -> None:
    """Non-LRM without topic defaults to misc."""
    assert clause_to_filename("test_non_lrm_", "non-lrm") == "test_non_lrm_misc"


def test_clause_to_filename_bare_annex() -> None:
    """Single letter becomes bare annex filename."""
    assert clause_to_filename("test_parser_", "A") == "test_parser_annex_a"


def test_clause_to_filename_annex_subclause() -> None:
    """Annex subclause becomes padded annex filename."""
    assert clause_to_filename("test_parser_", "A.1.3") == "test_parser_annex_a_01_03"


# --- build_hierarchy ---


def test_build_hierarchy_numeric_depth_1() -> None:
    """Clause '4' produces depth-1 numeric hierarchy."""
    assert build_hierarchy("4")["clause_number"] == "4"


def test_build_hierarchy_numeric_no_ancestors() -> None:
    """Depth-2 clause '4.1' has no ancestors."""
    assert build_hierarchy("4.1")["ancestors"] == []


def test_build_hierarchy_numeric_ancestors() -> None:
    """Depth-3 clause '6.24.1' has one ancestor."""
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
