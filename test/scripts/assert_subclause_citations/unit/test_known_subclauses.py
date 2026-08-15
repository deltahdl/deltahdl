"""Tests for known_subclauses in assert_subclause_citations."""

from pathlib import Path

from assert_subclause_citations import known_subclauses


def test_only_the_identifiers_are_returned(clauses_file: Path) -> None:
    """A line opening with # and a blank line each name no clause."""
    assert known_subclauses(clauses_file) == {"11.4.14", "A.10"}


def test_the_committed_list_holds_a_clause_the_standard_defines() -> None:
    """clauses.txt holds §11.4.14, which IEEE 1800-2023 defines."""
    assert "11.4.14" in known_subclauses()


def test_the_committed_list_lacks_a_number_with_no_clause() -> None:
    """clauses.txt lacks 6.20.3.1, the number #3068 was filed over.

    Every test that expects a citation reported invalid cites that number,
    and each proves nothing unless the list really is without it.
    """
    assert "6.20.3.1" not in known_subclauses()
