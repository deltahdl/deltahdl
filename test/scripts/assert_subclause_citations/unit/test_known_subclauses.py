from pathlib import Path

from assert_subclause_citations import known_subclauses


def test_only_the_identifiers_are_returned(clauses_file: Path) -> None:
    assert known_subclauses(clauses_file) == {"11.4.14", "A.10"}


def test_the_committed_list_holds_a_clause_the_standard_defines() -> None:
    assert "11.4.14" in known_subclauses()


def test_the_committed_list_lacks_a_number_with_no_clause() -> None:
    assert "6.20.3.1" not in known_subclauses()
