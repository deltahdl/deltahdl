"""Tests for invalid_citations in assert_subclause_citations."""

from collections.abc import Callable, Mapping
from pathlib import Path

from assert_subclause_citations import invalid_citations

TreeBuilder = Callable[[Mapping[str, str]], Path]


def test_a_citation_the_clause_list_lacks_is_reported(
    make_tree: TreeBuilder, clauses_file: Path,
) -> None:
    """6.20.3.1 is in no clause list, so the citation of it is reported."""
    root = make_tree({"bad.cpp": 'Subclause("6.20.3.1")'})
    reported = invalid_citations(root, clauses_file)
    assert reported == {str(root / "bad.cpp"): {"6.20.3.1"}}


def test_a_citation_the_clause_list_holds_is_not_reported(
    make_tree: TreeBuilder, clauses_file: Path,
) -> None:
    """11.4.14 is in the clause list, so nothing is reported against it."""
    root = make_tree({"good.cpp": 'Subclause("11.4.14")'})
    assert invalid_citations(root, clauses_file) == {}


def test_only_the_file_holding_the_bad_citation_is_named(
    make_tree: TreeBuilder, clauses_file: Path,
) -> None:
    """The report keys the file, so a failure says which one to open.

    Two sources cite here and one of them is wrong, so a report that named
    the tree rather than the file would leave the reader to find it.
    """
    root = make_tree({
        "good.cpp": 'Subclause("A.10")',
        "bad.cpp": 'Subclause("6.20.3.1")',
    })
    named = set(invalid_citations(root, clauses_file))
    assert named == {str(root / "bad.cpp")}
