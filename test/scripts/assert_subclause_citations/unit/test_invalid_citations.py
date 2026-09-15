from collections.abc import Callable, Mapping
from pathlib import Path

from assert_subclause_citations import invalid_citations

TreeBuilder = Callable[[Mapping[str, str]], Path]


def test_a_citation_the_clause_list_lacks_is_reported(
    make_tree: TreeBuilder, clauses_file: Path,
) -> None:
    root = make_tree({"bad.cpp": 'Subclause("6.20.3.1")'})
    reported = invalid_citations(root, clauses_file)
    assert reported == {str(root / "bad.cpp"): {"6.20.3.1"}}


def test_a_citation_the_clause_list_holds_is_not_reported(
    make_tree: TreeBuilder, clauses_file: Path,
) -> None:
    root = make_tree({"good.cpp": 'Subclause("11.4.14")'})
    assert not invalid_citations(root, clauses_file)


def test_only_the_file_holding_the_bad_citation_is_named(
    make_tree: TreeBuilder, clauses_file: Path,
) -> None:
    root = make_tree({
        "good.cpp": 'Subclause("A.10")',
        "bad.cpp": 'Subclause("6.20.3.1")',
    })
    named = set(invalid_citations(root, clauses_file))
    assert named == {str(root / "bad.cpp")}
