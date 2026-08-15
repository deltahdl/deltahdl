"""Tests for citations_in_tree in assert_subclause_citations."""

from collections.abc import Callable, Mapping
from pathlib import Path

from assert_subclause_citations import citations_in_tree

TreeBuilder = Callable[[Mapping[str, str]], Path]


def test_a_citing_cpp_file_is_keyed_by_its_path(
    make_tree: TreeBuilder,
) -> None:
    """A .cpp file is read, and its citations answer under its own path."""
    root = make_tree({"a.cpp": 'Subclause("11.4.14")'})
    assert citations_in_tree(root) == {str(root / "a.cpp"): {"11.4.14"}}


def test_a_citing_header_is_keyed_by_its_path(
    make_tree: TreeBuilder,
) -> None:
    """A .h file is read as a .cpp file is, since both hold emission sites."""
    root = make_tree({"b.h": 'Subclause("A.10")'})
    assert citations_in_tree(root) == {str(root / "b.h"): {"A.10"}}


def test_a_citing_source_in_a_subdirectory_is_found(
    make_tree: TreeBuilder,
) -> None:
    """The scan descends, so a source below the root is read too."""
    root = make_tree({"sub/deep.cpp": 'Subclause("1.5")'})
    found = citations_in_tree(root)
    assert found == {str(root / "sub" / "deep.cpp"): {"1.5"}}


def test_a_file_that_is_neither_cpp_nor_h_is_not_read(
    make_tree: TreeBuilder,
) -> None:
    """A citation written in a .txt file is no citation the program makes."""
    root = make_tree({"notes.txt": 'Subclause("11.4.14")'})
    assert not citations_in_tree(root)


def test_a_source_citing_nothing_is_left_out(
    make_tree: TreeBuilder,
) -> None:
    """A file with no citation is absent rather than present and empty."""
    root = make_tree({"quiet.cpp": "int main() { return 0; }"})
    assert not citations_in_tree(root)
