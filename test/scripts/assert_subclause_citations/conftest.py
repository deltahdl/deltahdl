"""Fixtures specific to assert_subclause_citations tests."""

from collections.abc import Callable, Mapping
from pathlib import Path

import pytest


@pytest.fixture()
def repo_root() -> Path:
    """The repository root, found from this file and not from the cwd."""
    return Path(__file__).resolve().parents[3]


@pytest.fixture()
def clauses_file(tmp_path: Path) -> Path:
    """Write a two-clause list and return its path.

    The file holds a comment line, a blank line and the identifiers 11.4.14
    and A.10, which are the three shapes known_subclauses tells apart. Both
    identifiers are ones IEEE 1800-2023 really defines, so a test expecting a
    citation accepted names a clause the standard has rather than a string
    this fixture invented.
    """
    path = tmp_path / "clauses.txt"
    path.write_text(
        "# Two clause identifiers of IEEE 1800-2023, one per line.\n"
        "#\n"
        "\n"
        "11.4.14\n"
        "A.10\n"
    )
    return path


@pytest.fixture()
def make_tree(tmp_path: Path) -> Callable[[Mapping[str, str]], Path]:
    """Return a builder that writes a source tree and answers its root.

    Each key of the mapping is a path relative to the root, and each value is
    the text written at that path. The root is a directory of its own beneath
    tmp_path, so a clause list written beside it is never scanned as part of
    it.
    """
    def _make(files: Mapping[str, str]) -> Path:
        root = tmp_path / "tree"
        root.mkdir(exist_ok=True)
        for name, text in files.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return root
    return _make
