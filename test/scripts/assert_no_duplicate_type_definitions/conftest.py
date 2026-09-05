"""Fixtures specific to assert_no_duplicate_type_definitions tests."""

from collections.abc import Callable
from pathlib import Path
from types import ModuleType

import pytest

_INIT = (
    Path(__file__).resolve().parents[3]
    / "scripts" / "assert_no_duplicate_type_definitions" / "__init__.py"
)


@pytest.fixture()
def andt(module_loader: Callable[[str, Path], ModuleType]) -> ModuleType:
    """Load the assert_no_duplicate_type_definitions module."""
    return module_loader("assert_no_duplicate_type_definitions", _INIT)


@pytest.fixture()
def header_tree(tmp_path: Path) -> Callable[..., Path]:
    """Return a factory writing headers into a root and returning that root.

    Called with keyword arguments naming each file and holding its text, so a
    test says only which headers exist and what is in them. A name carrying a
    directory is written under it, which is how a test puts two headers in two
    trees.
    """
    def write(**files: str) -> Path:
        root = tmp_path / "tree"
        for name, text in files.items():
            path = root / name.replace("__", "/")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        root.mkdir(parents=True, exist_ok=True)
        return root

    return write
