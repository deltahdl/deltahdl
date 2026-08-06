"""Tests for lib.python.test_utils.load_module_from_path.

The function imports a file that is not on ``sys.path``, which is what
``test/scripts/conftest.py`` needs to reach a script package by location
rather than by name. The claims below are that the module it returns is
the file's, that the name it was asked for is the name the module gets,
and that the module is registered so a later import finds the same one.
"""

import sys
from pathlib import Path

from lib.python.test_utils import load_module_from_path

SOURCE = "VALUE = 41\n"


def _written(tmp_path: Path, name: str) -> Path:
    """Write *SOURCE* to a file named after *name* and return its path."""
    path = tmp_path / f"{name}.py"
    path.write_text(SOURCE)
    return path


def test_returns_the_module_the_file_defines(tmp_path: Path) -> None:
    """The loaded module carries what the file assigned."""
    module = load_module_from_path(
        "loaded_by_value", _written(tmp_path, "loaded_by_value"),
    )
    assert module.VALUE == 41


def test_the_module_takes_the_name_it_was_asked_for(tmp_path: Path) -> None:
    """The module is named by the caller rather than by the file."""
    module = load_module_from_path(
        "asked_for_name", _written(tmp_path, "on_disk_name"),
    )
    assert module.__name__ == "asked_for_name"


def test_the_module_is_registered_under_that_name(tmp_path: Path) -> None:
    """A later import of the same name finds the module already loaded."""
    load_module_from_path(
        "registered_name", _written(tmp_path, "registered_name"),
    )
    assert sys.modules["registered_name"].VALUE == 41
