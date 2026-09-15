import sys
from pathlib import Path

from lib.python.test_utils import load_module_from_path

SOURCE = "VALUE = 41\n"


def _written(tmp_path: Path, name: str) -> Path:
    path = tmp_path / f"{name}.py"
    path.write_text(SOURCE)
    return path


def test_returns_the_module_the_file_defines(tmp_path: Path) -> None:
    module = load_module_from_path(
        "loaded_by_value", _written(tmp_path, "loaded_by_value"),
    )
    assert module.VALUE == 41


def test_the_module_takes_the_name_it_was_asked_for(tmp_path: Path) -> None:
    module = load_module_from_path(
        "asked_for_name", _written(tmp_path, "on_disk_name"),
    )
    assert module.__name__ == "asked_for_name"


def test_the_module_is_registered_under_that_name(tmp_path: Path) -> None:
    load_module_from_path(
        "registered_name", _written(tmp_path, "registered_name"),
    )
    assert sys.modules["registered_name"].VALUE == 41
