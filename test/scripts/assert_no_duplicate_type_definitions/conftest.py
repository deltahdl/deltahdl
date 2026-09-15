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
    return module_loader("assert_no_duplicate_type_definitions", _INIT)


@pytest.fixture()
def header_tree(tmp_path: Path) -> Callable[..., Path]:
    def write(**files: str) -> Path:
        root = tmp_path / "tree"
        for name, text in files.items():
            path = root / name.replace("__", "/")
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        root.mkdir(parents=True, exist_ok=True)
        return root

    return write
