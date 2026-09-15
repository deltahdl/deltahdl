from collections.abc import Callable, Mapping
from pathlib import Path

import pytest


@pytest.fixture()
def repo_root() -> Path:
    return Path(__file__).resolve().parents[3]


@pytest.fixture()
def clauses_file(tmp_path: Path) -> Path:
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
    def _make(files: Mapping[str, str]) -> Path:
        root = tmp_path / "tree"
        root.mkdir(exist_ok=True)
        for name, text in files.items():
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
        return root
    return _make
