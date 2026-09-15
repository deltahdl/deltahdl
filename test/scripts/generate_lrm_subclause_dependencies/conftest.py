from pathlib import Path

import pytest


@pytest.fixture()
def make_lrm(tmp_path: Path) -> Path:
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm


@pytest.fixture()
def make_output(tmp_path: Path) -> Path:
    return tmp_path / "graph.json"
