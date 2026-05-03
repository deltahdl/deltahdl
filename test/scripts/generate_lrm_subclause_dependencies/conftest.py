"""Shared fixtures for generate_lrm_subclause_dependencies tests."""

from pathlib import Path

import pytest


@pytest.fixture()
def make_lrm(tmp_path: Path) -> Path:
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm


@pytest.fixture()
def make_output(tmp_path: Path) -> Path:
    """Return a fresh output path inside ``tmp_path``."""
    return tmp_path / "graph.json"
