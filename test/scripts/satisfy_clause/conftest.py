"""Shared fixtures and helpers for satisfy_clause tests."""

from pathlib import Path

import pytest


@pytest.fixture()
def make_lrm(tmp_path: Path) -> Path:
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm
