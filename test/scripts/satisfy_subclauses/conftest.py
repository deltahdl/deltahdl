"""Shared fixtures and helpers for satisfy_subclauses tests."""

import pytest


@pytest.fixture()
def make_lrm(tmp_path):
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm
