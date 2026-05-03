"""Shared fixtures for document_dependency_graph tests."""

import pytest


@pytest.fixture()
def make_lrm(tmp_path):
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm


@pytest.fixture()
def make_output(tmp_path):
    """Return a fresh output path inside ``tmp_path``."""
    return tmp_path / "graph.json"
