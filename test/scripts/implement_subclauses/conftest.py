"""Shared fixtures for implement_subclauses tests."""

import pytest


@pytest.fixture()
def base_argv(tmp_path):
    """Return minimal valid argv for implement_subclauses."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--issues", "100,101",
        "--organization", "o", "--repo", "r",
    ]
