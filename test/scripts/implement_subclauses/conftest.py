"""Shared fixtures for implement_subclauses tests."""

import pytest


@pytest.fixture()
def base_argv(tmp_path):
    """Return minimal valid argv for implement_subclauses."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--subclauses", "6.1,6.2",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ]
