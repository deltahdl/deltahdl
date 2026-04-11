"""Shared fixtures for implement_clauses tests."""

import pytest


@pytest.fixture()
def base_argv(tmp_path):
    """Return minimal valid argv for implement_clauses."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--clauses", "15=17,16=18",
        "--organization", "o", "--repo", "r",
        "--labels", "IEEE 1800-2023",
    ]
