"""Shared fixtures for implement_clause unit tests."""

from pathlib import Path

import pytest


@pytest.fixture()
def clause_argv(tmp_path: Path) -> list[str]:
    """Return argv for --clause 4 WITH --issue (skip discovery path)."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1",
        "--organization", "o", "--repo", "r",
        "--labels", "IEEE 1800-2023",
    ]


@pytest.fixture()
def clause_argv_no_issue(tmp_path: Path) -> list[str]:
    """Return argv for --clause 4 WITHOUT --issue (discovery path)."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--clause", "4",
        "--organization", "o", "--repo", "r",
        "--labels", "IEEE 1800-2023",
    ]
