"""Shared fixtures for implement_clause unit tests."""

import subprocess
from pathlib import Path
from unittest.mock import patch

import pytest


@pytest.fixture()
def clause_argv(tmp_path: Path) -> list[str]:
    """Return argv for a --clause 4 invocation with a dummy LRM file."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1", "--organization", "o", "--repo", "r",
    ]


@pytest.fixture()
def invoke_subprocess_ok():
    """Patch subprocess.run to return success; yield mock_run."""
    with patch("implement_clause.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=[], returncode=0,
        )
        yield mock_run


@pytest.fixture()
def patch_filter_ok():
    """Patch subprocess to return ["4.2", "4.3"] for filter calls."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout='["4.2", "4.3"]\n', stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        yield
