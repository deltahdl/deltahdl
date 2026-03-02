"""Tests for implement_clause core functions."""

import subprocess
import sys
from unittest.mock import patch

import pytest

from implement_clause import invoke_implement_subclause


def test_invoke_implement_subclause_calls_subprocess() -> None:
    """Correct command is passed to subprocess.run."""
    with patch("implement_clause.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=[], returncode=0,
        )
        invoke_implement_subclause(
            lrm="/path/lrm.txt",
            subclause="4.2",
            issue=123,
            organization="deltahdl",
            repo="deltahdl",
        )
    assert mock_run.call_args[0][0] == [
        sys.executable, "-m", "implement_subclause",
        "--lrm", "/path/lrm.txt",
        "--subclause", "4.2",
        "--issue", "123",
        "--organization", "deltahdl",
        "--repo", "deltahdl",
    ]


def test_invoke_implement_subclause_failure() -> None:
    """SystemExit on non-zero return code."""
    with patch("implement_clause.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=[], returncode=1,
        )
        with pytest.raises(SystemExit):
            invoke_implement_subclause(
                lrm="/path/lrm.txt",
                subclause="4.2",
                issue=123,
                organization="deltahdl",
                repo="deltahdl",
            )
