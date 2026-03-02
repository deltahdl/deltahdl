"""Tests for implement_clause core functions."""

import subprocess
import sys
from unittest.mock import patch

import pytest

from implement_clause import invoke_implement_subclause, parse_args


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


# --- parse_args ---


def test_parse_args_clause(tmp_path) -> None:
    """--clause flag sets args.clause to the number."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1", "--organization", "o", "--repo", "r",
    ])
    assert args.clause == "4"


def test_parse_args_annex(tmp_path) -> None:
    """--annex flag sets args.annex to the letter."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--annex", "A",
        "--issue", "1", "--organization", "o", "--repo", "r",
    ])
    assert args.annex == "A"


def test_parse_args_clause_and_annex_exclusive(tmp_path) -> None:
    """--clause and --annex are mutually exclusive."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", str(lrm), "--clause", "4", "--annex", "A",
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])


def test_parse_args_missing_lrm() -> None:
    """SystemExit when --lrm points to a nonexistent file."""
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", "/no/such/file", "--clause", "4",
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])


def test_parse_args_issue_is_int(tmp_path) -> None:
    """--issue is parsed as an integer."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "42", "--organization", "o", "--repo", "r",
    ])
    assert args.issue == 42


def test_parse_args_no_clause_or_annex(tmp_path) -> None:
    """SystemExit when neither --clause nor --annex is provided."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", str(lrm),
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])


# --- invoke_implement_subclause ---


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
