"""Tests for implement_clause.filter_implementable."""

import subprocess
from unittest.mock import patch

import pytest

from implement_clause import filter_implementable


def test_filter_implementable_returns_list() -> None:
    """Implementable subclauses from Claude response are returned."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout='["4.2", "4.3"]\n', stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert filter_implementable(
            "clause text",
            {"4.1": "General", "4.2": "Exec", "4.3": "Sim"},
        ) == ["4.2", "4.3"]


def test_filter_implementable_prints_count(capsys) -> None:
    """Prints how many subclauses are being filtered."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout='["4.2"]\n', stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        filter_implementable(
            "text", {"4.1": "General", "4.2": "Exec"},
        )
    assert "Filtering 2 subclauses" in capsys.readouterr().err


def test_filter_implementable_prints_result(capsys) -> None:
    """Prints the implementable subclauses returned by Claude."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout='["4.2", "4.3"]\n', stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        filter_implementable(
            "text",
            {"4.1": "General", "4.2": "Exec", "4.3": "Sim"},
        )
    assert "['4.2', '4.3']" in capsys.readouterr().err


def test_filter_implementable_empty() -> None:
    """Empty list when Claude returns no implementable subclauses."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout="[]\n", stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert filter_implementable("text", {"4.1": "General"}) == []


def test_filter_implementable_failure(capsys) -> None:
    """SystemExit and stderr message on Claude failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            filter_implementable("text", {"4.1": "General"})
    assert "Claude failed" in capsys.readouterr().err
