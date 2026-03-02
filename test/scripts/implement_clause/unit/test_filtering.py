"""Tests for implement_clause.filter_implementable."""

import subprocess
from unittest.mock import patch

import pytest

from implement_clause import filter_implementable

THREE_SUBCLAUSES = {"4.1": "General", "4.2": "Exec", "4.3": "Sim"}


def test_filter_implementable_returns_list() -> None:
    """Implementable subclauses from Claude response are returned."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout='["4.2", "4.3"]\n', stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert filter_implementable(
            "clause text", THREE_SUBCLAUSES,
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
    assert "Filtering 2 subclauses" in capsys.readouterr().out


def test_filter_implementable_prints_raw_response(
    patch_filter_ok, capsys,
) -> None:
    """Prints Claude's raw stdout before parsing."""
    filter_implementable("text", THREE_SUBCLAUSES)
    assert '["4.2", "4.3"]' in capsys.readouterr().out


def test_filter_implementable_prints_result(
    patch_filter_ok, capsys,
) -> None:
    """Prints the implementable subclauses returned by Claude."""
    filter_implementable("text", THREE_SUBCLAUSES)
    assert "['4.2', '4.3']" in capsys.readouterr().out


def test_filter_implementable_empty() -> None:
    """Empty list when Claude returns no implementable subclauses."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout="[]\n", stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert filter_implementable("text", {"4.1": "General"}) == []


def test_filter_implementable_failure() -> None:
    """SystemExit on Claude failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            filter_implementable("text", {"4.1": "General"})


def test_filter_implementable_failure_prints_error(capsys) -> None:
    """Prints Claude failure message to stderr."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        try:
            filter_implementable("text", {"4.1": "General"})
        except SystemExit:
            pass
    assert "Claude failed" in capsys.readouterr().err
