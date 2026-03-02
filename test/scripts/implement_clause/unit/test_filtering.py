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
