"""Tests for implement_clause.filter_implementable."""

import subprocess
from unittest.mock import patch

import pytest

from implement_clause import filter_implementable

THREE_SUBCLAUSES = {"4.1": "General", "4.2": "Exec", "4.3": "Sim"}


def test_filter_implementable_returns_list() -> None:
    """Implementable subclauses from Claude response are returned."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": false, "4.2": true, "4.3": true}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert filter_implementable(
            "clause text", THREE_SUBCLAUSES,
        ) == ["4.2", "4.3"]


def test_filter_implementable_prints_count(capsys) -> None:
    """Prints how many subclauses are being filtered."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": false, "4.2": true}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        filter_implementable(
            "text", {"4.1": "General", "4.2": "Exec"},
        )
    assert "Filtering 2 subclauses" in capsys.readouterr().out


@pytest.mark.usefixtures("patch_filter_ok")
def test_filter_implementable_prints_raw_response(capsys) -> None:
    """Prints Claude's raw stdout before parsing."""
    filter_implementable("text", THREE_SUBCLAUSES)
    out = capsys.readouterr().out
    assert '"4.2": true' in out


@pytest.mark.usefixtures("patch_filter_ok")
def test_filter_implementable_prints_result(capsys) -> None:
    """Prints the implementable subclauses returned by Claude."""
    filter_implementable("text", THREE_SUBCLAUSES)
    assert "['4.2', '4.3']" in capsys.readouterr().out


def test_filter_implementable_excludes_false() -> None:
    """Subclauses marked false are excluded."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": false, "4.2": true, "4.3": false}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert filter_implementable(
            "text", THREE_SUBCLAUSES,
        ) == ["4.2"]


def test_filter_implementable_rationale_is_implementable() -> None:
    """A string rationale counts as implementable."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "Defines syntax rules", "4.2": true}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert filter_implementable(
            "text", THREE_SUBCLAUSES,
        ) == ["4.1", "4.2"]


def test_filter_implementable_prints_rationale(capsys) -> None:
    """Rationale for General/Overview subclauses is printed to stdout."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "Defines syntax rules", "4.2": true}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        filter_implementable("text", THREE_SUBCLAUSES)
    assert "Rationale for 4.1: Defines syntax rules" in capsys.readouterr().out


def test_filter_implementable_empty() -> None:
    """Empty list when Claude returns no implementable subclauses."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout='{"4.1": false}\n', stderr="",
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
