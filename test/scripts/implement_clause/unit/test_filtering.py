"""Tests for implement_clause.filter_implementable."""

import subprocess
from unittest.mock import patch

import pytest

THREE_SUBCLAUSES = {"4.1": "General", "4.2": "Exec", "4.3": "Sim"}


@pytest.mark.usefixtures("patch_filter_ok")
def test_filter_implementable_returns_list(ic) -> None:
    """Implementable subclauses from Claude response are returned."""
    assert ic.filter_implementable(
        "clause text", THREE_SUBCLAUSES,
    ) == ["4.2", "4.3"]


def test_filter_implementable_prints_count(ic, capsys) -> None:
    """Prints how many subclauses are being filtered."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": false, "4.2": true}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        ic.filter_implementable(
            "text", {"4.1": "General", "4.2": "Exec"},
        )
    assert "Filtering 2 subclauses" in capsys.readouterr().out


@pytest.mark.usefixtures("patch_filter_ok")
def test_filter_implementable_prints_raw_response(ic, capsys) -> None:
    """Prints Claude's raw stdout before parsing."""
    ic.filter_implementable("text", THREE_SUBCLAUSES)
    out = capsys.readouterr().out
    assert '"4.2": true' in out


@pytest.mark.usefixtures("patch_filter_ok")
def test_filter_implementable_prints_result(ic, capsys) -> None:
    """Prints the implementable subclauses returned by Claude."""
    ic.filter_implementable("text", THREE_SUBCLAUSES)
    assert "['4.2', '4.3']" in capsys.readouterr().out


def test_filter_implementable_excludes_false(ic) -> None:
    """Subclauses marked false are excluded."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": false, "4.2": true, "4.3": false}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert ic.filter_implementable(
            "text", THREE_SUBCLAUSES,
        ) == ["4.2"]


def test_filter_implementable_rationale_is_implementable(ic) -> None:
    """A string rationale counts as implementable."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "Defines syntax rules", "4.2": true}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert ic.filter_implementable(
            "text", THREE_SUBCLAUSES,
        ) == ["4.1", "4.2"]


def test_filter_implementable_prints_rationale(ic, capsys) -> None:
    """Rationale for General/Overview subclauses is printed to stdout."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "Defines syntax rules", "4.2": true}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        ic.filter_implementable("text", THREE_SUBCLAUSES)
    assert "Rationale for 4.1: Defines syntax rules" in capsys.readouterr().out


def test_filter_implementable_strips_markdown_fences(ic) -> None:
    """Claude response wrapped in ```json fences is parsed correctly."""
    fenced = '```json\n{"4.1": false, "4.2": true}\n```\n'
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout=fenced, stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert ic.filter_implementable("text", THREE_SUBCLAUSES) == ["4.2"]


def test_filter_implementable_empty(ic) -> None:
    """Empty list when Claude returns no implementable subclauses."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout='{"4.1": false}\n', stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        assert ic.filter_implementable("text", {"4.1": "General"}) == []


def test_filter_implementable_failure(ic) -> None:
    """SystemExit on Claude failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            ic.filter_implementable("text", {"4.1": "General"})


def test_filter_implementable_failure_prints_error(ic, capsys) -> None:
    """Prints Claude failure message to stderr."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        try:
            ic.filter_implementable("text", {"4.1": "General"})
        except SystemExit:
            pass
    assert "Claude failed" in capsys.readouterr().err
