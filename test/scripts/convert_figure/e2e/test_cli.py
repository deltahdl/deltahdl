"""End-to-end tests for the convert_figure CLI."""

import subprocess
import sys
from pathlib import Path

_SCRIPT = str(
    Path(__file__).resolve().parents[4] / "scripts" / "convert_figure.py",
)


# ---- Helpers ---------------------------------------------------------------


def _invoke(*args):
    """Run convert_figure as a child process."""
    return subprocess.run(
        [sys.executable, _SCRIPT, *args],
        capture_output=True,
        text=True,
        check=False,
    )


# ---- CLI argument errors ---------------------------------------------------


def test_no_args_prints_usage():
    """Running with no arguments prints usage to stderr."""
    assert "usage:" in _invoke().stderr


def test_missing_lrm_flag_reported():
    """Omitting --lrm reports the missing argument."""
    assert "--lrm" in _invoke("--clause", "4").stderr


def test_missing_clause_flag_reported():
    """Omitting --clause reports the missing argument."""
    assert "--clause" in _invoke("--lrm", "dummy.pdf").stderr


def test_invalid_clause_reported(tmp_path):
    """An invalid clause format is reported."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_bytes(b"")
    assert "Invalid clause" in _invoke(
        "--lrm", str(lrm), "--clause", "0.1",
    ).stderr


def test_nonexistent_lrm_reports_error():
    """Pointing --lrm at a missing path reports an error."""
    assert "not found" in _invoke(
        "--lrm", "/no/such/file.pdf", "--clause", "4",
    ).stderr
