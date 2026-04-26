"""Tests for lib.python.satisfy.orchestrator (shared orchestrator helpers)."""

import argparse
from unittest.mock import patch

import pytest

from lib.python.satisfy.orchestrator import (
    add_in_progress_arg,
    parse_in_progress,
    run_capture,
)
from lib.python.test_fixtures.satisfy import stub_completed


# --- add_in_progress_arg ---------------------------------------------------


def test_add_in_progress_arg_default() -> None:
    """--in-progress defaults to an empty string."""
    parser = argparse.ArgumentParser()
    add_in_progress_arg(parser)
    args = parser.parse_args([])
    assert args.in_progress == ""


def test_add_in_progress_arg_value() -> None:
    """--in-progress accepts a comma-separated value."""
    parser = argparse.ArgumentParser()
    add_in_progress_arg(parser)
    args = parser.parse_args(["--in-progress", "33.4,33.5"])
    assert args.in_progress == "33.4,33.5"


# --- parse_in_progress -----------------------------------------------------


def test_parse_in_progress_empty() -> None:
    """An empty string parses to an empty list."""
    assert parse_in_progress("") == []


def test_parse_in_progress_single() -> None:
    """A single value parses to a one-element list."""
    assert parse_in_progress("33.4") == ["33.4"]


def test_parse_in_progress_multiple() -> None:
    """Multiple values parse with whitespace stripped."""
    assert parse_in_progress("33.4, 33.5") == ["33.4", "33.5"]


def test_parse_in_progress_skips_blanks() -> None:
    """Empty fragments between commas are dropped."""
    assert parse_in_progress("a,,b") == ["a", "b"]


# --- run_capture -----------------------------------------------------------


def test_run_capture_returns_stdout() -> None:
    """run_capture returns the subprocess stdout on success."""
    with patch(
        "lib.python.satisfy.orchestrator.subprocess.run",
        return_value=stub_completed(stdout="payload"),
    ):
        assert run_capture(["echo", "x"]) == "payload"


def test_run_capture_exits_on_nonzero() -> None:
    """run_capture exits non-zero when the subprocess fails."""
    with patch(
        "lib.python.satisfy.orchestrator.subprocess.run",
        return_value=stub_completed(returncode=2),
    ):
        with pytest.raises(SystemExit):
            run_capture(["false"])


def test_run_capture_dumps_stderr_on_nonzero(capsys) -> None:
    """run_capture echoes the subprocess stderr when it fails."""
    with patch(
        "lib.python.satisfy.orchestrator.subprocess.run",
        return_value=stub_completed(
            returncode=1, stderr="UNIQUE_RUN_CAPTURE_STDERR",
        ),
    ):
        try:
            run_capture(["false"])
        except SystemExit:
            pass
    assert "UNIQUE_RUN_CAPTURE_STDERR" in capsys.readouterr().err
