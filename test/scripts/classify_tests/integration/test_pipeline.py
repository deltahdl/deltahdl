"""Integration tests for the classify_tests pipeline."""

import subprocess
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

from lib.python.test_fixtures.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
)


# ---- Helpers ---------------------------------------------------------------


def _pipeline_args(**overrides):
    """Build args for _run."""
    defaults = {
        "file": "/path/to/test.cpp",
        "tests": "A,B,C",
        "output_dir": "/out",
        "lrm": "/lrm.txt",
        "issue": None,
        "organization": "testorg",
        "repo": "testrepo",
        "dry_run": False,
        "no_commit": False,
        "max_lines": 1000,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


# ---- Batch processing ------------------------------------------------------


def test_processes_all_tests(monkeypatch, cts):
    """Pipeline invokes classify_test for each of three tests."""
    log = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="A,B,C"))
    assert len(log) == 3


def test_each_call_has_distinct_test_name(monkeypatch, cts):
    """Each subprocess call targets a different test name."""
    log = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="Alpha,Beta"))
    names = [c[c.index("--test") + 1] for c in log]
    assert names == ["Alpha", "Beta"]


def test_flags_propagated(monkeypatch, cts):
    """Optional flags are forwarded to classify_test calls."""
    log = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="T", dry_run=True))
    assert "--dry-run" in log[0]


# ---- Error handling --------------------------------------------------------


def test_stops_after_first_failure(monkeypatch, cts):
    """Only one subprocess call is made when the first test fails."""
    captured = []

    def failing_run(cmd, **_kw):
        captured.append(cmd)
        m = MagicMock()
        m.returncode = 1
        m.stdout, m.stderr = "", ""
        return m

    monkeypatch.setattr(subprocess, "run", failing_run)
    try:
        getattr(cts, "_run")(_pipeline_args(tests="A,B,C"))
    except SystemExit:
        pass
    assert len(captured) == 1


def test_exits_on_failure(monkeypatch, cts):
    """SystemExit is raised when subprocess fails."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        getattr(cts, "_run")(_pipeline_args(tests="A"))


# ---- Single test -----------------------------------------------------------


def test_single_test_succeeds(monkeypatch, cts):
    """Single-test batch succeeds without error."""
    log = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="Only"))
    assert len(log) == 1


# ---- Progress output -------------------------------------------------------


def test_progress_shows_index_and_total(monkeypatch, cts, capsys):
    """Progress line shows correct index and total."""
    stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="A,B,C"))
    assert "Processing test 1/3: A" in capsys.readouterr().out
