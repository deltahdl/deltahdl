"""Integration tests for the classify_tests pipeline."""

import subprocess
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock

import pytest

from classify_tests.test_helpers import make_args as _pipeline_args
from lib.python.test_fixtures.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
)


# ---- Batch processing ------------------------------------------------------


def test_processes_all_tests(
    monkeypatch: pytest.MonkeyPatch, cts: ModuleType,
) -> None:
    """Pipeline invokes classify_test for each of three tests."""
    log = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="S.A,S.B,S.C"))
    assert len(log) == 3


def test_each_call_has_distinct_test_name(
    monkeypatch: pytest.MonkeyPatch, cts: ModuleType,
) -> None:
    """Each subprocess call targets a different test name."""
    log = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="S.Alpha,S.Beta"))
    names = [c[c.index("--test") + 1] for c in log]
    assert names == ["Alpha", "Beta"]


def test_each_call_has_suite_flag(
    monkeypatch: pytest.MonkeyPatch, cts: ModuleType,
) -> None:
    """Each subprocess call includes --suite."""
    log = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="MySuite.Alpha,MySuite.Beta"))
    suites = [c[c.index("--suite") + 1] for c in log]
    assert suites == ["MySuite", "MySuite"]


def test_flags_propagated(
    monkeypatch: pytest.MonkeyPatch, cts: ModuleType,
) -> None:
    """Optional flags are forwarded to classify_test calls."""
    log = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="S.T", dry_run=True))
    assert "--dry-run" in log[0]


# ---- Error handling --------------------------------------------------------


def test_stops_after_first_failure(
    monkeypatch: pytest.MonkeyPatch, cts: ModuleType,
) -> None:
    """Only one subprocess call is made when the first test fails."""
    captured: list[list[str]] = []

    def failing_run(cmd: list[str], **_kw: Any) -> MagicMock:
        captured.append(cmd)
        m = MagicMock()
        m.returncode = 1
        m.stdout, m.stderr = "", ""
        return m

    monkeypatch.setattr(subprocess, "run", failing_run)
    try:
        getattr(cts, "_run")(_pipeline_args(tests="S.A,S.B,S.C"))
    except SystemExit:
        pass
    assert len(captured) == 1


def test_exits_on_failure(
    monkeypatch: pytest.MonkeyPatch, cts: ModuleType,
) -> None:
    """SystemExit is raised when subprocess fails."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        getattr(cts, "_run")(_pipeline_args(tests="S.A"))


# ---- Single test -----------------------------------------------------------


def test_single_test_succeeds(
    monkeypatch: pytest.MonkeyPatch, cts: ModuleType,
) -> None:
    """Single-test batch succeeds without error."""
    log = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="S.Only"))
    assert len(log) == 1


# ---- Progress output -------------------------------------------------------


def test_progress_shows_index_and_total(
    monkeypatch: pytest.MonkeyPatch,
    cts: ModuleType,
    capsys: pytest.CaptureFixture[str],
) -> None:
    """Progress line shows correct index and total."""
    stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_pipeline_args(tests="S.A,S.B,S.C"))
    assert "Processing test 1/3: S.A" in capsys.readouterr().out
