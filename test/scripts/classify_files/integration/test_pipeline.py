"""Integration tests for the classify_files pipeline."""

import subprocess
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

import classify_files

_run = getattr(classify_files, "_run")


# ---- Helpers ---------------------------------------------------------------


_ARGS_DEFAULTS = {
    "issue": 61,
    "organization": "testorg",
    "repo": "testrepo",
    "max_lines": 1000,
}


def _pipeline_args(**overrides):
    """Build args for _run."""
    result = {
        "files": "a.cpp,b.cpp",
        "output_dir": "/out",
        "lrm": "/lrm.txt",
        **_ARGS_DEFAULTS, **overrides,
    }
    return SimpleNamespace(**result)


def _mock_run_ok(monkeypatch):
    """Stub subprocess.run to succeed; return command log."""
    log: list[list[str]] = []

    def ok_run(cmd, **_kw):
        log.append(list(cmd))
        result = MagicMock()
        result.returncode, result.stdout, result.stderr = 0, "", ""
        return result

    monkeypatch.setattr(subprocess, "run", ok_run)
    return log


def _mock_run_fail_first(monkeypatch):
    """Stub subprocess.run to fail on the first call only."""
    call_count: list[int] = [0]

    def fail_first(_cmd, **_kw):
        call_count[0] += 1
        result = MagicMock()
        result.stdout, result.stderr = "", "fail"
        result.returncode = 1 if call_count[0] == 1 else 0
        return result

    monkeypatch.setattr(subprocess, "run", fail_first)


def _stub_tick(monkeypatch):
    """Stub tick_file_checkbox; return list of filenames ticked."""
    ticked: list[str] = []
    monkeypatch.setattr(
        classify_files, "tick_file_checkbox",
        lambda _o, _r, _i, fn: ticked.append(fn),
    )
    return ticked


# ---- Pipeline tests --------------------------------------------------------


def test_processes_two_files(monkeypatch):
    """Pipeline invokes classify_file for each of two files."""
    log = _mock_run_ok(monkeypatch)
    _stub_tick(monkeypatch)
    _run(_pipeline_args())
    assert len(log) == 2


def test_each_call_targets_distinct_file(monkeypatch):
    """Each subprocess call targets a different file."""
    log = _mock_run_ok(monkeypatch)
    _stub_tick(monkeypatch)
    _run(_pipeline_args())
    files = [c[c.index("--file") + 1] for c in log]
    assert files == ["a.cpp", "b.cpp"]


def test_halts_on_first_failure(monkeypatch):
    """Pipeline halts immediately when first file fails."""
    _mock_run_fail_first(monkeypatch)
    _stub_tick(monkeypatch)
    with pytest.raises(SystemExit):
        _run(_pipeline_args())


def test_ticks_checkbox_after_each_file(monkeypatch):
    """Ticks checkbox after each successful file."""
    _mock_run_ok(monkeypatch)
    ticked = _stub_tick(monkeypatch)
    _run(_pipeline_args())
    assert ticked == ["a.cpp", "b.cpp"]
