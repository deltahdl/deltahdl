"""Shared subprocess stubs for pytest-based test suites."""

import subprocess
from unittest.mock import MagicMock


def stub_subprocess_success(monkeypatch):
    """Stub subprocess.run to succeed; return list of captured commands."""
    captured: list[list[str]] = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""

    def capture_run(cmd, **_kwargs):
        captured.append(list(cmd))
        return mock_result

    monkeypatch.setattr(subprocess, "run", capture_run)
    return captured


def stub_subprocess_failure(monkeypatch):
    """Stub subprocess.run to return a failure result."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "error"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )


def spy_subprocess_run(monkeypatch):
    """Spy on subprocess.run; return (kwargs_log, result_stub).

    The stub returns exit code 0 for every call.  Callers inspect
    *kwargs_log* to verify keyword arguments (e.g. ``capture_output``).
    """
    kwargs_log: list[dict] = []

    def spy_run(_cmd, **kwargs):
        kwargs_log.append(kwargs)
        result = MagicMock()
        result.returncode = 0
        return result

    monkeypatch.setattr(subprocess, "run", spy_run)
    return kwargs_log
