"""Shared subprocess stubs for pytest-based test suites."""

import subprocess
from typing import Any
from unittest.mock import MagicMock

import pytest


def stub_subprocess_success(monkeypatch: pytest.MonkeyPatch) -> list[list[str]]:
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


def stub_subprocess_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    """Stub subprocess.run to return a failure result."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "error"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )


def spy_subprocess_run(monkeypatch: pytest.MonkeyPatch) -> list[dict[str, Any]]:
    """Spy on subprocess.run; return (kwargs_log, result_stub).

    The stub returns exit code 0 for every call.  Callers inspect
    *kwargs_log* to verify keyword arguments (e.g. ``capture_output``).
    """
    kwargs_log: list[dict[str, Any]] = []

    def spy_run(_cmd, **kwargs):
        kwargs_log.append(kwargs)
        result = MagicMock()
        result.returncode = 0
        return result

    monkeypatch.setattr(subprocess, "run", spy_run)
    return kwargs_log
