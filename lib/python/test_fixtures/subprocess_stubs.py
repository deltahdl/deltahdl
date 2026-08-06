"""Shared subprocess stubs for pytest-based test suites."""

import subprocess
from typing import Any
from unittest.mock import MagicMock

import pytest


def make_stub_completed(
    stdout: str = "", returncode: int = 0, stderr: str = "",
) -> MagicMock:
    """Return a stubbed ``CompletedProcess``-shaped MagicMock."""
    completed = MagicMock()
    completed.returncode = returncode
    completed.stdout = stdout
    completed.stderr = stderr
    return completed


def stub_subprocess_success(monkeypatch: pytest.MonkeyPatch) -> list[list[str]]:
    """Stub subprocess.run to succeed; return list of captured commands."""
    captured: list[list[str]] = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""

    def capture_run(cmd: Any, **_kwargs: Any) -> MagicMock:
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
