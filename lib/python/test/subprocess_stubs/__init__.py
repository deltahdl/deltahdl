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
