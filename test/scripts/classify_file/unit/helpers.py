"""Shared test helpers for classify_file unit tests."""

import json
import subprocess
from pathlib import Path
from unittest.mock import MagicMock

import classify_file


def make_test_file(tmp_path: Path, body: str) -> Path:
    """Write *body* to test_input.cpp and return its path."""
    f = tmp_path / "test_input.cpp"
    f.write_text(body, encoding="utf-8")
    return f


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


def stub_subprocess_mixed(monkeypatch, fail_names):
    """Stub subprocess.run to fail for specific test names."""
    captured: list[list[str]] = []

    def mixed_run(cmd, **_kwargs):
        captured.append(list(cmd))
        mock_result = MagicMock()
        mock_result.stdout = ""
        mock_result.stderr = ""
        test_idx = cmd.index("--test")
        name = cmd[test_idx + 1]
        mock_result.returncode = 1 if name in fail_names else 0
        return mock_result

    monkeypatch.setattr(subprocess, "run", mixed_run)
    return captured


def stub_close_issue(monkeypatch):
    """Stub classify_file.close_issue; return call log."""
    log: list = []
    monkeypatch.setattr(
        classify_file, "close_issue", log.append,
    )
    return log


def stub_create_issue(monkeypatch, issue_number=42):
    """Stub subprocess.run for create_issue; return captured calls."""
    captured: list[dict] = []

    def capture_run(cmd, **kwargs):
        captured.append(
            {"cmd": list(cmd), "input": kwargs.get("input", "")},
        )
        result = MagicMock()
        result.returncode = 0
        result.stdout = json.dumps({"number": issue_number})
        result.stderr = ""
        return result

    monkeypatch.setattr(subprocess, "run", capture_run)
    return captured


def stub_ensure_unchecked(monkeypatch):
    """Stub classify_file.ensure_unchecked; return call log."""
    log: list = []
    monkeypatch.setattr(
        classify_file, "ensure_unchecked",
        lambda _a, _n: log.append(True),
    )
    return log
