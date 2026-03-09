"""Shared test helpers for classify_file unit tests."""

import json
import subprocess
from pathlib import Path
from unittest.mock import MagicMock

import pytest

import classify_file
from lib.python.test_fixtures.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
)

__all__ = [
    "make_test_file",
    "stub_close_issue",
    "stub_create_issue",
    "stub_sync_issue_rows",
    "stub_subprocess_failure",
    "stub_subprocess_success",
]


def make_test_file(tmp_path: Path, body: str) -> Path:
    """Write *body* to test_input.cpp and return its path."""
    f = tmp_path / "test_input.cpp"
    f.write_text(body, encoding="utf-8")
    return f


def stub_close_issue(
    monkeypatch: pytest.MonkeyPatch,
) -> list[tuple[str, str, int, str]]:
    """Stub classify_file.close_issue; return call log."""
    log: list[tuple[str, str, int, str]] = []
    monkeypatch.setattr(
        classify_file, "close_issue",
        lambda org, repo, issue, reason: log.append((org, repo, issue, reason)),
    )
    return log


def stub_create_issue(
    monkeypatch: pytest.MonkeyPatch, issue_number: int = 42,
) -> list[dict[str, str]]:
    """Stub subprocess.run for create_issue; return captured calls."""
    captured: list[dict[str, str]] = []

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


def stub_sync_issue_rows(monkeypatch: pytest.MonkeyPatch) -> list[bool]:
    """Stub classify_file.sync_issue_rows; return call log."""
    log: list[bool] = []

    def fake(_a: object, _n: object) -> set[str]:
        log.append(True)
        return set()

    monkeypatch.setattr(classify_file, "sync_issue_rows", fake)
    return log
