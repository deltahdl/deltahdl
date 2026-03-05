"""Shared test helpers for classify_files unit tests."""

import subprocess
from unittest.mock import MagicMock

import classify_files


def stub_subprocess_success(monkeypatch):
    """Stub subprocess.run to succeed; return captured command lists."""
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
    """Stub subprocess.run to return exit code 1."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "fake error"

    def fail_run(_cmd, **_kwargs):
        return mock_result

    monkeypatch.setattr(subprocess, "run", fail_run)


def stub_remove_file_checkbox(monkeypatch):
    """Stub remove_file_checkbox; return list of filenames removed."""
    removed: list[str] = []

    def fake_remove(_org, _repo, _issue, filename):
        removed.append(filename)

    monkeypatch.setattr(
        classify_files, "remove_file_checkbox", fake_remove,
    )
    return removed


def stub_fetch_issue_title(
    monkeypatch,
    titles: dict[int, str],
):
    """Stub fetch_issue_title; return title from *titles* dict."""
    monkeypatch.setattr(
        classify_files, "fetch_issue_title",
        lambda _o, _r, issue: titles[issue],
    )
