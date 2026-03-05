"""Shared test helpers for classify_files unit tests."""

import classify_files
from lib.python.test.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
)

__all__ = [
    "stub_fetch_issue_title",
    "stub_remove_file_checkbox",
    "stub_subprocess_failure",
    "stub_subprocess_success",
]


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
