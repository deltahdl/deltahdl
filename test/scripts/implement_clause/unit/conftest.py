"""Shared fixtures for implement_clause unit tests."""

import subprocess
from pathlib import Path
from unittest.mock import MagicMock

import pytest


@pytest.fixture()
def clause_argv(tmp_path: Path) -> list[str]:
    """Return argv for a --clause 4 invocation with a dummy LRM file."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
    ]


@pytest.fixture()
def invoke_subprocess_ok(ic, monkeypatch):
    """Patch subprocess.run to return success; return mock_run."""
    mock_run = MagicMock(
        return_value=subprocess.CompletedProcess(args=[], returncode=0),
    )
    monkeypatch.setattr(ic.subprocess, "run", mock_run)
    return mock_run


@pytest.fixture()
def commit_push_calls(monkeypatch):
    """Run commit_and_push and return captured subprocess calls.

    Returns a factory: call it with ``(ic, subclause)`` and get
    back the list of recorded ``cmd`` lists.
    """

    def _run(ic_mod, subclause: str = "4.1") -> list[list[str]]:
        calls: list[list[str]] = []

        def fake_run(cmd: list[str], **_kw):
            calls.append(cmd)
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                return subprocess.CompletedProcess(args=cmd, returncode=1)
            return subprocess.CompletedProcess(args=cmd, returncode=0)

        monkeypatch.setattr(ic_mod.subprocess, "run", fake_run)
        ic_mod.commit_and_push(subclause)
        return calls

    return _run
