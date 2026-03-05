"""Shared fixtures for implement_clause unit tests."""

import subprocess
from pathlib import Path
from types import ModuleType
from unittest.mock import patch

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def ic(module_loader):
    """Load the implement_clause module."""
    return module_loader(
        "implement_clause",
        SCRIPTS_DIR / "implement_clause" / "__init__.py",
    )


@pytest.fixture()
def clause_argv(tmp_path: Path) -> list[str]:
    """Return argv for a --clause 4 invocation with a dummy LRM file."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1", "--organization", "o", "--repo", "r",
    ]


@pytest.fixture()
def invoke_subprocess_ok():
    """Patch subprocess.run to return success; yield mock_run."""
    with patch("implement_clause.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=[], returncode=0,
        )
        yield mock_run


@pytest.fixture()
def commit_push_calls():
    """Run commit_and_push and return captured subprocess calls.

    Returns a factory: call it with ``(ic, subclause)`` and get
    back the list of recorded ``cmd`` lists.
    """

    def _run(ic_mod: ModuleType, subclause: str = "4.1") -> list[list[str]]:
        calls: list[list[str]] = []

        def fake_run(cmd: list[str], **_kw: object) -> subprocess.CompletedProcess[str]:
            calls.append(cmd)
            if cmd == ["git", "diff", "--cached", "--quiet"]:
                return subprocess.CompletedProcess(args=cmd, returncode=1)
            return subprocess.CompletedProcess(args=cmd, returncode=0)

        with patch("implement_clause.subprocess.run", side_effect=fake_run):
            ic_mod.commit_and_push(subclause)
        return calls

    return _run


@pytest.fixture()
def patch_filter_ok():
    """Patch subprocess to return ["4.2", "4.3"] for filter calls."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": false, "4.2": true, "4.3": true}\n',
        stderr="",
    )
    with patch("implement_clause.subprocess.run", return_value=cp):
        yield
