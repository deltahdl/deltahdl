"""Unit tests for satisfy_subclause.mutators._close_satisfied_issue."""

import subprocess
from typing import Any
from unittest.mock import patch

import pytest

from satisfy_subclause.mutators import _close_satisfied_issue


def _completed(
    returncode: int = 0, stderr: str = "",
) -> subprocess.CompletedProcess[str]:
    """Build the CompletedProcess a stubbed ``gh issue close`` returns."""
    return subprocess.CompletedProcess(
        args=["gh"], returncode=returncode, stdout="", stderr=stderr,
    )


def _patched_subprocess_run(
    returncode: int = 0, stderr: str = "",
) -> Any:
    """Patch subprocess.run inside satisfy_subclause.mutators.

    The stub returns a real CompletedProcess rather than a bare mock so
    the exit status is a number the caller can act on. A mock attribute
    compares unequal to zero, which would make every close look failed.
    """
    return patch(
        "satisfy_subclause.mutators.subprocess.run",
        return_value=_completed(returncode, stderr),
    )


def test_close_satisfied_issue_invokes_gh() -> None:
    """_close_satisfied_issue runs ``gh issue close`` for the given issue."""
    with _patched_subprocess_run() as run:
        _close_satisfied_issue("6.3", 42)
    assert run.call_args[0][0][:4] == ["gh", "issue", "close", "42"]


def test_close_satisfied_issue_attaches_comment() -> None:
    """The close call attaches an explanatory comment naming the subclause."""
    with _patched_subprocess_run() as run:
        _close_satisfied_issue("6.3", 42)
    cmd = run.call_args[0][0]
    assert "§6.3" in cmd[cmd.index("--comment") + 1]


def test_close_satisfied_issue_uses_annex_label() -> None:
    """Annex subclauses appear with their letter prefix in the close comment."""
    with _patched_subprocess_run() as run:
        _close_satisfied_issue("A.7.1", 99)
    cmd = run.call_args[0][0]
    assert "A.7.1" in cmd[cmd.index("--comment") + 1]


def test_close_satisfied_issue_raises_when_gh_fails() -> None:
    """A non-zero exit from ``gh issue close`` stops the run.

    The close is the only record that a subclause needing no edits was
    satisfied, so a failure that is stepped over leaves the issue open
    and the next pass pays a full mutator run to rediscover nothing.
    """
    with _patched_subprocess_run(returncode=1), pytest.raises(RuntimeError):
        _close_satisfied_issue("6.3", 42)


def test_close_satisfied_issue_error_names_issue_and_stderr() -> None:
    """The raised error identifies the issue and repeats what gh reported."""
    failed = _patched_subprocess_run(returncode=1, stderr="gh: not found")
    with failed, pytest.raises(RuntimeError, match=r"42.*gh: not found"):
        _close_satisfied_issue("6.3", 42)
