"""Unit tests for satisfy_subclause.mutators._close_satisfied_issue."""

from unittest.mock import patch

from satisfy_subclause.mutators import _close_satisfied_issue


def _patched_subprocess_run():
    """Patch subprocess.run inside satisfy_subclause.mutators."""
    return patch("satisfy_subclause.mutators.subprocess.run")


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
