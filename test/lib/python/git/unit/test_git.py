"""Unit tests for lib.python.git."""

import subprocess
from pathlib import Path
from unittest.mock import MagicMock

import pytest

from lib.python.git import commit_and_push, get_remote_repo, run_git
from lib.python.test_fixtures.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
)


# ---- run_git ----------------------------------------------------------------


def test_run_git_returns_result(monkeypatch):
    """Returns the CompletedProcess on success."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    assert run_git(["git", "status"]) is mock_result


def test_run_git_exits_on_failure(monkeypatch):
    """Exits when the git command fails."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        run_git(["git", "status"])


def test_run_git_prints_error_on_failure(monkeypatch, capsys):
    """Prints an error message when the git command fails."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "error"
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    monkeypatch.setattr("lib.python.git.sys.exit", lambda _: None)
    run_git(["git", "status"])
    assert "ERROR" in capsys.readouterr().err


def test_run_git_passes_kwargs(monkeypatch):
    """Forwards keyword arguments to subprocess.run."""
    received = {}
    mock_result = MagicMock()
    mock_result.returncode = 0

    def spy(_cmd, **kwargs):
        received.update(kwargs)
        return mock_result

    monkeypatch.setattr(subprocess, "run", spy)
    run_git(["git", "commit", "-F", "-"], input="msg")
    assert received["input"] == "msg"


# ---- commit_and_push --------------------------------------------------------


def test_commit_and_push_calls_git_add(monkeypatch):
    """Calls git add for each changed file."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push(
        [Path("/a/b.cpp"), Path("/a/c.cpp")], [], "msg",
    )
    add_cmds = [c for c in captured if c[:2] == ["git", "add"]]
    assert len(add_cmds) == 2


def test_commit_and_push_adds_correct_files(monkeypatch):
    """git add receives the correct file paths."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    add_cmd = next(c for c in captured if c[:2] == ["git", "add"])
    assert add_cmd[2] == str(Path("/a/b.cpp"))


def test_commit_and_push_calls_git_rm(monkeypatch):
    """Calls git rm for each deleted file."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([], [Path("/a/d.cpp")], "msg")
    rm_cmds = [c for c in captured if c[:2] == ["git", "rm"]]
    assert len(rm_cmds) == 1


def test_commit_and_push_rm_correct_file(monkeypatch):
    """git rm receives the correct file path."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([], [Path("/a/d.cpp")], "msg")
    rm_cmd = next(c for c in captured if c[:2] == ["git", "rm"])
    assert rm_cmd[2] == str(Path("/a/d.cpp"))


def test_commit_and_push_calls_git_commit(monkeypatch):
    """Calls git commit."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    commit_cmds = [c for c in captured if c[:2] == ["git", "commit"]]
    assert len(commit_cmds) == 1


def test_commit_and_push_commit_uses_stdin(monkeypatch):
    """git commit uses -F - to read message from stdin."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    commit_cmd = next(c for c in captured if c[:2] == ["git", "commit"])
    assert "-F" in commit_cmd and "-" in commit_cmd


def test_commit_and_push_calls_git_push(monkeypatch):
    """Calls git push after committing."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    push_cmds = [c for c in captured if c[:2] == ["git", "push"]]
    assert len(push_cmds) == 1


def test_commit_and_push_order(monkeypatch):
    """Operations happen in order: add, rm, commit, rev-parse, push."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push(
        [Path("/a/b.cpp")], [Path("/a/d.cpp")], "msg",
    )
    ops = [c[1] for c in captured]
    assert ops == ["add", "rm", "commit", "rev-parse", "push"]


def test_commit_and_push_noop_when_empty(monkeypatch):
    """No git commands when no files changed or deleted."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([], [], "msg")
    assert len(captured) == 0


def test_commit_and_push_exits_on_add_failure(monkeypatch):
    """Exits when git add fails."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        commit_and_push([Path("/a/b.cpp")], [], "msg")


def test_commit_and_push_exits_on_commit_failure(monkeypatch):
    """Exits when git commit fails."""
    call_count = [0]
    success = MagicMock()
    success.returncode = 0
    failure = MagicMock()
    failure.returncode = 1
    failure.stderr = "error"

    def alternating(_cmd, **_kw):
        call_count[0] += 1
        if call_count[0] <= 1:
            return success
        return failure

    monkeypatch.setattr(subprocess, "run", alternating)
    with pytest.raises(SystemExit):
        commit_and_push([Path("/a/b.cpp")], [], "msg")


def test_commit_and_push_exits_on_push_failure(monkeypatch):
    """Exits when git push fails."""
    call_count = [0]
    success = MagicMock()
    success.returncode = 0
    success.stdout = "fakeSHA\n"
    failure = MagicMock()
    failure.returncode = 1
    failure.stderr = "push error"

    def alternating(_cmd, **_kw):
        call_count[0] += 1
        if call_count[0] <= 3:  # add, commit, rev-parse succeed
            return success
        return failure

    monkeypatch.setattr(subprocess, "run", alternating)
    with pytest.raises(SystemExit):
        commit_and_push([Path("/a/b.cpp")], [], "msg")


def test_commit_and_push_message_passed_to_commit(monkeypatch):
    """The commit message is passed via stdin to git commit."""
    inputs = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""

    def capture_run(cmd, **kwargs):
        if cmd[:2] == ["git", "commit"]:
            inputs.append(kwargs.get("input", ""))
        return mock_result

    monkeypatch.setattr(subprocess, "run", capture_run)
    commit_and_push([Path("/a/b.cpp")], [], "my commit msg")
    assert inputs[0] == "my commit msg"


def test_commit_and_push_prints_committed(monkeypatch, capsys):
    """Prints 'Committed.' after git commit."""
    stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    assert "Committed." in capsys.readouterr().out


def test_commit_and_push_prints_pushed(monkeypatch, capsys):
    """Prints 'Pushed.' after git push."""
    stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    assert "Pushed." in capsys.readouterr().out


def test_commit_and_push_returns_sha(monkeypatch):
    """Returns the commit SHA after a successful commit."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""
    sha_result = MagicMock()
    sha_result.returncode = 0
    sha_result.stdout = "abc1234def5678\n"
    sha_result.stderr = ""

    def dispatch(cmd, **_kw):
        if cmd[:2] == ["git", "rev-parse"]:
            return sha_result
        return mock_result

    monkeypatch.setattr(subprocess, "run", dispatch)
    result = commit_and_push([Path("/a/b.cpp")], [], "msg")
    assert result == "abc1234def5678"


def test_commit_and_push_noop_returns_none(monkeypatch):
    """Returns None when there are no files to commit."""
    stub_subprocess_success(monkeypatch)
    result = commit_and_push([], [], "msg")
    assert result is None


def test_commit_and_push_calls_rev_parse(monkeypatch):
    """Calls git rev-parse exactly once."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    rev_parse_cmds = [c for c in captured if c[:2] == ["git", "rev-parse"]]
    assert len(rev_parse_cmds) == 1


def test_commit_and_push_rev_parse_uses_head(monkeypatch):
    """git rev-parse is called with HEAD."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    rev_parse_cmd = next(c for c in captured if c[:2] == ["git", "rev-parse"])
    assert rev_parse_cmd == ["git", "rev-parse", "HEAD"]


def test_commit_and_push_rev_parse_after_commit(monkeypatch):
    """git rev-parse HEAD is called after git commit."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    ops = [c[1] for c in captured]
    assert ops.index("rev-parse") > ops.index("commit")


# ---- get_remote_repo -------------------------------------------------------


def test_get_remote_repo_ssh(monkeypatch):
    """Parses org/repo from an SSH remote URL."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "git@github.com:deltahdl/deltahdl.git\n"
    mock_result.stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    assert get_remote_repo() == ("deltahdl", "deltahdl")


def test_get_remote_repo_https(monkeypatch):
    """Parses org/repo from an HTTPS remote URL."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "https://github.com/myorg/myrepo.git\n"
    mock_result.stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    assert get_remote_repo() == ("myorg", "myrepo")


def test_get_remote_repo_https_no_dotgit(monkeypatch):
    """Parses org/repo from an HTTPS URL without .git suffix."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "https://github.com/myorg/myrepo\n"
    mock_result.stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    assert get_remote_repo() == ("myorg", "myrepo")
