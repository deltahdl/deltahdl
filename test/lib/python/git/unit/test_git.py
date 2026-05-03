"""Unit tests for lib.python.git."""

import subprocess
from pathlib import Path
from typing import Any
from unittest.mock import MagicMock

import pytest

from lib.python.git import (
    build_file_change_summary,
    commit_and_push,
    get_porcelain_changes,
    get_remote_repo,
    run_git,
)
from lib.python.test_fixtures.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
)


# ---- run_git ----------------------------------------------------------------


def test_run_git_returns_result(monkeypatch: pytest.MonkeyPatch) -> None:
    """Returns the CompletedProcess on success."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    assert run_git(["git", "status"]) is mock_result


def test_run_git_exits_on_failure(monkeypatch: pytest.MonkeyPatch) -> None:
    """Exits when the git command fails."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        run_git(["git", "status"])


def test_run_git_prints_error_on_failure(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    """Prints an error message when the git command fails."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "error"
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    monkeypatch.setattr("lib.python.git.sys.exit", lambda _: None)
    run_git(["git", "status"])
    assert "ERROR" in capsys.readouterr().err


def test_run_git_passes_kwargs(monkeypatch: pytest.MonkeyPatch) -> None:
    """Forwards keyword arguments to subprocess.run."""
    received: dict[str, Any] = {}
    mock_result = MagicMock()
    mock_result.returncode = 0

    def spy(_cmd: list[str], **kwargs: Any) -> MagicMock:
        received.update(kwargs)
        return mock_result

    monkeypatch.setattr(subprocess, "run", spy)
    run_git(["git", "commit", "-F", "-"], input="msg")
    assert received["input"] == "msg"


# ---- commit_and_push --------------------------------------------------------


def test_commit_and_push_calls_git_add(monkeypatch: pytest.MonkeyPatch) -> None:
    """Calls git add for each changed file."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push(
        [str(Path("/a/b.cpp")), str(Path("/a/c.cpp"))], [], "msg",
    )
    add_cmds = [c for c in captured if c[:2] == ["git", "add"]]
    assert len(add_cmds) == 2


def test_commit_and_push_adds_correct_files(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """git add receives the correct file paths."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    add_cmd = next(c for c in captured if c[:2] == ["git", "add"])
    assert add_cmd[2] == str(Path("/a/b.cpp"))


def test_commit_and_push_calls_git_rm(monkeypatch: pytest.MonkeyPatch) -> None:
    """Calls git rm for each deleted file."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([], [str(Path("/a/d.cpp"))], "msg")
    rm_cmds = [c for c in captured if c[:2] == ["git", "rm"]]
    assert len(rm_cmds) == 1


def test_commit_and_push_rm_correct_file(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """git rm receives the correct file path."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([], [str(Path("/a/d.cpp"))], "msg")
    rm_cmd = next(c for c in captured if c[:2] == ["git", "rm"])
    assert rm_cmd[2] == str(Path("/a/d.cpp"))


def test_commit_and_push_calls_git_commit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Calls git commit."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    commit_cmds = [c for c in captured if c[:2] == ["git", "commit"]]
    assert len(commit_cmds) == 1


def test_commit_and_push_commit_uses_stdin(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """git commit uses -F - to read message from stdin."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    commit_cmd = next(c for c in captured if c[:2] == ["git", "commit"])
    assert "-F" in commit_cmd and "-" in commit_cmd


def test_commit_and_push_calls_git_push(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Calls git push after committing."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    push_cmds = [c for c in captured if c[:2] == ["git", "push"]]
    assert len(push_cmds) == 1


def test_commit_and_push_order(monkeypatch: pytest.MonkeyPatch) -> None:
    """Operations happen in order: add, rm, commit, rev-parse, push."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push(
        [str(Path("/a/b.cpp"))], [str(Path("/a/d.cpp"))], "msg",
    )
    ops = [c[1] for c in captured]
    assert ops == ["add", "rm", "commit", "rev-parse", "push"]


def test_commit_and_push_noop_when_empty(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """No git commands when no files changed or deleted."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([], [], "msg")
    assert len(captured) == 0


def test_commit_and_push_exits_on_add_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Exits when git add fails."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        commit_and_push([str(Path("/a/b.cpp"))], [], "msg")


def test_commit_and_push_exits_on_commit_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Exits when git commit fails."""
    call_count = [0]
    success = MagicMock()
    success.returncode = 0
    failure = MagicMock()
    failure.returncode = 1
    failure.stderr = "error"

    def alternating(_cmd: list[str], **_kw: Any) -> MagicMock:
        call_count[0] += 1
        if call_count[0] <= 1:
            return success
        return failure

    monkeypatch.setattr(subprocess, "run", alternating)
    with pytest.raises(SystemExit):
        commit_and_push([str(Path("/a/b.cpp"))], [], "msg")


def test_commit_and_push_exits_on_push_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Exits when git push fails."""
    call_count = [0]
    success = MagicMock()
    success.returncode = 0
    success.stdout = "fakeSHA\n"
    failure = MagicMock()
    failure.returncode = 1
    failure.stderr = "push error"

    def alternating(_cmd: list[str], **_kw: Any) -> MagicMock:
        call_count[0] += 1
        if call_count[0] <= 3:  # add, commit, rev-parse succeed
            return success
        return failure

    monkeypatch.setattr(subprocess, "run", alternating)
    with pytest.raises(SystemExit):
        commit_and_push([str(Path("/a/b.cpp"))], [], "msg")


def test_commit_and_push_message_passed_to_commit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The commit message is passed via stdin to git commit."""
    inputs: list[str] = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""

    def capture_run(cmd: list[str], **kwargs: Any) -> MagicMock:
        if cmd[:2] == ["git", "commit"]:
            inputs.append(kwargs.get("input", ""))
        return mock_result

    monkeypatch.setattr(subprocess, "run", capture_run)
    commit_and_push([str(Path("/a/b.cpp"))], [], "my commit msg")
    assert inputs[0] == "my commit msg"


def test_commit_and_push_prints_committed(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    """Prints 'Committed.' after git commit."""
    stub_subprocess_success(monkeypatch)
    commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    assert "Committed." in capsys.readouterr().out


def test_commit_and_push_prints_pushed(
    monkeypatch: pytest.MonkeyPatch,
    capsys: pytest.CaptureFixture[str],
) -> None:
    """Prints 'Pushed.' after git push."""
    stub_subprocess_success(monkeypatch)
    commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    assert "Pushed." in capsys.readouterr().out


def test_commit_and_push_returns_sha(monkeypatch: pytest.MonkeyPatch) -> None:
    """Returns the commit SHA after a successful commit."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""
    sha_result = MagicMock()
    sha_result.returncode = 0
    sha_result.stdout = "abc1234def5678\n"
    sha_result.stderr = ""

    def dispatch(cmd: list[str], **_kw: Any) -> MagicMock:
        if cmd[:2] == ["git", "rev-parse"]:
            return sha_result
        return mock_result

    monkeypatch.setattr(subprocess, "run", dispatch)
    result = commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    assert result == "abc1234def5678"


def test_commit_and_push_noop_returns_none(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Returns None when there are no files to commit."""
    stub_subprocess_success(monkeypatch)
    result = commit_and_push([], [], "msg")
    assert result is None


def test_commit_and_push_calls_rev_parse(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Calls git rev-parse exactly once."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    rev_parse_cmds = [c for c in captured if c[:2] == ["git", "rev-parse"]]
    assert len(rev_parse_cmds) == 1


def test_commit_and_push_rev_parse_uses_head(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """git rev-parse is called with HEAD."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    rev_parse_cmd = next(c for c in captured if c[:2] == ["git", "rev-parse"])
    assert rev_parse_cmd == ["git", "rev-parse", "HEAD"]


def test_commit_and_push_rev_parse_after_commit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """git rev-parse HEAD is called after git commit."""
    captured = stub_subprocess_success(monkeypatch)
    commit_and_push([str(Path("/a/b.cpp"))], [], "msg")
    ops = [c[1] for c in captured]
    assert ops.index("rev-parse") > ops.index("commit")


# ---- get_remote_repo -------------------------------------------------------


def test_get_remote_repo_ssh(monkeypatch: pytest.MonkeyPatch) -> None:
    """Parses org/repo from an SSH remote URL."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "git@github.com:deltahdl/deltahdl.git\n"
    mock_result.stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    assert get_remote_repo() == ("deltahdl", "deltahdl")


def test_get_remote_repo_https(monkeypatch: pytest.MonkeyPatch) -> None:
    """Parses org/repo from an HTTPS remote URL."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "https://github.com/myorg/myrepo.git\n"
    mock_result.stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    assert get_remote_repo() == ("myorg", "myrepo")


def test_get_remote_repo_https_no_dotgit(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Parses org/repo from an HTTPS URL without .git suffix."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "https://github.com/myorg/myrepo\n"
    mock_result.stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    assert get_remote_repo() == ("myorg", "myrepo")


def test_get_remote_repo_exits_on_unparseable_url(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Exits when the remote URL cannot be parsed."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "file:///local/repo\n"
    mock_result.stderr = ""
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    with pytest.raises(SystemExit):
        get_remote_repo()


# ---- get_porcelain_changes -------------------------------------------------


def _porcelain_result(
    monkeypatch: pytest.MonkeyPatch, stdout: str,
) -> None:
    """Stub subprocess.run to return the given porcelain stdout."""
    mock_result = MagicMock(returncode=0, stdout=stdout, stderr="")
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)


def test_get_porcelain_changes_untracked_in_added(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Untracked files appear in the added list."""
    _porcelain_result(monkeypatch, "?? src/new.cpp\n")
    added, _, _ = get_porcelain_changes()
    assert added == ["src/new.cpp"]


def test_get_porcelain_changes_modified_in_modified(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Modified files appear in the modified list."""
    _porcelain_result(monkeypatch, " M src/foo.cpp\n")
    _, modified, _ = get_porcelain_changes()
    assert modified == ["src/foo.cpp"]


def test_get_porcelain_changes_deleted_in_deleted(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Deleted files appear in the deleted list."""
    _porcelain_result(monkeypatch, " D src/old.cpp\n")
    _, _, deleted = get_porcelain_changes()
    assert deleted == ["src/old.cpp"]


def test_get_porcelain_changes_empty(monkeypatch: pytest.MonkeyPatch) -> None:
    """Empty status returns three empty lists."""
    _porcelain_result(monkeypatch, "")
    assert get_porcelain_changes() == ([], [], [])


def test_get_porcelain_changes_skips_blank_lines(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Blank lines in status output are skipped."""
    _porcelain_result(monkeypatch, " M a.cpp\n\n M b.cpp\n")
    _, modified, _ = get_porcelain_changes()
    assert len(modified) == 2


# ---- build_file_change_summary --------------------------------------------


def test_build_file_change_summary_added_only() -> None:
    """Summary for added files only."""
    assert build_file_change_summary(["src/foo.cpp"], [], []) == "Added foo.cpp"


def test_build_file_change_summary_all_three() -> None:
    """Summary with added, modified, and deleted."""
    result = build_file_change_summary(["a.cpp"], ["b.cpp"], ["c.cpp"])
    assert result == "Added a.cpp; modified b.cpp; deleted c.cpp"


def test_build_file_change_summary_empty() -> None:
    """Empty lists return empty string."""
    assert build_file_change_summary([], [], []) == ""


def test_build_file_change_summary_uses_basenames() -> None:
    """Summary uses basenames, not full paths."""
    result = build_file_change_summary(["test/src/unit/foo.cpp"], [], [])
    assert result == "Added foo.cpp"


def test_build_file_change_summary_sorts() -> None:
    """Files are sorted alphabetically within each category."""
    result = build_file_change_summary(["z.cpp", "a.cpp"], [], [])
    assert result == "Added a.cpp, z.cpp"
