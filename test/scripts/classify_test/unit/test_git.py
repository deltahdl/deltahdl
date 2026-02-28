"""Unit tests for git integration functions in classify_test."""

import subprocess
from pathlib import Path
from unittest.mock import MagicMock

import pytest

from classify_test._git import build_commit_message, commit_and_push
from helpers import stub_subprocess_failure


# ---- build_commit_message --------------------------------------------------


def test_build_commit_message_title_has_test_name():
    """Title line contains the test name."""
    msg = build_commit_message("FooBar", "6.1", "rationale text")
    assert "Classify FooBar" in msg.splitlines()[0]


def test_build_commit_message_title_has_clause():
    """Title line contains the formatted clause with section sign."""
    msg = build_commit_message("T", "6.1", "r")
    assert "§6.1" in msg.splitlines()[0]


def test_build_commit_message_title_has_skip_ci():
    """Title line contains [skip ci]."""
    msg = build_commit_message("T", "6.1", "r")
    assert "[skip ci]" in msg.splitlines()[0]


def test_build_commit_message_title_has_arrow():
    """Title line uses arrow separator."""
    msg = build_commit_message("T", "6.1", "r")
    assert "→" in msg.splitlines()[0]


def test_build_commit_message_title_format():
    """Title line matches exact format."""
    msg = build_commit_message("MyTest", "9.2.1", "r")
    assert msg.splitlines()[0] == "Classify MyTest → §9.2.1 [skip ci]"


def test_build_commit_message_non_lrm_clause():
    """Non-LRM clause formats as 'Non-LRM TOPIC'."""
    msg = build_commit_message("T", "non-lrm:aig", "r")
    assert "Non-LRM AIG" in msg.splitlines()[0]


def test_build_commit_message_non_lrm_underscore():
    """Non-LRM clause with underscore converts to space."""
    msg = build_commit_message("T", "non-lrm:aig_opt", "r")
    assert "Non-LRM AIG OPT" in msg.splitlines()[0]


def test_build_commit_message_has_co_authored_by():
    """Message contains Co-Authored-By trailer."""
    msg = build_commit_message("T", "6.1", "r")
    assert "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>" in msg


def test_build_commit_message_rationale_in_body():
    """Rationale text appears in message body."""
    rationale = "This test exercises the UDP initial statement construct."
    msg = build_commit_message("T", "6.1", rationale)
    assert rationale in msg


def test_build_commit_message_exhaustive_rationale():
    """Full multi-sentence rationale is preserved, not truncated."""
    rationale = (
        "This test exercises the UDP initial statement construct "
        "defined in §29.7. The grammar production "
        "udp_initial_statement sets the starting value of a "
        "sequential UDP output register."
    )
    msg = build_commit_message("T", "29.7", rationale)
    assert rationale in msg


def test_build_commit_message_blank_line_after_title():
    """Blank line separates title from body."""
    msg = build_commit_message("T", "6.1", "rationale")
    lines = msg.splitlines()
    assert lines[1] == ""


def test_build_commit_message_blank_line_before_trailer():
    """Blank line separates body from Co-Authored-By trailer."""
    msg = build_commit_message("T", "6.1", "rationale")
    lines = msg.splitlines()
    trailer_idx = next(
        i for i, l in enumerate(lines) if "Co-Authored-By" in l
    )
    assert lines[trailer_idx - 1] == ""


def test_build_commit_message_annex_clause():
    """Annex clause formats with section sign."""
    msg = build_commit_message("T", "A.6.3", "r")
    assert "§A.6.3" in msg.splitlines()[0]


# ---- commit_and_push -------------------------------------------------------


def _mock_subprocess_success(monkeypatch):
    """Stub subprocess.run to always succeed; return captured commands."""
    captured = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""

    def capture_run(cmd, **_kwargs):
        captured.append(list(cmd))
        return mock_result

    monkeypatch.setattr(subprocess, "run", capture_run)
    return captured


def test_commit_and_push_calls_git_add(monkeypatch):
    """Calls git add for each changed file."""
    captured = _mock_subprocess_success(monkeypatch)
    commit_and_push(
        [Path("/a/b.cpp"), Path("/a/c.cpp")], [], "msg",
    )
    add_cmds = [c for c in captured if c[:2] == ["git", "add"]]
    assert len(add_cmds) == 2


def test_commit_and_push_adds_correct_files(monkeypatch):
    """git add receives the correct file paths."""
    captured = _mock_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    add_cmd = next(c for c in captured if c[:2] == ["git", "add"])
    assert add_cmd[2] == str(Path("/a/b.cpp"))


def test_commit_and_push_calls_git_rm(monkeypatch):
    """Calls git rm for each deleted file."""
    captured = _mock_subprocess_success(monkeypatch)
    commit_and_push([], [Path("/a/d.cpp")], "msg")
    rm_cmds = [c for c in captured if c[:2] == ["git", "rm"]]
    assert len(rm_cmds) == 1


def test_commit_and_push_rm_correct_file(monkeypatch):
    """git rm receives the correct file path."""
    captured = _mock_subprocess_success(monkeypatch)
    commit_and_push([], [Path("/a/d.cpp")], "msg")
    rm_cmd = next(c for c in captured if c[:2] == ["git", "rm"])
    assert rm_cmd[2] == str(Path("/a/d.cpp"))


def test_commit_and_push_calls_git_commit(monkeypatch):
    """Calls git commit."""
    captured = _mock_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    commit_cmds = [c for c in captured if c[:2] == ["git", "commit"]]
    assert len(commit_cmds) == 1


def test_commit_and_push_commit_uses_stdin(monkeypatch):
    """git commit uses -F - to read message from stdin."""
    captured = _mock_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    commit_cmd = next(c for c in captured if c[:2] == ["git", "commit"])
    assert "-F" in commit_cmd and "-" in commit_cmd


def test_commit_and_push_calls_git_push(monkeypatch):
    """Calls git push after committing."""
    captured = _mock_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    push_cmds = [c for c in captured if c[:2] == ["git", "push"]]
    assert len(push_cmds) == 1


def test_commit_and_push_order(monkeypatch):
    """Operations happen in order: add, rm, commit, push."""
    captured = _mock_subprocess_success(monkeypatch)
    commit_and_push(
        [Path("/a/b.cpp")], [Path("/a/d.cpp")], "msg",
    )
    ops = [c[1] for c in captured]
    assert ops == ["add", "rm", "commit", "push"]


def test_commit_and_push_noop_when_empty(monkeypatch):
    """No git commands when no files changed or deleted."""
    captured = _mock_subprocess_success(monkeypatch)
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

    def alternating(cmd, **_kw):
        call_count[0] += 1
        # First call (add) succeeds, second (commit) fails
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
    failure = MagicMock()
    failure.returncode = 1
    failure.stderr = "push error"

    def alternating(cmd, **_kw):
        call_count[0] += 1
        # add + commit succeed, push fails
        if call_count[0] <= 2:
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
