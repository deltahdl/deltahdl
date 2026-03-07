"""Unit tests for git integration functions in classify_test."""

import subprocess
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest


# ---- build_commit_message --------------------------------------------------


def test_build_commit_message_title_has_test_name(ct_git):
    """Title line contains the test name."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("FooBar", "6.1", "rationale text")
    assert "Classify FooBar" in msg.splitlines()[0]


def test_build_commit_message_title_has_clause(ct_git):
    """Title line contains the formatted clause with section sign."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "r")
    assert "§6.1" in msg.splitlines()[0]


def test_build_commit_message_title_has_skip_ci(ct_git):
    """Title line contains [skip ci]."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "r")
    assert "[skip ci]" in msg.splitlines()[0]


def test_build_commit_message_title_has_arrow(ct_git):
    """Title line uses arrow separator."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "r")
    assert "→" in msg.splitlines()[0]


def test_build_commit_message_title_format(ct_git):
    """Title line matches exact format."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("MyTest", "9.2.1", "r")
    assert msg.splitlines()[0] == "Classify MyTest → §9.2.1 [skip ci]"


def test_build_commit_message_non_lrm_clause(ct_git):
    """Non-LRM clause formats as 'Non-LRM TOPIC'."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "non-lrm:aig", "r")
    assert "Non-LRM AIG" in msg.splitlines()[0]


def test_build_commit_message_non_lrm_underscore(ct_git):
    """Non-LRM clause with underscore converts to space."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "non-lrm:aig_opt", "r")
    assert "Non-LRM AIG OPT" in msg.splitlines()[0]


def test_build_commit_message_has_co_authored_by(ct_git):
    """Message contains Co-Authored-By trailer."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "r")
    assert "Co-Authored-By: Claude Opus 4.6 <noreply@anthropic.com>" in msg


def test_build_commit_message_rationale_in_body(ct_git):
    """Rationale text appears in message body."""
    build_commit_message = ct_git.build_commit_message
    rationale = "This test exercises the UDP initial statement construct."
    msg = build_commit_message("T", "6.1", rationale)
    assert rationale in msg


def test_build_commit_message_exhaustive_rationale(ct_git):
    """Full multi-sentence rationale is preserved, not truncated."""
    build_commit_message = ct_git.build_commit_message
    rationale = (
        "This test exercises the UDP initial statement construct "
        "defined in §29.7. The grammar production "
        "udp_initial_statement sets the starting value of a "
        "sequential UDP output register."
    )
    msg = build_commit_message("T", "29.7", rationale)
    assert rationale in msg


def test_build_commit_message_blank_line_after_title(ct_git):
    """Blank line separates title from body."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "rationale")
    lines = msg.splitlines()
    assert lines[1] == ""


def test_build_commit_message_blank_line_before_trailer(ct_git):
    """Blank line separates body from Co-Authored-By trailer."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "6.1", "rationale")
    lines = msg.splitlines()
    trailer_idx = next(
        i for i, l in enumerate(lines) if "Co-Authored-By" in l
    )
    assert lines[trailer_idx - 1] == ""


def test_build_commit_message_annex_clause(ct_git):
    """Annex clause formats with section sign."""
    build_commit_message = ct_git.build_commit_message
    msg = build_commit_message("T", "A.6.3", "r")
    assert "§A.6.3" in msg.splitlines()[0]


# ---- commit_and_push -------------------------------------------------------


def test_commit_and_push_calls_git_add(monkeypatch, ct_git, ct_helpers):
    """Calls git add for each changed file."""
    commit_and_push = ct_git.commit_and_push
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push(
        [Path("/a/b.cpp"), Path("/a/c.cpp")], [], "msg",
    )
    add_cmds = [c for c in captured if c[:2] == ["git", "add"]]
    assert len(add_cmds) == 2


def test_commit_and_push_adds_correct_files(monkeypatch, ct_git, ct_helpers):
    """git add receives the correct file paths."""
    commit_and_push = ct_git.commit_and_push
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    add_cmd = next(c for c in captured if c[:2] == ["git", "add"])
    assert add_cmd[2] == str(Path("/a/b.cpp"))


def test_commit_and_push_calls_git_rm(monkeypatch, ct_git, ct_helpers):
    """Calls git rm for each deleted file."""
    commit_and_push = ct_git.commit_and_push
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push([], [Path("/a/d.cpp")], "msg")
    rm_cmds = [c for c in captured if c[:2] == ["git", "rm"]]
    assert len(rm_cmds) == 1


def test_commit_and_push_rm_correct_file(monkeypatch, ct_git, ct_helpers):
    """git rm receives the correct file path."""
    commit_and_push = ct_git.commit_and_push
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push([], [Path("/a/d.cpp")], "msg")
    rm_cmd = next(c for c in captured if c[:2] == ["git", "rm"])
    assert rm_cmd[2] == str(Path("/a/d.cpp"))


def test_commit_and_push_calls_git_commit(monkeypatch, ct_git, ct_helpers):
    """Calls git commit."""
    commit_and_push = ct_git.commit_and_push
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    commit_cmds = [c for c in captured if c[:2] == ["git", "commit"]]
    assert len(commit_cmds) == 1


def test_commit_and_push_commit_uses_stdin(monkeypatch, ct_git, ct_helpers):
    """git commit uses -F - to read message from stdin."""
    commit_and_push = ct_git.commit_and_push
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    commit_cmd = next(c for c in captured if c[:2] == ["git", "commit"])
    assert "-F" in commit_cmd and "-" in commit_cmd


def test_commit_and_push_calls_git_push(monkeypatch, ct_git, ct_helpers):
    """Calls git push after committing."""
    commit_and_push = ct_git.commit_and_push
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    push_cmds = [c for c in captured if c[:2] == ["git", "push"]]
    assert len(push_cmds) == 1


def test_commit_and_push_order(monkeypatch, ct_git, ct_helpers):
    """Operations happen in order: add, rm, commit, push."""
    commit_and_push = ct_git.commit_and_push
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push(
        [Path("/a/b.cpp")], [Path("/a/d.cpp")], "msg",
    )
    ops = [c[1] for c in captured]
    assert ops == ["add", "rm", "commit", "push"]


def test_commit_and_push_noop_when_empty(monkeypatch, ct_git, ct_helpers):
    """No git commands when no files changed or deleted."""
    commit_and_push = ct_git.commit_and_push
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push([], [], "msg")
    assert len(captured) == 0


def test_commit_and_push_exits_on_add_failure(monkeypatch, ct_git, ct_helpers):
    """Exits when git add fails."""
    commit_and_push = ct_git.commit_and_push
    ct_helpers.stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        commit_and_push([Path("/a/b.cpp")], [], "msg")


def test_commit_and_push_exits_on_commit_failure(monkeypatch, ct_git):
    """Exits when git commit fails."""
    commit_and_push = ct_git.commit_and_push
    call_count = [0]
    success = MagicMock()
    success.returncode = 0
    failure = MagicMock()
    failure.returncode = 1
    failure.stderr = "error"

    def alternating(_cmd, **_kw):
        call_count[0] += 1
        # First call (add) succeeds, second (commit) fails
        if call_count[0] <= 1:
            return success
        return failure

    monkeypatch.setattr(subprocess, "run", alternating)
    with pytest.raises(SystemExit):
        commit_and_push([Path("/a/b.cpp")], [], "msg")


def test_commit_and_push_exits_on_push_failure(monkeypatch, ct_git):
    """Exits when git push fails."""
    commit_and_push = ct_git.commit_and_push
    call_count = [0]
    success = MagicMock()
    success.returncode = 0
    failure = MagicMock()
    failure.returncode = 1
    failure.stderr = "push error"

    def alternating(_cmd, **_kw):
        call_count[0] += 1
        # add + commit succeed, push fails
        if call_count[0] <= 2:
            return success
        return failure

    monkeypatch.setattr(subprocess, "run", alternating)
    with pytest.raises(SystemExit):
        commit_and_push([Path("/a/b.cpp")], [], "msg")


def test_commit_and_push_message_passed_to_commit(monkeypatch, ct_git):
    """The commit message is passed via stdin to git commit."""
    commit_and_push = ct_git.commit_and_push
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


def test_commit_and_push_prints_committed(monkeypatch, capsys, ct_git, ct_helpers):
    """Prints 'Committed.' after git commit."""
    commit_and_push = ct_git.commit_and_push
    ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    assert "Committed." in capsys.readouterr().out


def test_commit_and_push_prints_pushed(monkeypatch, capsys, ct_git, ct_helpers):
    """Prints 'Pushed.' after git push."""
    commit_and_push = ct_git.commit_and_push
    ct_helpers.stub_subprocess_success(monkeypatch)
    commit_and_push([Path("/a/b.cpp")], [], "msg")
    assert "Pushed." in capsys.readouterr().out


# ---- commit_classification ---------------------------------------------------


def _stub_commit_push(monkeypatch, ct_git):
    """Stub commit_and_push to capture arguments."""
    captured = {}

    def fake(changed, deleted, message):
        captured["changed"] = list(changed)
        captured["deleted"] = list(deleted)
        captured["message"] = message

    monkeypatch.setattr(ct_git, "commit_and_push", fake)
    return captured


def _make_ctx(tmp_path, **overrides):
    """Build a commit_classification context dict."""
    defaults = {
        "filepath": tmp_path / "test_input.cpp",
        "target": [SimpleNamespace(
            test_name="T", clause="6.1", rationale="r",
        )],
        "new_names": [],
        "to_merge": [],
        "test_dir": tmp_path,
        "cmake_path": tmp_path / "CMakeLists.txt",
    }
    defaults.update(overrides)
    return defaults


def test_commit_classification_includes_new_files(monkeypatch, tmp_path, ct_git):
    """Changed files include newly created output files."""
    commit_classification = ct_git.commit_classification
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, new_names=["test_parser_clause_06_01"])
    commit_classification(ctx)
    assert tmp_path / "test_parser_clause_06_01.cpp" in captured["changed"]


def test_commit_classification_includes_merged(monkeypatch, tmp_path, ct_git):
    """Changed files include merge targets."""
    commit_classification = ct_git.commit_classification
    merge_path = tmp_path / "test_parser_clause_06_01.cpp"
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, to_merge=[(merge_path, None)])
    commit_classification(ctx)
    assert merge_path in captured["changed"]


def test_commit_classification_includes_cmake(monkeypatch, tmp_path, ct_git):
    """Changed files include CMakeLists.txt."""
    commit_classification = ct_git.commit_classification
    cmake = tmp_path / "CMakeLists.txt"
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, cmake_path=cmake)
    commit_classification(ctx)
    assert cmake in captured["changed"]


def test_commit_classification_existing_source_in_changed(
    monkeypatch, tmp_path, ct_git,
):
    """Source file that still exists goes into changed list."""
    commit_classification = ct_git.commit_classification
    src = tmp_path / "test_input.cpp"
    src.touch()
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, filepath=src)
    commit_classification(ctx)
    assert src in captured["changed"]


def test_commit_classification_deleted_source_in_deleted(
    monkeypatch, tmp_path, ct_git,
):
    """Source file that was removed goes into deleted list."""
    commit_classification = ct_git.commit_classification
    src = tmp_path / "test_input.cpp"
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, filepath=src)
    commit_classification(ctx)
    assert src in captured["deleted"]


def test_commit_classification_message_has_test_name(monkeypatch, tmp_path, ct_git):
    """Commit message includes the test name."""
    commit_classification = ct_git.commit_classification
    captured = _stub_commit_push(monkeypatch, ct_git)
    ctx = _make_ctx(tmp_path, target=[SimpleNamespace(
        test_name="FooBar", clause="6.1", rationale="r",
    )])
    commit_classification(ctx)
    assert "FooBar" in captured["message"]
