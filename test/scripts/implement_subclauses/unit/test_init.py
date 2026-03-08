"""Unit tests for implement_subclauses (arg parsing and dispatch)."""

import argparse
import runpy
import subprocess
import sys
from unittest.mock import MagicMock, patch

import pytest


# ---- parse_subclauses -------------------------------------------------------


def test_parse_subclauses_single(iscs):
    """Single subclause returns a one-element list."""
    assert iscs.parse_subclauses("6.1") == ["6.1"]


def test_parse_subclauses_multiple(iscs):
    """Comma-separated subclauses are split correctly."""
    assert iscs.parse_subclauses("6.1,6.1.1") == ["6.1", "6.1.1"]


def test_parse_subclauses_strips_whitespace(iscs):
    """Whitespace around subclauses is stripped."""
    assert iscs.parse_subclauses(" 6.1 , 6.2 ") == ["6.1", "6.2"]


def test_parse_subclauses_rejects_invalid(iscs):
    """Invalid subclause format raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        iscs.parse_subclauses("bad")


def test_parse_subclauses_rejects_one_invalid_in_list(iscs):
    """One invalid subclause in a list raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        iscs.parse_subclauses("6.1,bad,6.2")


# ---- parse_args --------------------------------------------------------------


def _base_argv(tmp_path):
    """Return minimal valid argv for parse_args."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--subclauses", "6.1,6.2",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "deltahdl", "--repo", "deltahdl",
    ]


def test_parse_args_subclauses_parsed(iscs, tmp_path):
    """--subclauses is parsed into a list."""
    args = iscs.parse_args(_base_argv(tmp_path))
    assert args.subclauses == ["6.1", "6.2"]


def test_parse_args_clause_issue_is_int(iscs, tmp_path):
    """--clause-issue is parsed as an integer."""
    args = iscs.parse_args(_base_argv(tmp_path))
    assert args.clause_issue == 8


def test_parse_args_master_issue_is_int(iscs, tmp_path):
    """--master-issue is parsed as an integer."""
    args = iscs.parse_args(_base_argv(tmp_path))
    assert args.master_issue == 1


def test_parse_args_organization(iscs, tmp_path):
    """--organization is parsed correctly."""
    args = iscs.parse_args(_base_argv(tmp_path))
    assert args.organization == "deltahdl"


def test_parse_args_repo(iscs, tmp_path):
    """--repo is parsed correctly."""
    args = iscs.parse_args(_base_argv(tmp_path))
    assert args.repo == "deltahdl"


def test_parse_args_model_default(iscs, tmp_path):
    """--model defaults to 'opus'."""
    args = iscs.parse_args(_base_argv(tmp_path))
    assert args.model == "opus"


def test_parse_args_model_override(iscs, tmp_path):
    """--model can be overridden."""
    argv = _base_argv(tmp_path) + ["--model", "sonnet"]
    args = iscs.parse_args(argv)
    assert args.model == "sonnet"


def test_parse_args_continue_default_false(iscs, tmp_path):
    """continue_session defaults to False."""
    args = iscs.parse_args(_base_argv(tmp_path))
    assert args.continue_session is False


def test_parse_args_continue_flag(iscs, tmp_path):
    """--continue sets continue_session to True."""
    argv = _base_argv(tmp_path) + ["--continue"]
    args = iscs.parse_args(argv)
    assert args.continue_session is True


def test_parse_args_rejects_missing_lrm(iscs, tmp_path):
    """Non-existent LRM file exits."""
    with pytest.raises(SystemExit):
        iscs.parse_args([
            "--lrm", str(tmp_path / "no.txt"), "--subclauses", "6.1",
            "--clause-issue", "8", "--master-issue", "1",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_rejects_bad_subclauses(iscs, tmp_path):
    """Invalid subclause format exits."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        iscs.parse_args([
            "--lrm", str(lrm), "--subclauses", "bad",
            "--clause-issue", "8", "--master-issue", "1",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_requires_subclauses(iscs, tmp_path):
    """--subclauses is required."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        iscs.parse_args([
            "--lrm", str(lrm),
            "--clause-issue", "8", "--master-issue", "1",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_requires_clause_issue(iscs, tmp_path):
    """--clause-issue is required."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        iscs.parse_args([
            "--lrm", str(lrm), "--subclauses", "6.1",
            "--master-issue", "1",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_requires_master_issue(iscs, tmp_path):
    """--master-issue is required."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        iscs.parse_args([
            "--lrm", str(lrm), "--subclauses", "6.1",
            "--clause-issue", "8",
            "--organization", "o", "--repo", "r",
        ])


# ---- invoke_implement_subclause ---------------------------------------------


def test_invoke_builds_correct_command(iscs, monkeypatch):
    """Correct command is passed to subprocess.run."""
    mock_run = MagicMock(
        return_value=subprocess.CompletedProcess(args=[], returncode=0),
    )
    monkeypatch.setattr(iscs.subprocess, "run", mock_run)
    iscs.invoke_implement_subclause(
        "/path/lrm.pdf", "6.1", 8, "opus", False,
    )
    assert mock_run.call_args[0][0] == [
        sys.executable, "-m", "implement_subclause",
        "--lrm", "/path/lrm.pdf",
        "--subclause", "6.1",
        "--issue", "8",
        "--model", "opus",
    ]


def test_invoke_passes_continue(iscs, monkeypatch):
    """--continue appears in command when continue_session=True."""
    mock_run = MagicMock(
        return_value=subprocess.CompletedProcess(args=[], returncode=0),
    )
    monkeypatch.setattr(iscs.subprocess, "run", mock_run)
    iscs.invoke_implement_subclause(
        "/path/lrm.pdf", "6.1", 8, "opus", True,
    )
    assert "--continue" in mock_run.call_args[0][0]


def test_invoke_no_continue_by_default(iscs, monkeypatch):
    """--continue not in command when continue_session=False."""
    mock_run = MagicMock(
        return_value=subprocess.CompletedProcess(args=[], returncode=0),
    )
    monkeypatch.setattr(iscs.subprocess, "run", mock_run)
    iscs.invoke_implement_subclause(
        "/path/lrm.pdf", "6.1", 8, "opus", False,
    )
    assert "--continue" not in mock_run.call_args[0][0]


def test_invoke_exits_on_failure(iscs, monkeypatch):
    """SystemExit on non-zero return code."""
    mock_run = MagicMock(
        return_value=subprocess.CompletedProcess(args=[], returncode=1),
    )
    monkeypatch.setattr(iscs.subprocess, "run", mock_run)
    with pytest.raises(SystemExit):
        iscs.invoke_implement_subclause(
            "/path/lrm.pdf", "6.1", 8, "opus", False,
        )


# ---- main -------------------------------------------------------------------


def _patch_main(monkeypatch, iscs, *, all_complete=False):
    """Patch dependencies for main() and return mocks."""
    mock_invoke = MagicMock()
    monkeypatch.setattr(iscs, "invoke_implement_subclause", mock_invoke)

    body = "- [x] 6.1\n- [x] 6.2\n" if all_complete else "- [ ] 6.3\n"
    monkeypatch.setattr(iscs, "fetch_issue_body", lambda *_a: body)
    monkeypatch.setattr(
        iscs, "next_unchecked",
        lambda _b: None if all_complete else "6.3",
    )

    mock_close = MagicMock()
    monkeypatch.setattr(iscs, "close_issue", mock_close)

    mock_mark = MagicMock()
    monkeypatch.setattr(iscs, "mark_master_complete", mock_mark)

    return mock_invoke, mock_close, mock_mark


def test_main_invokes_each_subclause(iscs, monkeypatch, tmp_path):
    """main() invokes implement_subclause for each subclause."""
    mock_invoke, _, __ = _patch_main(monkeypatch, iscs)
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    iscs.main([
        "--lrm", str(lrm), "--subclauses", "6.1,6.2",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ])
    assert mock_invoke.call_count == 2


def test_main_first_subclause_no_continue(iscs, monkeypatch, tmp_path):
    """First subclause does not pass continue_session=True."""
    mock_invoke, _, __ = _patch_main(monkeypatch, iscs)
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    iscs.main([
        "--lrm", str(lrm), "--subclauses", "6.1,6.2",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ])
    assert mock_invoke.call_args_list[0][0][4] is False


def test_main_second_subclause_uses_continue(iscs, monkeypatch, tmp_path):
    """Second subclause passes continue_session=True."""
    mock_invoke, _, __ = _patch_main(monkeypatch, iscs)
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    iscs.main([
        "--lrm", str(lrm), "--subclauses", "6.1,6.2",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ])
    assert mock_invoke.call_args_list[1][0][4] is True


def test_main_continue_flag_on_first(iscs, monkeypatch, tmp_path):
    """--continue flag makes the first subclause use continue_session=True."""
    mock_invoke, _, __ = _patch_main(monkeypatch, iscs)
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    iscs.main([
        "--lrm", str(lrm), "--subclauses", "6.1",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
        "--continue",
    ])
    assert mock_invoke.call_args_list[0][0][4] is True


def test_main_closes_issue_when_all_complete(iscs, monkeypatch, tmp_path):
    """Clause issue is closed when all subclauses are complete."""
    _, mock_close, __ = _patch_main(
        monkeypatch, iscs, all_complete=True,
    )
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    iscs.main([
        "--lrm", str(lrm), "--subclauses", "6.1",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ])
    assert mock_close.call_args == (
        ("o", "r", 8, "all subclauses are implemented"),
    )


def test_main_marks_master_when_all_complete(iscs, monkeypatch, tmp_path):
    """Master issue is marked complete when clause issue is done."""
    _, __, mock_mark = _patch_main(
        monkeypatch, iscs, all_complete=True,
    )
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    iscs.main([
        "--lrm", str(lrm), "--subclauses", "6.1",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ])
    assert mock_mark.call_args == (("o", "r", 1, 8),)


def test_main_does_not_close_when_incomplete(iscs, monkeypatch, tmp_path):
    """Clause issue is not closed when subclauses remain."""
    _, mock_close, __ = _patch_main(
        monkeypatch, iscs, all_complete=False,
    )
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    iscs.main([
        "--lrm", str(lrm), "--subclauses", "6.1",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ])
    assert not mock_close.called


def test_main_does_not_mark_master_when_incomplete(
    iscs, monkeypatch, tmp_path,
):
    """Master issue is not marked when subclauses remain."""
    _, __, mock_mark = _patch_main(
        monkeypatch, iscs, all_complete=False,
    )
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    iscs.main([
        "--lrm", str(lrm), "--subclauses", "6.1",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ])
    assert not mock_mark.called


# ---- __main__ guard ---------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("implement_subclauses", run_name="__main__")
