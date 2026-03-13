"""Tests for implement_clause core functions."""

import argparse
import subprocess
import sys
from pathlib import Path
from unittest.mock import MagicMock

import pytest

_STUB_ARGS = argparse.Namespace(
    lrm="/path/lrm.pdf", sub_issue=123, master_issue=99,
    organization="deltahdl", repo="deltahdl",
)


def _patch_main_no_subclauses(monkeypatch, ic):
    """Patch dependencies for the no-subclauses main() path."""
    monkeypatch.setattr(ic, "discover_subclauses", lambda *_a: {})
    monkeypatch.setattr(ic, "invoke_implement_subclause", MagicMock())
    monkeypatch.setattr(ic, "close_issue", MagicMock())
    monkeypatch.setattr(ic, "mark_master_complete", MagicMock())


def _patch_main_with_subclauses(
    monkeypatch, ic, *, subclauses=None,
    synced_body="body", next_sub="4.2",
):
    """Patch all dependencies for main() with subclauses.

    *next_sub* can be a string (single call then None) or a list
    (successive return values via ``side_effect``).
    """
    if subclauses is None:
        subclauses = {"4.1": "General", "4.2": "Exec"}

    if isinstance(next_sub, list):
        next_kw = {"side_effect": next_sub}
    else:
        next_kw = {"side_effect": [next_sub, None]}

    monkeypatch.setattr(ic, "discover_subclauses", lambda *_a: subclauses)
    monkeypatch.setattr(ic, "fetch_issue_body", lambda *_a: "")
    monkeypatch.setattr(ic, "build_synced_body", lambda *_a: synced_body)
    monkeypatch.setattr(ic, "update_issue_body", lambda *_a, **_kw: None)

    mock_next = MagicMock(**next_kw)
    monkeypatch.setattr(ic, "next_unchecked", mock_next)

    mock_inv = MagicMock()
    monkeypatch.setattr(ic, "invoke_implement_subclause", mock_inv)

    mock_cap = MagicMock()
    monkeypatch.setattr(ic, "commit_and_push", mock_cap)

    mock_close = MagicMock()
    monkeypatch.setattr(ic, "close_issue", mock_close)

    mock_mark = MagicMock()
    monkeypatch.setattr(ic, "mark_master_complete", mock_mark)

    return mock_inv, mock_cap, mock_close, mock_mark


def test_invoke_implement_subclause_calls_subprocess(
    ic, invoke_subprocess_ok,
) -> None:
    """Correct command is passed to subprocess.run."""
    ic.invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert invoke_subprocess_ok.call_args[0][0] == [
        sys.executable, "-m", "implement_subclause",
        "--lrm", "/path/lrm.pdf",
        "--subclause", "4.2",
        "--issue", "123",
        "--model", "opus",
    ]


@pytest.mark.usefixtures("invoke_subprocess_ok")
def test_invoke_implement_subclause_prints_subclause(ic, capsys) -> None:
    """Prints which subclause is being invoked."""
    ic.invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert "4.2" in capsys.readouterr().out


# --- parse_args ---


def test_parse_args_clause(ic, tmp_path) -> None:
    """--clause flag sets args.clause to the number."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
    ])
    assert args.clause == "4"


def test_parse_args_annex(ic, tmp_path) -> None:
    """--annex flag sets args.annex to the letter."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--annex", "A",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
    ])
    assert args.annex == "A"


def test_parse_args_clause_and_annex_exclusive(ic, tmp_path) -> None:
    """--clause and --annex are mutually exclusive."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm), "--clause", "4", "--annex", "A",
            "--sub-issue", "1", "--master-issue", "99",
            "--organization", "o", "--repo", "r",
        ])


def test_parse_args_missing_lrm(ic) -> None:
    """SystemExit when --lrm points to a nonexistent file."""
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", "/no/such/file", "--clause", "4",
            "--sub-issue", "1", "--master-issue", "99",
            "--organization", "o", "--repo", "r",
        ])


def _parse_issue_args(ic, tmp_path):
    """Parse args with --sub-issue 42 --master-issue 1."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "42", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ])


def test_parse_args_sub_issue_is_int(ic, tmp_path) -> None:
    """--sub-issue is parsed as an integer."""
    assert _parse_issue_args(ic, tmp_path).sub_issue == 42


def test_parse_args_master_issue_is_int(ic, tmp_path) -> None:
    """--master-issue is parsed as an integer."""
    assert _parse_issue_args(ic, tmp_path).master_issue == 1


def test_parse_args_no_clause_or_annex(ic, tmp_path) -> None:
    """SystemExit when neither --clause nor --annex is provided."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm),
            "--sub-issue", "1", "--master-issue", "99",
            "--organization", "o", "--repo", "r",
        ])


@pytest.mark.parametrize("flag,value", [
    ("--figures", "4_1=fig.gv"),
    ("--tables", "4_1=tbl.md"),
])
def test_parse_args_rejects_removed_flag(ic, tmp_path, flag, value) -> None:
    """Removed flags (--figures, --tables) are no longer accepted."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm), "--clause", "4",
            "--sub-issue", "1", "--master-issue", "99",
            "--organization", "o", "--repo", "r",
            flag, value,
        ])


# --- main ---


def test_main_no_subclauses_exits(ic, monkeypatch, clause_argv) -> None:
    """Empty discovery causes SystemExit(1)."""
    _patch_main_no_subclauses(monkeypatch, ic)
    with pytest.raises(SystemExit):
        ic.main(clause_argv)


def test_main_no_subclauses_error_message(
    ic, monkeypatch, clause_argv, capsys,
) -> None:
    """Empty discovery prints an error to stderr."""
    _patch_main_no_subclauses(monkeypatch, ic)
    with pytest.raises(SystemExit):
        ic.main(clause_argv)
    assert "no implementable subclauses" in capsys.readouterr().err.lower()


def test_main_with_subclauses(ic, monkeypatch, clause_argv) -> None:
    """Next unchecked subclause is passed to implement_subclause."""
    mock_inv, _, __, ___ = _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert mock_inv.call_args[0][1] == "4.2"


def test_main_prints_subclauses_found(
    ic, monkeypatch, clause_argv, capsys,
) -> None:
    """Prints how many subclauses were discovered."""
    _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert "Found 2 subclauses" in capsys.readouterr().out


def test_main_prints_synced_body(
    ic, monkeypatch, clause_argv, capsys,
) -> None:
    """Prints the synced issue body."""
    _patch_main_with_subclauses(
        monkeypatch, ic,
        synced_body="## Subclauses\n\n- [ ] 4.1 General\n",
        next_sub="4.1",
    )
    ic.main(clause_argv)
    assert "## Subclauses" in capsys.readouterr().out


def test_main_prints_next_subclause(
    ic, monkeypatch, clause_argv, capsys,
) -> None:
    """Prints which subclause was picked as next."""
    _patch_main_with_subclauses(monkeypatch, ic)
    ic.main(clause_argv)
    assert "Next unchecked: 4.2" in capsys.readouterr().out


def test_main_all_done(ic, monkeypatch, clause_argv, capsys) -> None:
    """Prints all-done message when no unchecked subclauses remain."""
    _patch_main_with_subclauses(
        monkeypatch, ic,
        subclauses={"4.1": "General"}, next_sub=None,
    )
    ic.main(clause_argv)
    assert "All subclauses are done" in capsys.readouterr().out


def test_main_closes_issue_when_all_done(
    ic, monkeypatch, clause_argv,
) -> None:
    """Sub-issue is closed when all subclauses are implemented."""
    _, __, mock_close, ___ = _patch_main_with_subclauses(
        monkeypatch, ic,
        subclauses={"4.1": "General"}, next_sub=None,
    )
    ic.main(clause_argv)
    assert mock_close.call_args == (
        ("o", "r", 1, "all subclauses are implemented"),
    )


def test_main_marks_master_after_close(
    ic, monkeypatch, clause_argv,
) -> None:
    """Master issue is marked complete after sub-issue is closed."""
    _, __, ___, mock_mark = _patch_main_with_subclauses(
        monkeypatch, ic,
        subclauses={"4.1": "General"}, next_sub=None,
    )
    ic.main(clause_argv)
    assert mock_mark.call_args == (
        ("o", "r", 99, 1),
    )


def test_main_annex(ic, monkeypatch, tmp_path) -> None:
    """Annex flag passes the letter to discover_subclauses."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    argv = [
        "--lrm", str(lrm), "--annex", "A",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
    ]
    mock_ds = MagicMock(return_value={"A.1": "General"})
    monkeypatch.setattr(ic, "discover_subclauses", mock_ds)
    monkeypatch.setattr(ic, "fetch_issue_body", lambda *_a: "")
    monkeypatch.setattr(ic, "build_synced_body", lambda *_a: "body")
    monkeypatch.setattr(ic, "update_issue_body", lambda *_a, **_kw: None)
    monkeypatch.setattr(ic, "next_unchecked", MagicMock(return_value=None))
    monkeypatch.setattr(ic, "invoke_implement_subclause", MagicMock())
    monkeypatch.setattr(ic, "close_issue", MagicMock())
    monkeypatch.setattr(ic, "mark_master_complete", MagicMock())
    ic.main(argv)
    assert mock_ds.call_args[0][1] == "A"


# --- invoke_implement_subclause ---


def test_invoke_implement_subclause_failure(ic, monkeypatch) -> None:
    """SystemExit on non-zero return code."""
    mock_run = MagicMock(
        return_value=subprocess.CompletedProcess(args=[], returncode=1),
    )
    monkeypatch.setattr(ic.subprocess, "run", mock_run)
    with pytest.raises(SystemExit):
        ic.invoke_implement_subclause(_STUB_ARGS, "4.2")


def test_invoke_implement_subclause_passes_continue(
    ic, invoke_subprocess_ok,
) -> None:
    """--continue appears in subprocess command when continue_session=True."""
    ic.invoke_implement_subclause(
        _STUB_ARGS, "4.2", continue_session=True,
    )
    assert "--continue" in invoke_subprocess_ok.call_args[0][0]


def test_invoke_implement_subclause_no_continue_by_default(
    ic, invoke_subprocess_ok,
) -> None:
    """--continue not in subprocess command by default."""
    ic.invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert "--continue" not in invoke_subprocess_ok.call_args[0][0]


def test_invoke_implement_subclause_no_figures_flag(
    ic, invoke_subprocess_ok,
) -> None:
    """invoke_implement_subclause does not pass --figures."""
    ic.invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert "--figures" not in invoke_subprocess_ok.call_args[0][0]


def test_invoke_implement_subclause_no_tables_flag(
    ic, invoke_subprocess_ok,
) -> None:
    """invoke_implement_subclause does not pass --tables."""
    ic.invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert "--tables" not in invoke_subprocess_ok.call_args[0][0]


# --- main loop ---


def test_main_loops_all_subclauses(ic, monkeypatch, clause_argv) -> None:
    """main invokes implement_subclause for each unchecked subclause."""
    mock_inv, _, __, ___ = _patch_main_with_subclauses(
        monkeypatch, ic, next_sub=["4.1", "4.2", None],
    )
    ic.main(clause_argv)
    assert mock_inv.call_count == 2


def test_main_first_subclause_no_continue(
    ic, monkeypatch, clause_argv,
) -> None:
    """First invocation does not pass continue_session=True."""
    mock_inv, _, __, ___ = _patch_main_with_subclauses(
        monkeypatch, ic, next_sub=["4.1", None],
    )
    ic.main(clause_argv)
    assert mock_inv.call_args_list[0].kwargs.get("continue_session") is not True


def test_main_second_subclause_uses_continue(
    ic, monkeypatch, clause_argv,
) -> None:
    """Second invocation passes continue_session=True."""
    mock_inv, _, __, ___ = _patch_main_with_subclauses(
        monkeypatch, ic, next_sub=["4.1", "4.2", None],
    )
    ic.main(clause_argv)
    assert mock_inv.call_args_list[1].kwargs["continue_session"] is True


def test_main_commits_after_each_subclause(
    ic, monkeypatch, clause_argv,
) -> None:
    """commit_and_push is called after each subclause implementation."""
    _, mock_cap, __, ___ = _patch_main_with_subclauses(
        monkeypatch, ic, next_sub=["4.1", "4.2", None],
    )
    ic.main(clause_argv)
    assert mock_cap.call_count == 2


def test_main_commits_with_subclause_number(
    ic, monkeypatch, clause_argv,
) -> None:
    """commit_and_push receives the subclause number."""
    _, mock_cap, __, ___ = _patch_main_with_subclauses(
        monkeypatch, ic, next_sub=["4.1", None],
    )
    ic.main(clause_argv)
    assert mock_cap.call_args[0][0] == "4.1"


# --- commit_and_push ---


def test_commit_and_push_stages_all(ic, monkeypatch) -> None:
    """commit_and_push runs git add -A."""
    calls = []

    def fake_run(cmd, **_kw):
        calls.append(cmd)
        return subprocess.CompletedProcess(args=cmd, returncode=0)

    monkeypatch.setattr(ic.subprocess, "run", fake_run)
    ic.commit_and_push("4.1")
    assert ["git", "add", "-A"] in calls


def test_commit_and_push_skips_when_nothing_staged(ic, monkeypatch) -> None:
    """commit_and_push skips commit/push when nothing is staged."""
    calls = []

    def fake_run(cmd, **_kw):
        calls.append(cmd)
        if cmd == ["git", "diff", "--cached", "--quiet"]:
            return subprocess.CompletedProcess(args=cmd, returncode=0)
        return subprocess.CompletedProcess(args=cmd, returncode=0)

    monkeypatch.setattr(ic.subprocess, "run", fake_run)
    ic.commit_and_push("4.1")
    assert not any(
        c[1] == "commit"
        for c in calls if isinstance(c, list) and len(c) > 1
    )


def test_commit_and_push_runs_commit(ic, commit_push_calls) -> None:
    """commit_and_push runs git commit when changes exist."""
    calls = commit_push_calls(ic)
    git_cmds = [c[1] for c in calls if isinstance(c, list) and c[0] == "git"]
    assert "commit" in git_cmds


def test_commit_and_push_runs_push(ic, commit_push_calls) -> None:
    """commit_and_push runs git push when changes exist."""
    calls = commit_push_calls(ic)
    git_cmds = [c[1] for c in calls if isinstance(c, list) and c[0] == "git"]
    assert "push" in git_cmds


def test_commit_and_push_message_contains_subclause(
    ic, commit_push_calls,
) -> None:
    """Commit message contains the subclause number."""
    calls = commit_push_calls(ic)
    commit_call = [c for c in calls if c[0] == "git" and c[1] == "commit"][0]
    msg_idx = commit_call.index("-m") + 1
    assert "4.1" in commit_call[msg_idx]


# --- discover_subclauses ---


def test_discover_subclauses_parses_json(ic, monkeypatch) -> None:
    """discover_subclauses parses Claude's JSON response."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "General", "4.2": "Exec", "4.3": false}\n',
        stderr="",
    )
    monkeypatch.setattr(ic.subprocess, "run", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {"4.1": "General", "4.2": "Exec"}


def test_discover_subclauses_strips_code_fences(ic, monkeypatch) -> None:
    """discover_subclauses strips markdown code fences from response."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='```json\n{"4.1": "General"}\n```\n',
        stderr="",
    )
    monkeypatch.setattr(ic.subprocess, "run", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {"4.1": "General"}


def test_discover_subclauses_strips_preamble_before_fences(
    ic, monkeypatch,
) -> None:
    """discover_subclauses extracts JSON from fences preceded by prose."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='Here is the JSON:\n\n```json\n{"4.1": "General"}\n```\n',
        stderr="",
    )
    monkeypatch.setattr(ic.subprocess, "run", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {"4.1": "General"}


def _discover_subclauses_prompt(ic, monkeypatch):
    """Helper: run discover_subclauses and return the prompt string."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "General"}\n',
        stderr="",
    )
    mock_run = MagicMock(return_value=cp)
    monkeypatch.setattr(ic.subprocess, "run", mock_run)
    ic.discover_subclauses(Path("/path/lrm.pdf"), "4")
    return mock_run.call_args[1]["input"]


def test_discover_subclauses_prompt_contains_clause(
    ic, monkeypatch,
) -> None:
    """discover_subclauses prompt references the clause number."""
    prompt = _discover_subclauses_prompt(ic, monkeypatch)
    assert "clause 4" in prompt.lower() or "§4" in prompt


def test_discover_subclauses_prompt_contains_lrm_path(
    ic, monkeypatch,
) -> None:
    """discover_subclauses prompt references the LRM PDF path."""
    prompt = _discover_subclauses_prompt(ic, monkeypatch)
    assert "/path/lrm.pdf" in prompt


def test_discover_subclauses_exits_on_claude_failure(
    ic, monkeypatch,
) -> None:
    """discover_subclauses exits when Claude CLI fails."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="error",
    )
    monkeypatch.setattr(ic.subprocess, "run", lambda *_a, **_kw: cp)
    with pytest.raises(SystemExit):
        ic.discover_subclauses(Path("/lrm.pdf"), "4")


def test_discover_subclauses_empty_result(ic, monkeypatch) -> None:
    """discover_subclauses returns empty dict when all false."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": false, "4.2": false}\n',
        stderr="",
    )
    monkeypatch.setattr(ic.subprocess, "run", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {}


def test_discover_subclauses_rationale_is_implementable(
    ic, monkeypatch,
) -> None:
    """Subclauses with string rationale are treated as implementable."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "Defines syntax rules that must be parsed"}\n',
        stderr="",
    )
    monkeypatch.setattr(ic.subprocess, "run", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert "4.1" in result


def test_discover_subclauses_default_model_is_opus(ic, monkeypatch) -> None:
    """discover_subclauses uses --model opus by default."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "General"}\n',
        stderr="",
    )
    mock_run = MagicMock(return_value=cp)
    monkeypatch.setattr(ic.subprocess, "run", mock_run)
    ic.discover_subclauses(Path("/lrm.pdf"), "4")
    cmd = mock_run.call_args[0][0]
    idx = cmd.index("--model")
    assert cmd[idx + 1] == "opus"


def test_discover_subclauses_passes_effort_high(ic, monkeypatch) -> None:
    """discover_subclauses passes --effort high to Claude CLI."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.1": "General"}\n',
        stderr="",
    )
    mock_run = MagicMock(return_value=cp)
    monkeypatch.setattr(ic.subprocess, "run", mock_run)
    ic.discover_subclauses(Path("/lrm.pdf"), "4")
    cmd = mock_run.call_args[0][0]
    idx = cmd.index("--effort")
    assert cmd[idx + 1] == "high"


def test_discover_subclauses_excludes_parent_clause(
    ic, monkeypatch,
) -> None:
    """discover_subclauses filters out the parent clause itself."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"15": "Processes", "15.1": "General"}\n',
        stderr="",
    )
    monkeypatch.setattr(ic.subprocess, "run", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "15")
    assert "15" not in result
    assert result == {"15.1": "General"}


def test_discover_subclauses_bool_true_is_implementable(
    ic, monkeypatch,
) -> None:
    """Subclauses with value true are treated as implementable."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"4.2": true}\n',
        stderr="",
    )
    monkeypatch.setattr(ic.subprocess, "run", lambda *_a, **_kw: cp)
    result = ic.discover_subclauses(Path("/lrm.pdf"), "4")
    assert result == {"4.2": "4.2"}
