"""Unit tests for implement_subclause (arg parsing and dispatch)."""

import runpy
from unittest.mock import MagicMock, patch

import pytest


# ---- clause_depth -----------------------------------------------------------


def test_clause_depth_1(isc):
    """Single component has depth 1."""
    assert isc.clause_depth("4") == 1


def test_clause_depth_1_annex(isc):
    """Single letter component has depth 1."""
    assert isc.clause_depth("B") == 1


def test_clause_depth_2(isc):
    """Two components have depth 2."""
    assert isc.clause_depth("4.1") == 2


def test_clause_depth_3(isc):
    """Three components have depth 3."""
    assert isc.clause_depth("6.24.1") == 3


def test_clause_depth_4(isc):
    """Four components have depth 4."""
    assert isc.clause_depth("4.4.3.1") == 4


def test_clause_depth_5(isc):
    """Five components have depth 5."""
    assert isc.clause_depth("4.4.3.1.2") == 5


# ---- parse_args -------------------------------------------------------------


def test_parse_args_requires_issue(isc, tmp_path):
    """--issue is required; omitting it exits."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        isc.parse_args(["--lrm", str(lrm), "--subclause", "4.1"])


def test_parse_args_accepts_issue(isc, tmp_path):
    """--issue is parsed as int."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args(["--lrm", str(lrm), "--subclause", "4.1", "--issue", "8"])
    assert args.issue == 8


def test_parse_args_model_default(isc, tmp_path):
    """--model defaults to 'opus'."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
    ])
    assert args.model == "opus"


def test_parse_args_model_override(isc, tmp_path):
    """--model can be overridden."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
        "--model", "opus",
    ])
    assert args.model == "opus"


def test_parse_args_rejects_bad_clause(isc, tmp_path):
    """Invalid clause format exits."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        isc.parse_args([
            "--lrm", str(lrm), "--subclause", "bad", "--issue", "8",
        ])


def test_parse_args_rejects_missing_lrm(isc, tmp_path):
    """Non-existent LRM file exits."""
    with pytest.raises(SystemExit):
        isc.parse_args([
            "--lrm", str(tmp_path / "no.txt"), "--subclause", "4.1",
            "--issue", "8",
        ])


def test_parse_args_accepts_annex_clause(isc, tmp_path):
    """Uppercase letter clause is accepted."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "B", "--issue", "44",
    ])
    assert (args.subclause, args.issue) == ("B", 44)


def test_parse_args_continue_flag(isc, tmp_path):
    """--continue sets continue_session to True."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
        "--continue",
    ])
    assert args.continue_session is True


def test_parse_args_continue_default_false(isc, tmp_path):
    """continue_session defaults to False."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
    ])
    assert args.continue_session is False


def test_parse_args_exclude_default_empty(isc, tmp_path):
    """--exclude defaults to empty string."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
    ])
    assert args.exclude == ""


def test_parse_args_exclude_value(isc, tmp_path):
    """--exclude accepts a comma-separated string."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = isc.parse_args([
        "--lrm", str(lrm), "--subclause", "15.3", "--issue", "8",
        "--exclude", "15.3.1,15.3.2",
    ])
    assert args.exclude == "15.3.1,15.3.2"


# ---- main ------------------------------------------------------------------


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_prompt")
def test_main_dispatches_depth_1(mock_run, _mock_commit, isc, tmp_path):
    """main() passes args namespace to run_prompt."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "4", "--issue", "6", "--model", "opus"])
    assert mock_run.call_args[0][1].model == "opus"


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_prompt")
def test_main_calls_commit_implementation_subclause(
    _mock_run, mock_commit, isc, tmp_path,
):
    """main() calls commit_implementation with the subclause."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1", "--issue", "8", "--model", "opus"])
    assert mock_commit.call_args[0][0] == "6.6.1"


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_prompt")
def test_main_calls_commit_implementation_issue(
    _mock_run, mock_commit, isc, tmp_path,
):
    """main() calls commit_implementation with the issue number."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1", "--issue", "8", "--model", "opus"])
    assert mock_commit.call_args[0][1] == 8


def test_parse_args_rejects_figures_flag(isc, tmp_path):
    """--figures flag is no longer accepted."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        isc.parse_args([
            "--lrm", str(lrm), "--subclause", "4", "--issue", "6",
            "--figures", "4_1=fig.gv",
        ])


def test_parse_args_rejects_tables_flag(isc, tmp_path):
    """--tables flag is no longer accepted."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        isc.parse_args([
            "--lrm", str(lrm), "--subclause", "4", "--issue", "6",
            "--tables", "4_1=tbl.md",
        ])


# ---- get_unstaged_files -----------------------------------------------------


def test_get_unstaged_files_modified(monkeypatch, isc):
    """Modified files appear in changed list."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = " M src/foo.cpp\n"
    mock_result.stderr = ""
    monkeypatch.setattr("implement_subclause.run_git", lambda *a, **kw: mock_result)
    changed, _deleted = isc.get_unstaged_files()
    assert "src/foo.cpp" in changed


def test_get_unstaged_files_untracked(monkeypatch, isc):
    """Untracked files appear in changed list."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "?? src/new.cpp\n"
    mock_result.stderr = ""
    monkeypatch.setattr("implement_subclause.run_git", lambda *a, **kw: mock_result)
    changed, _deleted = isc.get_unstaged_files()
    assert "src/new.cpp" in changed


def test_get_unstaged_files_deleted(monkeypatch, isc):
    """Deleted files appear in deleted list."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = " D src/old.cpp\n"
    mock_result.stderr = ""
    monkeypatch.setattr("implement_subclause.run_git", lambda *a, **kw: mock_result)
    _changed, deleted = isc.get_unstaged_files()
    assert "src/old.cpp" in deleted


def test_get_unstaged_files_empty_changed(monkeypatch, isc):
    """Empty status returns empty changed list."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""
    monkeypatch.setattr("implement_subclause.run_git", lambda *a, **kw: mock_result)
    changed, _ = isc.get_unstaged_files()
    assert changed == []


def test_get_unstaged_files_empty_deleted(monkeypatch, isc):
    """Empty status returns empty deleted list."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""
    monkeypatch.setattr("implement_subclause.run_git", lambda *a, **kw: mock_result)
    _, deleted = isc.get_unstaged_files()
    assert deleted == []


def test_get_unstaged_files_skips_blank_lines(monkeypatch, isc):
    """Blank lines in status output are skipped."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = " M a.cpp\n\n M b.cpp\n"
    mock_result.stderr = ""
    monkeypatch.setattr("implement_subclause.run_git", lambda *a, **kw: mock_result)
    changed, _ = isc.get_unstaged_files()
    assert len(changed) == 2


# ---- commit_implementation -------------------------------------------------


@patch("implement_subclause.mark_subclause_complete")
@patch("implement_subclause.get_remote_repo", return_value=("org", "repo"))
@patch("implement_subclause.commit_and_push", return_value="abc123")
@patch("implement_subclause.get_unstaged_files", return_value=(["a.cpp"], []))
def test_commit_implementation_calls_commit_and_push(
    _mock_files, mock_cap, _mock_repo, _mock_mark, isc,
):
    """commit_implementation passes files and message to commit_and_push."""
    isc.commit_implementation("6.6.1", 8)
    assert mock_cap.called


@patch("implement_subclause.mark_subclause_complete")
@patch("implement_subclause.get_remote_repo", return_value=("org", "repo"))
@patch("implement_subclause.commit_and_push", return_value="abc123")
@patch("implement_subclause.get_unstaged_files", return_value=(["a.cpp"], []))
def test_commit_implementation_message_has_subclause(
    _mock_files, mock_cap, _mock_repo, _mock_mark, isc,
):
    """Commit message contains the subclause."""
    isc.commit_implementation("6.6.1", 8)
    assert "§6.6.1" in mock_cap.call_args[0][2]


@patch("implement_subclause.mark_subclause_complete")
@patch("implement_subclause.get_remote_repo", return_value=("org", "repo"))
@patch("implement_subclause.commit_and_push", return_value="abc123")
@patch("implement_subclause.get_unstaged_files", return_value=(["a.cpp"], []))
def test_commit_implementation_message_has_co_authored_by(
    _mock_files, mock_cap, _mock_repo, _mock_mark, isc,
):
    """Commit message contains Co-Authored-By trailer."""
    isc.commit_implementation("6.6.1", 8)
    assert "Co-Authored-By:" in mock_cap.call_args[0][2]


@patch("implement_subclause.mark_subclause_complete")
@patch("implement_subclause.get_remote_repo", return_value=("org", "repo"))
@patch("implement_subclause.commit_and_push", return_value="abc123")
@patch("implement_subclause.get_unstaged_files", return_value=(["a.cpp"], []))
def test_commit_implementation_calls_mark_subclause_complete(
    _mock_files, _mock_cap, _mock_repo, mock_mark, isc,
):
    """commit_implementation marks the subclause complete on the issue."""
    isc.commit_implementation("6.6.1", 8)
    assert mock_mark.call_args[0] == ("org", "repo", 8, "6.6.1", "abc123")


@patch("implement_subclause.mark_subclause_complete")
@patch("implement_subclause.commit_and_push", return_value=None)
@patch("implement_subclause.get_unstaged_files", return_value=([], []))
def test_commit_implementation_skips_mark_when_no_sha(
    _mock_files, _mock_cap, mock_mark, isc,
):
    """commit_implementation does not mark when commit_and_push returns None."""
    isc.commit_implementation("6.6.1", 8)
    assert not mock_mark.called


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("implement_subclause", run_name="__main__")
