"""Unit tests for implement_subclause (arg parsing and dispatch)."""

import runpy
from unittest.mock import patch

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


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_prompt", return_value="- Added foo.cpp")
def test_main_passes_action_to_commit(
    _mock_run, mock_commit, isc, tmp_path,
):
    """main() passes action summary from run_prompt to commit_implementation."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1", "--issue", "8", "--model", "opus"])
    assert mock_commit.call_args[1]["action"] == "- Added foo.cpp"


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_prompt", return_value="- Added foo.cpp")
def test_main_prints_action_summary(
    _mock_run, _mock_commit, isc, tmp_path, capsys,
):
    """main() prints the action summary to stdout."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1", "--issue", "8", "--model", "opus"])
    assert "- Added foo.cpp" in capsys.readouterr().out


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_prompt", return_value="")
def test_main_skips_action_print_when_empty(
    _mock_run, _mock_commit, isc, tmp_path, capsys,
):
    """main() does not print action summary when it is empty."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1", "--issue", "8", "--model", "opus"])
    assert "Action summary" not in capsys.readouterr().out


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


# ---- _extract_action_summary ------------------------------------------------


def test_extract_action_summary_found(isc):
    """Returns content between ACTION_SUMMARY delimiters."""
    extract = getattr(isc, "_extract_action_summary")
    text = (
        "Some preamble.\n"
        "ACTION_SUMMARY_START\n"
        "- Added foo.cpp\n"
        "- Modified bar.cpp\n"
        "ACTION_SUMMARY_END\n"
        "Trailing text."
    )
    assert extract(text) == "- Added foo.cpp\n- Modified bar.cpp"


def test_extract_action_summary_not_found(isc):
    """Returns empty string when no ACTION_SUMMARY block is present."""
    extract = getattr(isc, "_extract_action_summary")
    assert extract("No summary here.") == ""


def test_extract_action_summary_strips_whitespace(isc):
    """Strips leading/trailing whitespace from extracted summary."""
    extract = getattr(isc, "_extract_action_summary")
    text = (
        "ACTION_SUMMARY_START\n"
        "  - Did something  \n"
        "ACTION_SUMMARY_END"
    )
    assert extract(text) == "- Did something"


# ---- commit_implementation -------------------------------------------------


def _commit_impl_and_capture(isc, *, action="",
                             added=None, modified=None, deleted=None):
    """Run commit_implementation with standard mocks; return mock dict."""
    if added is None:
        added = ["a.cpp"]
    if modified is None:
        modified = []
    if deleted is None:
        deleted = []
    with (
        patch("implement_subclause.get_porcelain_changes",
              return_value=(added, modified, deleted)) as m_files,
        patch("implement_subclause.commit_and_push",
              return_value="abc123") as m_cap,
        patch("implement_subclause.get_remote_repo",
              return_value=("org", "repo")) as m_repo,
        patch("implement_subclause.mark_subclause_complete") as m_mark,
    ):
        isc.commit_implementation("6.6.1", 8, action=action)
    return {"files": m_files, "cap": m_cap, "repo": m_repo, "mark": m_mark}


def test_commit_implementation_calls_commit_and_push(isc):
    """commit_implementation passes files and message to commit_and_push."""
    assert _commit_impl_and_capture(isc)["cap"].called


def test_commit_implementation_message_has_subclause(isc):
    """Commit message contains the subclause."""
    assert "§6.6.1" in _commit_impl_and_capture(isc)["cap"].call_args[0][2]


def test_commit_implementation_message_has_co_authored_by(isc):
    """Commit message contains Co-Authored-By trailer."""
    assert "Co-Authored-By:" in _commit_impl_and_capture(isc)["cap"].call_args[0][2]


def test_commit_implementation_calls_mark_subclause_complete(isc):
    """commit_implementation marks the subclause complete on the issue."""
    mocks = _commit_impl_and_capture(isc)
    assert mocks["mark"].call_args[0] == ("org", "repo", 8, "6.6.1", "abc123")


@patch("implement_subclause.mark_subclause_complete")
@patch("implement_subclause.commit_and_push", return_value=None)
@patch("implement_subclause.get_porcelain_changes", return_value=([], [], []))
def test_commit_implementation_skips_mark_when_no_sha(
    _mock_files, _mock_cap, mock_mark, isc,
):
    """commit_implementation does not mark when commit_and_push returns None."""
    isc.commit_implementation("6.6.1", 8)
    assert not mock_mark.called


def test_commit_implementation_message_has_action(isc):
    """Commit message contains action text when provided."""
    mocks = _commit_impl_and_capture(isc, action="- Added foo.cpp")
    assert "- Added foo.cpp" in mocks["cap"].call_args[0][2]


def test_commit_implementation_message_omits_action_when_empty(isc):
    """Commit message has no double blank lines when action is empty."""
    msg = _commit_impl_and_capture(isc)["cap"].call_args[0][2]
    assert "\n\n\n" not in msg


def test_commit_implementation_message_has_file_summary(isc):
    """Commit message contains file change summary."""
    mocks = _commit_impl_and_capture(
        isc, added=["new.cpp"], modified=["old.cpp"],
    )
    assert "Added new.cpp" in mocks["cap"].call_args[0][2]


def test_commit_implementation_message_has_both_summary_and_action(isc):
    """Commit message contains both file summary and action rationale."""
    mocks = _commit_impl_and_capture(
        isc, added=["new.cpp"], action="- Implemented feature X",
    )
    msg = mocks["cap"].call_args[0][2]
    assert "Added new.cpp" in msg


def test_commit_implementation_changed_includes_added_and_modified(isc):
    """commit_and_push receives added + modified as changed files."""
    mocks = _commit_impl_and_capture(
        isc, added=["a.cpp"], modified=["b.cpp"],
    )
    assert mocks["cap"].call_args[0][0] == ["a.cpp", "b.cpp"]


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("implement_subclause", run_name="__main__")
