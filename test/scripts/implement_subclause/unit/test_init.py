"""Unit tests for implement_subclause (arg parsing and dispatch)."""

import json
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


_MOCK_PROMPT_RESULT = "- Added foo.cpp"


# ---- main ------------------------------------------------------------------


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value="summary")
def test_main_dispatches_depth_1(mock_run, _mock_commit, isc, tmp_path):
    """main() passes model to run_steps."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "4", "--issue", "6", "--model", "opus"])
    assert mock_run.call_args[1]["model"] == "opus"


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value="summary")
def test_main_calls_commit_implementation_subclause(
    _mock_run, mock_commit, isc, tmp_path,
):
    """main() calls commit_implementation with the subclause."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1", "--issue", "8", "--model", "opus"])
    assert mock_commit.call_args[0][0] == "6.6.1"


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value="summary")
def test_main_calls_commit_implementation_issue(
    _mock_run, mock_commit, isc, tmp_path,
):
    """main() calls commit_implementation with the issue number."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1", "--issue", "8", "--model", "opus"])
    assert mock_commit.call_args[0][1] == 8


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value=_MOCK_PROMPT_RESULT)
def test_main_passes_action_to_commit(
    _mock_run, mock_commit, isc, tmp_path,
):
    """main() passes action summary from run_prompt to commit_implementation."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1", "--issue", "8", "--model", "opus"])
    assert mock_commit.call_args[1]["action"] == "- Added foo.cpp"


@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value=_MOCK_PROMPT_RESULT)
def test_main_prints_action_summary(
    _mock_run, _mock_commit, isc, tmp_path, capsys,
):
    """main() prints the action summary to stdout."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1", "--issue", "8", "--model", "opus"])
    assert "- Added foo.cpp" in capsys.readouterr().out



@patch("implement_subclause.subprocess.run",
       return_value=MagicMock(returncode=0))
@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value=None)
def test_main_closes_issue_when_not_implementable(
    _mock_run, _mock_commit, mock_gh, isc, tmp_path,
):
    """main() closes issue with comment when not implementable."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1",
              "--issue", "8", "--model", "opus"])
    cmd = mock_gh.call_args[0][0]
    assert "close" in cmd


@patch("implement_subclause.subprocess.run",
       return_value=MagicMock(returncode=0))
@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value=None)
def test_main_close_comment_deemed_not_implementable(
    _mock_run, _mock_commit, mock_gh, isc, tmp_path,
):
    """main() passes 'Deemed not implementable.' comment."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1",
              "--issue", "8", "--model", "opus"])
    cmd = mock_gh.call_args[0][0]
    assert "Deemed not implementable." in cmd


@patch("implement_subclause.subprocess.run",
       return_value=MagicMock(returncode=0))
@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value=None)
def test_main_skips_commit_when_not_implementable(
    _mock_run, mock_commit, _mock_gh, isc, tmp_path,
):
    """main() does not call commit_implementation when not implementable."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1",
              "--issue", "8", "--model", "opus"])
    assert not mock_commit.called


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


# ---- _extract_result_text --------------------------------------------------


def test_extract_result_text_json_envelope(isc):
    """Extracts result from JSON envelope."""
    extract = getattr(isc, "_extract_result_text")
    assert extract('{"result": "- Did X"}') == "- Did X"


def test_extract_result_text_json_array(isc):
    """Extracts result from JSON array envelope."""
    extract = getattr(isc, "_extract_result_text")
    stdout = json.dumps([{"type": "init"}, {"result": "- Did Y"}])
    assert extract(stdout) == "- Did Y"


def test_extract_result_text_no_result_key(isc):
    """Falls back to raw text when no result key."""
    extract = getattr(isc, "_extract_result_text")
    assert extract('{"session_id": "x"}') == '{"session_id": "x"}'


def test_extract_result_text_plain_text(isc):
    """Returns plain text when not valid JSON."""
    extract = getattr(isc, "_extract_result_text")
    assert extract("- Did Z because needed") == "- Did Z because needed"


def test_extract_result_text_array_no_result(isc):
    """Falls back to raw text when array has no result key."""
    extract = getattr(isc, "_extract_result_text")
    stdout = json.dumps([{"type": "init"}, {"session_id": "x"}])
    assert extract(stdout) == stdout.strip()


# ---- commit_implementation -------------------------------------------------


def _commit_impl_and_capture(isc, *, subclause="6.6.1", action="",
                             changes=None):
    """Run commit_implementation with standard mocks; return mock dict."""
    if changes is None:
        changes = (["a.cpp"], [], [])
    with (
        patch("implement_subclause.get_porcelain_changes",
              return_value=changes) as m_files,
        patch("implement_subclause.commit_and_push",
              return_value="abc123") as m_cap,
    ):
        isc.commit_implementation(subclause, 8, action=action)
    return {"files": m_files, "cap": m_cap}


def test_commit_implementation_calls_commit_and_push(isc):
    """commit_implementation passes files and message to commit_and_push."""
    assert _commit_impl_and_capture(isc)["cap"].called


def test_commit_implementation_message_has_subclause(isc):
    """Commit message uses section sign for numeric subclauses."""
    assert "Implement §6.6.1" in _commit_impl_and_capture(isc)["cap"].call_args[0][2]


def test_commit_implementation_message_annex_prefix(isc):
    """Commit message uses Annex prefix for annex subclauses."""
    msg = _commit_impl_and_capture(isc, subclause="A.8.1")["cap"].call_args[0][2]
    assert "Implement Annex A.8.1" in msg


def test_commit_implementation_message_no_co_authored_by(isc):
    """Commit message does not contain Co-Authored-By trailer."""
    assert "Co-Authored-By" not in _commit_impl_and_capture(isc)["cap"].call_args[0][2]


def test_commit_implementation_message_has_action(isc):
    """Commit message contains action text when provided."""
    mocks = _commit_impl_and_capture(isc, action="- Added foo.cpp")
    assert "- Added foo.cpp" in mocks["cap"].call_args[0][2]


def test_commit_implementation_message_omits_action_when_empty(isc):
    """Commit message has no double blank lines when action is empty."""
    msg = _commit_impl_and_capture(isc)["cap"].call_args[0][2]
    assert "\n\n\n" not in msg


def test_commit_implementation_changed_includes_added_and_modified(isc):
    """commit_and_push receives added + modified as changed files."""
    mocks = _commit_impl_and_capture(
        isc, changes=(["a.cpp"], ["b.cpp"], []),
    )
    assert mocks["cap"].call_args[0][0] == ["a.cpp", "b.cpp"]


def test_commit_implementation_message_closes_issue(isc):
    """Commit message contains Closes #issue."""
    msg = _commit_impl_and_capture(isc)["cap"].call_args[0][2]
    assert "Closes #8" in msg


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("implement_subclause", run_name="__main__")
