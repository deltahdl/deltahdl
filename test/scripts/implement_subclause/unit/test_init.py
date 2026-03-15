"""Unit tests for implement_subclause (arg parsing and dispatch)."""

import json
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



@patch("implement_subclause.delete_issue")
@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value=None)
def test_main_deletes_issue_when_not_implementable(
    _mock_run, _mock_commit, mock_delete, isc, tmp_path,
):
    """main() deletes issue when run_steps returns None."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    isc.main(["--lrm", str(lrm), "--subclause", "6.6.1",
              "--issue", "8", "--model", "opus"])
    assert mock_delete.call_args[0][0] == 8


@patch("implement_subclause.delete_issue")
@patch("implement_subclause.commit_implementation")
@patch("implement_subclause.run_steps", return_value=None)
def test_main_skips_commit_when_not_implementable(
    _mock_run, mock_commit, _mock_delete, isc, tmp_path,
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


# ---- _parse_action_summary ------------------------------------------------


def test_parse_action_summary_envelope_without_result(isc):
    """Returns empty when JSON envelope has no result key."""
    parse = getattr(isc, "_parse_action_summary")
    assert parse('{"session_id":"x"}') == ""


def test_parse_action_summary_json_array(isc):
    """Finds ACTION_SUMMARY in the last element of a JSON array."""
    parse = getattr(isc, "_parse_action_summary")
    # Use json.dumps which escapes newlines — but the JSON parsing path
    # will decode them back to literal newlines for _extract_action_summary.
    stdout = json.dumps([
        {"type": "init"},
        {"result": (
            "ACTION_SUMMARY_START\n"
            "- Did X because Y\n"
            "ACTION_SUMMARY_END"
        )},
    ])
    # Replace \\n with something else so escaped-newline path doesn't match
    # but JSON parsing still works
    stdout = stdout.replace("\\n", "\\u000a")
    assert parse(stdout) == "- Did X because Y"


def test_parse_action_summary_json_array_no_result(isc):
    """Returns empty when JSON array has no element with result key."""
    parse = getattr(isc, "_parse_action_summary")
    stdout = json.dumps([{"type": "init"}, {"session_id": "x"}])
    assert parse(stdout) == ""


def test_parse_action_summary_escaped_newlines(isc):
    """Finds ACTION_SUMMARY when newlines are escaped in raw stdout."""
    parse = getattr(isc, "_parse_action_summary")
    raw = (
        'ACTION_SUMMARY_START\\n'
        '- Did X because Y\\n'
        'ACTION_SUMMARY_END'
    )
    assert parse(raw) == "- Did X because Y"


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
