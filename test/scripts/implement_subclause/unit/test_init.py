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


# ---- build_action_summary --------------------------------------------------


def test_build_action_summary_added_bullets(isc):
    """Added paths produce 'Added' bullets in sorted order."""
    summary = isc.build_action_summary(["b.cpp", "a.cpp"], [], [])
    assert summary == "- Added a.cpp\n- Added b.cpp"


def test_build_action_summary_modified_bullets(isc):
    """Modified paths produce 'Modified' bullets."""
    summary = isc.build_action_summary([], ["x.h"], [])
    assert summary == "- Modified x.h"


def test_build_action_summary_deleted_bullets(isc):
    """Deleted paths produce 'Deleted' bullets."""
    summary = isc.build_action_summary([], [], ["old.cpp"])
    assert summary == "- Deleted old.cpp"


def test_build_action_summary_combined(isc):
    """Combined output orders added, then modified, then deleted."""
    summary = isc.build_action_summary(["a.cpp"], ["b.h"], ["c.cpp"])
    assert summary == "- Added a.cpp\n- Modified b.h\n- Deleted c.cpp"


def test_build_action_summary_empty(isc):
    """Empty inputs produce an empty string."""
    assert isc.build_action_summary([], [], []) == ""


# ---- main ------------------------------------------------------------------


_STEP_RESULTS = [f"step-{i}-summary" for i in range(1, 10)]


def _run_main_success(isc, tmp_path, *, changes=(["foo.cpp"], [], []),
                      step_results=None):
    """Run main() with run_steps success and stubbed git changes."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with (
        patch("implement_subclause.run_steps",
              return_value=step_results or _STEP_RESULTS) as mock_run,
        patch("implement_subclause.commit_implementation") as mock_commit,
        patch("implement_subclause.get_porcelain_changes",
              return_value=changes),
    ):
        isc.main([
            "--lrm", str(lrm), "--subclause", "6.6.1",
            "--issue", "8", "--model", "opus",
        ])
    return {"run": mock_run, "commit": mock_commit}


def test_main_dispatches_depth_1(isc, tmp_path):
    """main() passes model to run_steps."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    with (
        patch("implement_subclause.run_steps",
              return_value=_STEP_RESULTS) as mock_run,
        patch("implement_subclause.commit_implementation"),
        patch("implement_subclause.get_porcelain_changes",
              return_value=([], [], [])),
    ):
        isc.main([
            "--lrm", str(lrm), "--subclause", "4",
            "--issue", "6", "--model", "opus",
        ])
    assert mock_run.call_args[1]["model"] == "opus"


def test_main_uses_step_result_when_porcelain_empty(isc, tmp_path):
    """main() falls back to last step_results entry when porcelain empty."""
    mocks = _run_main_success(isc, tmp_path, changes=([], [], []))
    assert mocks["commit"].call_args[1]["action"] == "step-9-summary"


def test_main_prints_step_result_when_porcelain_empty(
    isc, tmp_path, capsys,
):
    """main() prints the step_results fallback under Action summary."""
    _run_main_success(isc, tmp_path, changes=([], [], []))
    assert "step-9-summary" in capsys.readouterr().out


def test_main_prefers_porcelain_over_step_results(isc, tmp_path):
    """main() uses porcelain-derived action when porcelain is non-empty."""
    mocks = _run_main_success(isc, tmp_path)
    assert mocks["commit"].call_args[1]["action"] == "- Added foo.cpp"


def test_main_calls_commit_implementation_subclause(isc, tmp_path):
    """main() calls commit_implementation with the subclause."""
    mocks = _run_main_success(isc, tmp_path)
    assert mocks["commit"].call_args[0][0] == "6.6.1"


def test_main_calls_commit_implementation_issue(isc, tmp_path):
    """main() calls commit_implementation with the issue number."""
    mocks = _run_main_success(isc, tmp_path)
    assert mocks["commit"].call_args[0][1] == 8


def test_main_passes_action_to_commit(isc, tmp_path):
    """main() builds the action summary from git status and passes it down."""
    mocks = _run_main_success(isc, tmp_path)
    assert mocks["commit"].call_args[1]["action"] == "- Added foo.cpp"


def test_main_prints_action_summary(isc, tmp_path, capsys):
    """main() prints the action summary to stdout."""
    _run_main_success(isc, tmp_path)
    assert "- Added foo.cpp" in capsys.readouterr().out


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


# ---- commit_implementation -------------------------------------------------


def _commit_impl_and_capture(isc, *, subclause="6.6.1", action="",
                             changes=None):
    """Run commit_implementation with standard mocks; return mock dict."""
    if changes is None:
        changes = (["a.cpp"], [], [])
    added, modified, deleted = changes
    with (
        patch("implement_subclause.commit_and_push",
              return_value="abc123") as m_cap,
        patch("implement_subclause.subprocess.run",
              return_value=MagicMock(returncode=0)) as m_gh,
    ):
        isc.commit_implementation(
            subclause, 8,
            changed=added + modified, deleted=deleted,
            action=action,
        )
    return {"cap": m_cap, "gh": m_gh}


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


def test_commit_implementation_skips_commit_when_no_changes(isc):
    """commit_implementation skips commit_and_push when all lists empty."""
    mocks = _commit_impl_and_capture(isc, changes=([], [], []))
    assert not mocks["cap"].called


def test_main_filters_garbage_files(isc, tmp_path):
    """main() filters garbage paths before calling commit_implementation."""
    mocks = _run_main_success(
        isc, tmp_path,
        changes=(["a.cpp", "2", "{a,"], ["b.h"], ["old"]),
    )
    assert mocks["commit"].call_args[1]["changed"] == ["a.cpp", "b.h"]


def test_main_filters_garbage_deleted(isc, tmp_path):
    """main() filters garbage paths from the deleted list."""
    mocks = _run_main_success(
        isc, tmp_path,
        changes=(["a.cpp"], [], ["old", "{a,"]),
    )
    assert mocks["commit"].call_args[1]["deleted"] == []


def test_main_filters_accepts_cmakelists(isc, tmp_path):
    """main() accepts CMakeLists.txt as a valid path."""
    mocks = _run_main_success(
        isc, tmp_path,
        changes=(["a.cpp"], ["test/CMakeLists.txt"], []),
    )
    assert "test/CMakeLists.txt" in mocks["commit"].call_args[1]["changed"]


def test_main_filters_accepts_python(isc, tmp_path):
    """main() accepts .py files as valid paths."""
    mocks = _run_main_success(
        isc, tmp_path,
        changes=(["foo.py"], [], []),
    )
    assert mocks["commit"].call_args[1]["changed"] == ["foo.py"]


def test_commit_implementation_closes_issue_when_no_changes(isc):
    """commit_implementation closes issue via gh when no valid changes."""
    mocks = _commit_impl_and_capture(
        isc, changes=([], [], []), action="No changes needed.",
    )
    cmd = mocks["gh"].call_args[0][0]
    assert "close" in cmd


def test_commit_implementation_close_comment_has_action(isc):
    """commit_implementation passes action summary as close comment."""
    mocks = _commit_impl_and_capture(
        isc, changes=([], [], []), action="Nothing to do.",
    )
    cmd = mocks["gh"].call_args[0][0]
    assert "Nothing to do." in cmd


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("implement_subclause", run_name="__main__")
