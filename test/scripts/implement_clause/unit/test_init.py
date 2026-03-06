"""Tests for implement_clause core functions."""

import argparse
import subprocess
import sys
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch

import pytest

_STUB_ARGS = argparse.Namespace(
    lrm="/path/lrm.txt", sub_issue=123, master_issue=99,
    organization="deltahdl", repo="deltahdl",
    figures={}, tables={}, ignore_figures=[],
)

@contextmanager
def _patch_main_with_subclauses(
    *, subclauses=None, implementable=None,
    synced_body="body", next_sub="4.2",
):
    """Patch all dependencies for main() with subclauses.

    *next_sub* can be a string (single call then None) or a list
    (successive return values via ``side_effect``).
    """
    if subclauses is None:
        subclauses = {"4.1": "General", "4.2": "Exec"}
    if implementable is None:
        implementable = list(subclauses.keys())

    if isinstance(next_sub, list):
        next_kw = {"side_effect": next_sub}
    else:
        next_kw = {"side_effect": [next_sub, None]}

    with (
        patch("implement_clause.parse_all_subclauses",
              return_value=subclauses),
        patch("implement_clause.extract_clause_text",
              return_value="text"),
        patch("implement_clause.filter_implementable",
              return_value=implementable),
        patch("implement_clause.fetch_issue_body", return_value=""),
        patch("implement_clause.build_synced_body",
              return_value=synced_body),
        patch("implement_clause.update_issue_body"),
        patch("implement_clause.next_unchecked", **next_kw),
        patch("implement_clause.invoke_implement_subclause") as mock_inv,
        patch("implement_clause.commit_and_push") as mock_cap,
        patch("implement_clause.close_issue") as mock_close,
        patch("implement_clause.mark_master_complete") as mock_mark,
    ):
        yield mock_inv, mock_cap, mock_close, mock_mark


def test_invoke_implement_subclause_calls_subprocess(
    ic, invoke_subprocess_ok,
) -> None:
    """Correct command is passed to subprocess.run."""
    ic.invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert invoke_subprocess_ok.call_args[0][0] == [
        sys.executable, "-m", "implement_subclause",
        "--lrm", "/path/lrm.txt",
        "--subclause", "4.2",
        "--issue", "123",
    ]


@pytest.mark.usefixtures("invoke_subprocess_ok")
def test_invoke_implement_subclause_prints_subclause(ic, capsys) -> None:
    """Prints which subclause is being invoked."""
    ic.invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert "4.2" in capsys.readouterr().out


# --- parse_args ---


def test_parse_args_clause(ic, tmp_path) -> None:
    """--clause flag sets args.clause to the number."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
    ])
    assert args.clause == "4"


def test_parse_args_annex(ic, tmp_path) -> None:
    """--annex flag sets args.annex to the letter."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--annex", "A",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
    ])
    assert args.annex == "A"


def test_parse_args_clause_and_annex_exclusive(ic, tmp_path) -> None:
    """--clause and --annex are mutually exclusive."""
    lrm = tmp_path / "lrm.txt"
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
    lrm = tmp_path / "lrm.txt"
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
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm),
            "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
        ])


# --- main ---


# --- parse_all_subclauses ---


_SAMPLE_LRM = """\
6. Data types

6.1 General
General text.

6.7 Net declarations
Net text.

6.7.1 Net data types
Data types text.

6.7.2 Drive strength
Drive text.

7. Aggregate data types
"""


def test_parse_all_subclauses_returns_all_descendants(ic, tmp_path) -> None:
    """All descendants at every depth are returned."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_SAMPLE_LRM)
    result = ic.parse_all_subclauses(lrm, "6")
    assert result == {
        "6.1": "General",
        "6.7": "Net declarations",
        "6.7.1": "Net data types",
        "6.7.2": "Drive strength",
    }


def test_parse_all_subclauses_leaf_returns_empty(ic, tmp_path) -> None:
    """Leaf clause with no children returns empty dict."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_SAMPLE_LRM)
    assert ic.parse_all_subclauses(lrm, "6.1") == {}


def test_parse_all_subclauses_mid_level(ic, tmp_path) -> None:
    """Mid-level clause returns its children."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_SAMPLE_LRM)
    assert ic.parse_all_subclauses(lrm, "6.7") == {
        "6.7.1": "Net data types",
        "6.7.2": "Drive strength",
    }


# --- main ---


def test_main_no_subclauses(ic, clause_argv) -> None:
    """Clause without subclauses invokes implement_subclause directly."""
    with (
        patch("implement_clause.parse_all_subclauses", return_value={}),
        patch("implement_clause.invoke_implement_subclause") as mock_inv,
        patch("implement_clause.close_issue"),
        patch("implement_clause.mark_master_complete"),
    ):
        ic.main(clause_argv)
    assert mock_inv.call_args[0][1] == "4"


def test_main_no_subclauses_forwards_tables(ic, tmp_path) -> None:
    """No-subclauses path forwards --tables to invoke_implement_subclause."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    tbl = tmp_path / "tbl.md"
    tbl.write_text("")
    argv = [
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
        "--tables", f"4_1={tbl}",
    ]
    with (
        patch("implement_clause.parse_all_subclauses", return_value={}),
        patch("implement_clause.invoke_implement_subclause") as mock_inv,
        patch("implement_clause.close_issue"),
        patch("implement_clause.mark_master_complete"),
    ):
        ic.main(argv)
    assert mock_inv.call_args.kwargs["tables"] == {"4-1": tbl}


def test_main_no_subclauses_prints_leaf(ic, clause_argv, capsys) -> None:
    """Prints that clause has no subclauses."""
    with (
        patch("implement_clause.parse_all_subclauses", return_value={}),
        patch("implement_clause.invoke_implement_subclause"),
        patch("implement_clause.close_issue"),
        patch("implement_clause.mark_master_complete"),
    ):
        ic.main(clause_argv)
    assert "No subclauses" in capsys.readouterr().out


def test_no_subclauses_closes_sub_issue(ic, clause_argv) -> None:
    """No-subclauses path closes the sub-issue."""
    with (
        patch("implement_clause.parse_all_subclauses", return_value={}),
        patch("implement_clause.invoke_implement_subclause"),
        patch("implement_clause.close_issue") as mock_close,
        patch("implement_clause.mark_master_complete"),
    ):
        ic.main(clause_argv)
    assert mock_close.call_args == (
        ("o", "r", 1, "all subclauses are implemented"),
    )


def test_no_subclauses_marks_master(ic, clause_argv) -> None:
    """No-subclauses path marks master issue complete."""
    with (
        patch("implement_clause.parse_all_subclauses", return_value={}),
        patch("implement_clause.invoke_implement_subclause"),
        patch("implement_clause.close_issue"),
        patch("implement_clause.mark_master_complete") as mock_mark,
    ):
        ic.main(clause_argv)
    assert mock_mark.call_args == (("o", "r", 99, 1),)


def test_main_with_subclauses(ic, clause_argv) -> None:
    """Next unchecked subclause is passed to implement_subclause."""
    with _patch_main_with_subclauses() as (mock_inv, _, __, ___):
        ic.main(clause_argv)
    assert mock_inv.call_args[0][1] == "4.2"


def test_main_prints_subclauses_found(ic, clause_argv, capsys) -> None:
    """Prints how many subclauses were discovered."""
    with _patch_main_with_subclauses() as (_, __, ___, ____):
        ic.main(clause_argv)
    assert "Found 2 subclauses" in capsys.readouterr().out


def test_main_prints_synced_body(ic, clause_argv, capsys) -> None:
    """Prints the synced issue body."""
    with _patch_main_with_subclauses(
        synced_body="## Subclauses\n\n- [ ] 4.1 General\n",
        next_sub="4.1",
    ) as (_, __, ___, ____):
        ic.main(clause_argv)
    assert "## Subclauses" in capsys.readouterr().out


def test_main_prints_next_subclause(ic, clause_argv, capsys) -> None:
    """Prints which subclause was picked as next."""
    with _patch_main_with_subclauses() as (_, __, ___, ____):
        ic.main(clause_argv)
    assert "Next unchecked: 4.2" in capsys.readouterr().out


def test_main_all_done(ic, clause_argv, capsys) -> None:
    """Prints all-done message when no unchecked subclauses remain."""
    with _patch_main_with_subclauses(
        subclauses={"4.1": "General"}, next_sub=None,
    ) as (_, __, ___, ____):
        ic.main(clause_argv)
    assert "All subclauses are done" in capsys.readouterr().out


def test_main_closes_issue_when_all_done(ic, clause_argv) -> None:
    """Sub-issue is closed when all subclauses are implemented."""
    with _patch_main_with_subclauses(
        subclauses={"4.1": "General"}, next_sub=None,
    ) as (_, __, mock_close, ___):
        ic.main(clause_argv)
    assert mock_close.call_args == (
        ("o", "r", 1, "all subclauses are implemented"),
    )


def test_main_marks_master_after_close(ic, clause_argv) -> None:
    """Master issue is marked complete after sub-issue is closed."""
    with _patch_main_with_subclauses(
        subclauses={"4.1": "General"}, next_sub=None,
    ) as (_, __, ___, mock_mark):
        ic.main(clause_argv)
    assert mock_mark.call_args == (
        ("o", "r", 99, 1),
    )


def test_main_annex(ic, tmp_path) -> None:
    """Annex flag passes the letter to parse_subclauses."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    argv = [
        "--lrm", str(lrm), "--annex", "A",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
    ]
    with (
        patch("implement_clause.parse_all_subclauses",
              return_value={}) as mock_ps,
        patch("implement_clause.invoke_implement_subclause"),
        patch("implement_clause.close_issue"),
        patch("implement_clause.mark_master_complete"),
    ):
        ic.main(argv)
    assert mock_ps.call_args[0][1] == "A"


# --- invoke_implement_subclause ---


def test_invoke_implement_subclause_failure(ic) -> None:
    """SystemExit on non-zero return code."""
    with patch("implement_clause.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=[], returncode=1,
        )
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


# --- main loop ---


def test_main_loops_all_subclauses(ic, clause_argv) -> None:
    """main invokes implement_subclause for each unchecked subclause."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", "4.2", None],
    ) as (mock_inv, _, __, ___):
        ic.main(clause_argv)
    assert mock_inv.call_count == 2


def test_main_first_subclause_no_continue(ic, clause_argv) -> None:
    """First invocation does not pass continue_session=True."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", None],
    ) as (mock_inv, _, __, ___):
        ic.main(clause_argv)
    assert mock_inv.call_args_list[0].kwargs.get("continue_session") is not True


def test_main_second_subclause_uses_continue(ic, clause_argv) -> None:
    """Second invocation passes continue_session=True."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", "4.2", None],
    ) as (mock_inv, _, __, ___):
        ic.main(clause_argv)
    assert mock_inv.call_args_list[1].kwargs["continue_session"] is True


def test_main_commits_after_each_subclause(ic, clause_argv) -> None:
    """commit_and_push is called after each subclause implementation."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", "4.2", None],
    ) as (_, mock_cap, __, ___):
        ic.main(clause_argv)
    assert mock_cap.call_count == 2


def test_main_commits_with_subclause_number(ic, clause_argv) -> None:
    """commit_and_push receives the subclause number."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", None],
    ) as (_, mock_cap, __, ___):
        ic.main(clause_argv)
    assert mock_cap.call_args[0][0] == "4.1"


# --- commit_and_push ---


def test_commit_and_push_stages_all(ic) -> None:
    """commit_and_push runs git add -A."""
    calls = []
    def fake_run(cmd, **_kw):
        calls.append(cmd)
        return subprocess.CompletedProcess(args=cmd, returncode=0)
    with patch("implement_clause.subprocess.run", side_effect=fake_run):
        ic.commit_and_push("4.1")
    assert ["git", "add", "-A"] in calls


def test_commit_and_push_skips_when_nothing_staged(ic) -> None:
    """commit_and_push skips commit/push when nothing is staged."""
    calls = []
    def fake_run(cmd, **_kw):
        calls.append(cmd)
        if cmd == ["git", "diff", "--cached", "--quiet"]:
            return subprocess.CompletedProcess(args=cmd, returncode=0)
        return subprocess.CompletedProcess(args=cmd, returncode=0)
    with patch("implement_clause.subprocess.run", side_effect=fake_run):
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


def test_commit_and_push_message_contains_subclause(ic, commit_push_calls) -> None:
    """Commit message contains the subclause number."""
    calls = commit_push_calls(ic)
    commit_call = [c for c in calls if c[0] == "git" and c[1] == "commit"][0]
    msg_idx = commit_call.index("-m") + 1
    assert "4.1" in commit_call[msg_idx]


# --- lrm_labels_for_clause (whole-clause) ---


_LRM_CLAUSE_WITH_TABLE = """\
List of figures
Figure 4-1\u2014Event scheduling regions

List of tables
Table 4-1\u2014PLI callbacks
"""


def testlrm_labels_for_clause_finds_figures(ic, tmp_path) -> None:
    """Finds figure labels for a clause."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_CLAUSE_WITH_TABLE)
    figs, _ = ic.lrm_labels_for_clause(lrm, "4")
    assert figs == ["4-1"]


def testlrm_labels_for_clause_finds_tables(ic, tmp_path) -> None:
    """Finds table labels for a clause."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_CLAUSE_WITH_TABLE)
    _, tbls = ic.lrm_labels_for_clause(lrm, "4")
    assert tbls == ["4-1"]


def testlrm_labels_for_clause_empty_figures(ic, tmp_path) -> None:
    """Returns empty figure list when no labels exist."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("No figures or tables here.\n")
    figs, _ = ic.lrm_labels_for_clause(lrm, "99")
    assert figs == []


def testlrm_labels_for_clause_empty_tables(ic, tmp_path) -> None:
    """Returns empty table list when no labels exist."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("No figures or tables here.\n")
    _, tbls = ic.lrm_labels_for_clause(lrm, "99")
    assert tbls == []


_LRM_ANNEX_WITH_TABLE = """\
List of tables
Table B.1\u2014Keywords
"""


def testlrm_labels_for_clause_finds_annex_tables(ic, tmp_path) -> None:
    """Finds dot-separated table labels for an annex clause."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_ANNEX_WITH_TABLE)
    _, tbls = ic.lrm_labels_for_clause(lrm, "B")
    assert tbls == ["B.1"]


def testlrm_labels_for_clause_ignores_other_clause_figures(ic, tmp_path) -> None:
    """Does not pick up figure labels from other clauses."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(
        "Figure 5-1\u2014Something\n"
        "Table 5-1\u2014Other\n"
    )
    figs, _ = ic.lrm_labels_for_clause(lrm, "4")
    assert figs == []


def testlrm_labels_for_clause_ignores_other_clause_tables(ic, tmp_path) -> None:
    """Does not pick up table labels from other clauses."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(
        "Figure 5-1\u2014Something\n"
        "Table 5-1\u2014Other\n"
    )
    _, tbls = ic.lrm_labels_for_clause(lrm, "4")
    assert tbls == []


# --- parse_args supplementary flags ---


def test_parse_args_figures(ic, tmp_path) -> None:
    """--figures flag is parsed as dict of shorthand to Path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    gv = tmp_path / "fig.gv"
    gv.write_text("digraph {}")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
        "--figures", f"4_1={gv}",
    ])
    assert args.figures == {"4-1": gv}


def test_parse_args_tables(ic, tmp_path) -> None:
    """--tables flag is parsed as dict of shorthand to Path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    md = tmp_path / "tbl.md"
    md.write_text("| col |\n")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
        "--tables", f"4_1={md}",
    ])
    assert args.tables == {"4-1": md}


def test_parse_args_ignore_figures(ic, tmp_path) -> None:
    """--ignore-figures flag is parsed as list of strings."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
        "--ignore-figures", "4-1,4-2",
    ])
    assert args.ignore_figures == ["4-1", "4-2"]


# --- early validation of supplementary args ---


_LRM_WITH_TABLE = """\
4. Scheduling semantics
Table 4-1\u2014PLI callbacks

4.1 General
General text.

5. Data types
"""


_LRM_WITH_FIGURE = """\
4. Scheduling semantics
Figure 4-1—Overview diagram

4.1 General
General text.

5. Data types
"""


@pytest.mark.parametrize(
    "lrm_content",
    [_LRM_WITH_TABLE, _LRM_WITH_FIGURE],
    ids=["tables_missing", "figures_missing"],
)
def test_main_exits_when_supplementary_missing(
    ic, tmp_path, lrm_content,
) -> None:
    """main() exits early when LRM has supplementary but flag not provided."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(lrm_content)
    with (
        patch("implement_clause.parse_all_subclauses") as mock_ps,
        pytest.raises(SystemExit),
    ):
        ic.main([
            "--lrm", str(lrm), "--clause", "4",
            "--sub-issue", "1", "--master-issue", "99",
        "--organization", "o", "--repo", "r",
        ])
    mock_ps.assert_not_called()


def test_main_no_exit_when_figures_ignored(ic, tmp_path) -> None:
    """main() does not exit when missing figures are in --ignore-figures."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_WITH_FIGURE)
    with (
        patch("implement_clause.parse_all_subclauses", return_value={}) as mock_ps,
        patch("implement_clause.invoke_implement_subclause"),
        patch("implement_clause.close_issue"),
        patch("implement_clause.mark_master_complete"),
    ):
        ic.main([
            "--lrm", str(lrm), "--clause", "4",
            "--sub-issue", "1", "--master-issue", "99",
            "--organization", "o", "--repo", "r",
            "--ignore-figures", "4-1",
        ])
    assert mock_ps.called


# --- invoke_implement_subclause forwarding ---


def test_invoke_forwards_tables_to_subclause(
    ic, invoke_subprocess_ok,
) -> None:
    """invoke_implement_subclause forwards --tables in key=path format."""
    args = argparse.Namespace(
        lrm="/path/lrm.txt", sub_issue=123, master_issue=99,
        organization="o", repo="r",
        figures={}, tables={"4-1": Path("/t/tbl.md")},
        ignore_figures=[],
    )
    ic.invoke_implement_subclause(
        args, "4.1", tables={"4-1": Path("/t/tbl.md")},
    )
    cmd = invoke_subprocess_ok.call_args[0][0]
    idx = cmd.index("--tables")
    assert cmd[idx + 1] == "4_1=/t/tbl.md"


def test_invoke_forwards_figures_to_subclause(
    ic, invoke_subprocess_ok,
) -> None:
    """invoke_implement_subclause forwards --figures in key=path format."""
    args = argparse.Namespace(
        lrm="/path/lrm.txt", sub_issue=123, master_issue=99,
        organization="o", repo="r",
        figures={"4-1": Path("/f/fig.gv")}, tables={},
        ignore_figures=[],
    )
    ic.invoke_implement_subclause(
        args, "4.1", figures={"4-1": Path("/f/fig.gv")},
    )
    cmd = invoke_subprocess_ok.call_args[0][0]
    idx = cmd.index("--figures")
    assert cmd[idx + 1] == "4_1=/f/fig.gv"


def test_invoke_forwards_annex_tables_to_subclause(
    ic, invoke_subprocess_ok,
) -> None:
    """invoke_implement_subclause forwards annex --tables with dot-to-underscore."""
    args = argparse.Namespace(
        lrm="/path/lrm.txt", sub_issue=123, master_issue=99,
        organization="o", repo="r",
        figures={}, tables={"B.1": Path("/t/tbl.md")},
        ignore_figures=[],
    )
    ic.invoke_implement_subclause(
        args, "B", tables={"B.1": Path("/t/tbl.md")},
    )
    cmd = invoke_subprocess_ok.call_args[0][0]
    idx = cmd.index("--tables")
    assert cmd[idx + 1] == "B_1=/t/tbl.md"


def test_invoke_no_tables_flag_when_empty(
    ic, invoke_subprocess_ok,
) -> None:
    """invoke_implement_subclause omits --tables when no tables to forward."""
    ic.invoke_implement_subclause(_STUB_ARGS, "4.1")
    cmd = invoke_subprocess_ok.call_args[0][0]
    assert "--tables" not in cmd


# --- mark_master_complete ---


_MASTER_BODY = """\
## Phase 1

| Section | Title | Issue | Status |
|---------|-------|-------|--------|
| §3 | Building blocks | #5 | :white_check_mark: |
| §4 | Scheduling semantics | #6 | |
"""


def _mark_master_and_capture(ic, monkeypatch, sub_issue=6) -> str:
    """Call mark_master_complete and return the updated body."""
    monkeypatch.setattr(
        "implement_clause.fetch_issue_body", lambda *_a: _MASTER_BODY,
    )
    updated: list[str] = []
    monkeypatch.setattr(
        "implement_clause.update_issue_body",
        lambda _o, _r, _i, body: updated.append(body),
    )
    ic.mark_master_complete("o", "r", 1, sub_issue)
    assert updated, "update_issue_body was not called"
    return updated[0]


def test_mark_master_complete_ticks_status(ic, monkeypatch) -> None:
    """Row matching the sub-issue gets :white_check_mark: in Status."""
    body = _mark_master_and_capture(ic, monkeypatch)
    assert "| #6 | :white_check_mark: |" in body


def test_mark_master_complete_preserves_other_rows(ic, monkeypatch) -> None:
    """Other rows are unchanged after marking."""
    body = _mark_master_and_capture(ic, monkeypatch)
    assert "| #5 | :white_check_mark: |" in body


def test_mark_master_complete_warns_when_not_found(
    ic, monkeypatch, capsys,
) -> None:
    """Prints warning when no matching row found."""
    monkeypatch.setattr(
        "implement_clause.fetch_issue_body", lambda *_a: _MASTER_BODY,
    )
    monkeypatch.setattr(
        "implement_clause.update_issue_body",
        lambda *_a: None,
    )
    ic.mark_master_complete("o", "r", 1, 999)
    assert "WARNING" in capsys.readouterr().err
