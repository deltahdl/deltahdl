"""Tests for implement_clause core functions."""

import argparse
import subprocess
import sys
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch

import pytest

_STUB_ARGS = argparse.Namespace(
    lrm="/path/lrm.txt", issue=123,
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
        patch("implement_clause.parse_subclauses",
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
    ):
        yield mock_inv, mock_cap


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
        "--issue", "1", "--organization", "o", "--repo", "r",
    ])
    assert args.clause == "4"


def test_parse_args_annex(ic, tmp_path) -> None:
    """--annex flag sets args.annex to the letter."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--annex", "A",
        "--issue", "1", "--organization", "o", "--repo", "r",
    ])
    assert args.annex == "A"


def test_parse_args_clause_and_annex_exclusive(ic, tmp_path) -> None:
    """--clause and --annex are mutually exclusive."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm), "--clause", "4", "--annex", "A",
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])


def test_parse_args_missing_lrm(ic) -> None:
    """SystemExit when --lrm points to a nonexistent file."""
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", "/no/such/file", "--clause", "4",
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])


def test_parse_args_issue_is_int(ic, tmp_path) -> None:
    """--issue is parsed as an integer."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "42", "--organization", "o", "--repo", "r",
    ])
    assert args.issue == 42


def test_parse_args_no_clause_or_annex(ic, tmp_path) -> None:
    """SystemExit when neither --clause nor --annex is provided."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        ic.parse_args([
            "--lrm", str(lrm),
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])


# --- main ---


def test_main_no_subclauses(ic, clause_argv) -> None:
    """Clause without subclauses invokes implement_subclause directly."""
    with (
        patch("implement_clause.parse_subclauses", return_value={}),
        patch("implement_clause.invoke_implement_subclause") as mock_inv,
    ):
        ic.main(clause_argv)
    assert mock_inv.call_args[0][1] == "4"


def test_main_no_subclauses_prints_leaf(ic, clause_argv, capsys) -> None:
    """Prints that clause has no subclauses."""
    with (
        patch("implement_clause.parse_subclauses", return_value={}),
        patch("implement_clause.invoke_implement_subclause"),
    ):
        ic.main(clause_argv)
    assert "No subclauses" in capsys.readouterr().out


def test_main_with_subclauses(ic, clause_argv) -> None:
    """Next unchecked subclause is passed to implement_subclause."""
    with _patch_main_with_subclauses() as (mock_inv, _):
        ic.main(clause_argv)
    assert mock_inv.call_args[0][1] == "4.2"


def test_main_prints_subclauses_found(ic, clause_argv, capsys) -> None:
    """Prints how many subclauses were discovered."""
    with _patch_main_with_subclauses() as (_, __):
        ic.main(clause_argv)
    assert "Found 2 subclauses" in capsys.readouterr().out


def test_main_prints_synced_body(ic, clause_argv, capsys) -> None:
    """Prints the synced issue body."""
    with _patch_main_with_subclauses(
        synced_body="## Subclauses\n\n- [ ] 4.1 General\n",
        next_sub="4.1",
    ) as (_, __):
        ic.main(clause_argv)
    assert "## Subclauses" in capsys.readouterr().out


def test_main_prints_next_subclause(ic, clause_argv, capsys) -> None:
    """Prints which subclause was picked as next."""
    with _patch_main_with_subclauses() as (_, __):
        ic.main(clause_argv)
    assert "Next unchecked: 4.2" in capsys.readouterr().out


def test_main_all_done(ic, clause_argv, capsys) -> None:
    """Prints all-done message when no unchecked subclauses remain."""
    with _patch_main_with_subclauses(
        subclauses={"4.1": "General"}, next_sub=None,
    ) as (_, __):
        ic.main(clause_argv)
    assert "All subclauses are done" in capsys.readouterr().out


def test_main_annex(ic, tmp_path) -> None:
    """Annex flag passes the letter to parse_subclauses."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    argv = [
        "--lrm", str(lrm), "--annex", "A",
        "--issue", "1", "--organization", "o", "--repo", "r",
    ]
    with (
        patch("implement_clause.parse_subclauses",
              return_value={}) as mock_ps,
        patch("implement_clause.invoke_implement_subclause"),
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
    ) as (mock_inv, _):
        ic.main(clause_argv)
    assert mock_inv.call_count == 2


def test_main_first_subclause_no_continue(ic, clause_argv) -> None:
    """First invocation does not pass continue_session=True."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", None],
    ) as (mock_inv, _):
        ic.main(clause_argv)
    assert mock_inv.call_args_list[0].kwargs.get("continue_session") is not True


def test_main_second_subclause_uses_continue(ic, clause_argv) -> None:
    """Second invocation passes continue_session=True."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", "4.2", None],
    ) as (mock_inv, _):
        ic.main(clause_argv)
    assert mock_inv.call_args_list[1].kwargs["continue_session"] is True


def test_main_commits_after_each_subclause(ic, clause_argv) -> None:
    """commit_and_push is called after each subclause implementation."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", "4.2", None],
    ) as (_, mock_cap):
        ic.main(clause_argv)
    assert mock_cap.call_count == 2


def test_main_commits_with_subclause_number(ic, clause_argv) -> None:
    """commit_and_push receives the subclause number."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", None],
    ) as (_, mock_cap):
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


def test_commit_and_push_runs_commit(ic) -> None:
    """commit_and_push runs git commit when changes exist."""
    calls = []
    def fake_run(cmd, **_kw):
        calls.append(cmd)
        if cmd == ["git", "diff", "--cached", "--quiet"]:
            return subprocess.CompletedProcess(args=cmd, returncode=1)
        return subprocess.CompletedProcess(args=cmd, returncode=0)
    with patch("implement_clause.subprocess.run", side_effect=fake_run):
        ic.commit_and_push("4.1")
    git_cmds = [c[1] for c in calls if isinstance(c, list) and c[0] == "git"]
    assert "commit" in git_cmds


def test_commit_and_push_runs_push(ic) -> None:
    """commit_and_push runs git push when changes exist."""
    calls = []
    def fake_run(cmd, **_kw):
        calls.append(cmd)
        if cmd == ["git", "diff", "--cached", "--quiet"]:
            return subprocess.CompletedProcess(args=cmd, returncode=1)
        return subprocess.CompletedProcess(args=cmd, returncode=0)
    with patch("implement_clause.subprocess.run", side_effect=fake_run):
        ic.commit_and_push("4.1")
    git_cmds = [c[1] for c in calls if isinstance(c, list) and c[0] == "git"]
    assert "push" in git_cmds


def test_commit_and_push_message_contains_subclause(ic) -> None:
    """Commit message contains the subclause number."""
    calls = []
    def fake_run(cmd, **kw):
        calls.append((cmd, kw))
        if cmd == ["git", "diff", "--cached", "--quiet"]:
            return subprocess.CompletedProcess(args=cmd, returncode=1)
        return subprocess.CompletedProcess(args=cmd, returncode=0)
    with patch("implement_clause.subprocess.run", side_effect=fake_run):
        ic.commit_and_push("4.1")
    commit_call = [c for c, k in calls if c[0] == "git" and c[1] == "commit"][0]
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
        "--issue", "1", "--organization", "o", "--repo", "r",
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
        "--issue", "1", "--organization", "o", "--repo", "r",
        "--tables", f"4_1={md}",
    ])
    assert args.tables == {"4-1": md}


def test_parse_args_ignore_figures(ic, tmp_path) -> None:
    """--ignore-figures flag is parsed as list of strings."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = ic.parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1", "--organization", "o", "--repo", "r",
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


def test_main_exits_when_tables_missing(ic, tmp_path) -> None:
    """main() exits early when LRM has tables but --tables not provided."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_WITH_TABLE)
    with (
        patch("implement_clause.parse_subclauses") as mock_ps,
        pytest.raises(SystemExit),
    ):
        ic.main([
            "--lrm", str(lrm), "--clause", "4",
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])
    mock_ps.assert_not_called()


_LRM_WITH_FIGURE = """\
4. Scheduling semantics
Figure 4-1\u2014Overview diagram

4.1 General
General text.

5. Data types
"""


def test_main_exits_when_figures_missing(ic, tmp_path) -> None:
    """main() exits early when LRM has figures but --figures not provided."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_WITH_FIGURE)
    with (
        patch("implement_clause.parse_subclauses") as mock_ps,
        pytest.raises(SystemExit),
    ):
        ic.main([
            "--lrm", str(lrm), "--clause", "4",
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])
    mock_ps.assert_not_called()


def test_main_no_exit_when_figures_ignored(ic, tmp_path) -> None:
    """main() does not exit when missing figures are in --ignore-figures."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_WITH_FIGURE)
    with (
        patch("implement_clause.parse_subclauses", return_value={}) as mock_ps,
        patch("implement_clause.invoke_implement_subclause"),
    ):
        ic.main([
            "--lrm", str(lrm), "--clause", "4",
            "--issue", "1", "--organization", "o", "--repo", "r",
            "--ignore-figures", "4-1",
        ])
    assert mock_ps.called


# --- invoke_implement_subclause forwarding ---


def test_invoke_forwards_tables_to_subclause(
    ic, invoke_subprocess_ok,
) -> None:
    """invoke_implement_subclause forwards --tables in key=path format."""
    args = argparse.Namespace(
        lrm="/path/lrm.txt", issue=123,
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
        lrm="/path/lrm.txt", issue=123,
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


def test_invoke_no_tables_flag_when_empty(
    ic, invoke_subprocess_ok,
) -> None:
    """invoke_implement_subclause omits --tables when no tables to forward."""
    ic.invoke_implement_subclause(_STUB_ARGS, "4.1")
    cmd = invoke_subprocess_ok.call_args[0][0]
    assert "--tables" not in cmd
