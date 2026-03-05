"""Tests for implement_clause core functions."""

import argparse
import subprocess
import sys
from contextlib import contextmanager
from unittest.mock import patch

import pytest

from implement_clause import (
    _lrm_labels_for_clause,
    invoke_implement_subclause,
    main,
    parse_args,
)

_STUB_ARGS = argparse.Namespace(
    lrm="/path/lrm.txt", issue=123,
    organization="deltahdl", repo="deltahdl",
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
    ):
        yield mock_inv


def test_invoke_implement_subclause_calls_subprocess(
    invoke_subprocess_ok,
) -> None:
    """Correct command is passed to subprocess.run."""
    invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert invoke_subprocess_ok.call_args[0][0] == [
        sys.executable, "-m", "implement_subclause",
        "--lrm", "/path/lrm.txt",
        "--subclause", "4.2",
        "--issue", "123",
    ]


@pytest.mark.usefixtures("invoke_subprocess_ok")
def test_invoke_implement_subclause_prints_subclause(capsys) -> None:
    """Prints which subclause is being invoked."""
    invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert "4.2" in capsys.readouterr().out


# --- parse_args ---


def test_parse_args_clause(tmp_path) -> None:
    """--clause flag sets args.clause to the number."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1", "--organization", "o", "--repo", "r",
    ])
    assert args.clause == "4"


def test_parse_args_annex(tmp_path) -> None:
    """--annex flag sets args.annex to the letter."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--annex", "A",
        "--issue", "1", "--organization", "o", "--repo", "r",
    ])
    assert args.annex == "A"


def test_parse_args_clause_and_annex_exclusive(tmp_path) -> None:
    """--clause and --annex are mutually exclusive."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", str(lrm), "--clause", "4", "--annex", "A",
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])


def test_parse_args_missing_lrm() -> None:
    """SystemExit when --lrm points to a nonexistent file."""
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", "/no/such/file", "--clause", "4",
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])


def test_parse_args_issue_is_int(tmp_path) -> None:
    """--issue is parsed as an integer."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "42", "--organization", "o", "--repo", "r",
    ])
    assert args.issue == 42


def test_parse_args_no_clause_or_annex(tmp_path) -> None:
    """SystemExit when neither --clause nor --annex is provided."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", str(lrm),
            "--issue", "1", "--organization", "o", "--repo", "r",
        ])


# --- main ---


def test_main_no_subclauses(clause_argv) -> None:
    """Clause without subclauses invokes implement_subclause directly."""
    with (
        patch("implement_clause.parse_subclauses", return_value={}),
        patch("implement_clause.invoke_implement_subclause") as mock_inv,
    ):
        main(clause_argv)
    assert mock_inv.call_args[0][1] == "4"


def test_main_no_subclauses_prints_leaf(clause_argv, capsys) -> None:
    """Prints that clause has no subclauses."""
    with (
        patch("implement_clause.parse_subclauses", return_value={}),
        patch("implement_clause.invoke_implement_subclause"),
    ):
        main(clause_argv)
    assert "No subclauses" in capsys.readouterr().out


def test_main_with_subclauses(clause_argv) -> None:
    """Next unchecked subclause is passed to implement_subclause."""
    with _patch_main_with_subclauses() as mock_inv:
        main(clause_argv)
    assert mock_inv.call_args[0][1] == "4.2"


def test_main_prints_subclauses_found(clause_argv, capsys) -> None:
    """Prints how many subclauses were discovered."""
    with _patch_main_with_subclauses():
        main(clause_argv)
    assert "Found 2 subclauses" in capsys.readouterr().out


def test_main_prints_synced_body(clause_argv, capsys) -> None:
    """Prints the synced issue body."""
    with _patch_main_with_subclauses(
        synced_body="## Subclauses\n\n- [ ] 4.1 General\n",
        next_sub="4.1",
    ):
        main(clause_argv)
    assert "## Subclauses" in capsys.readouterr().out


def test_main_prints_next_subclause(clause_argv, capsys) -> None:
    """Prints which subclause was picked as next."""
    with _patch_main_with_subclauses():
        main(clause_argv)
    assert "Next unchecked: 4.2" in capsys.readouterr().out


def test_main_all_done(clause_argv, capsys) -> None:
    """Prints all-done message when no unchecked subclauses remain."""
    with _patch_main_with_subclauses(
        subclauses={"4.1": "General"}, next_sub=None,
    ):
        main(clause_argv)
    assert "All subclauses are done" in capsys.readouterr().out


def test_main_annex(tmp_path) -> None:
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
        main(argv)
    assert mock_ps.call_args[0][1] == "A"


# --- invoke_implement_subclause ---


def test_invoke_implement_subclause_failure() -> None:
    """SystemExit on non-zero return code."""
    with patch("implement_clause.subprocess.run") as mock_run:
        mock_run.return_value = subprocess.CompletedProcess(
            args=[], returncode=1,
        )
        with pytest.raises(SystemExit):
            invoke_implement_subclause(_STUB_ARGS, "4.2")


def test_invoke_implement_subclause_passes_continue(
    invoke_subprocess_ok,
) -> None:
    """--continue appears in subprocess command when continue_session=True."""
    invoke_implement_subclause(
        _STUB_ARGS, "4.2", continue_session=True,
    )
    assert "--continue" in invoke_subprocess_ok.call_args[0][0]


def test_invoke_implement_subclause_no_continue_by_default(
    invoke_subprocess_ok,
) -> None:
    """--continue not in subprocess command by default."""
    invoke_implement_subclause(_STUB_ARGS, "4.2")
    assert "--continue" not in invoke_subprocess_ok.call_args[0][0]


# --- main loop ---


def test_main_loops_all_subclauses(clause_argv) -> None:
    """main invokes implement_subclause for each unchecked subclause."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", "4.2", None],
    ) as mock_inv:
        main(clause_argv)
    assert mock_inv.call_count == 2


def test_main_first_subclause_no_continue(clause_argv) -> None:
    """First invocation does not pass continue_session=True."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", None],
    ) as mock_inv:
        main(clause_argv)
    assert mock_inv.call_args_list[0].kwargs.get("continue_session") is not True


def test_main_second_subclause_uses_continue(clause_argv) -> None:
    """Second invocation passes continue_session=True."""
    with _patch_main_with_subclauses(
        next_sub=["4.1", "4.2", None],
    ) as mock_inv:
        main(clause_argv)
    assert mock_inv.call_args_list[1].kwargs["continue_session"] is True


# --- _lrm_labels_for_clause (whole-clause) ---


_LRM_CLAUSE_WITH_TABLE = """\
List of figures
Figure 4-1\u2014Event scheduling regions

List of tables
Table 4-1\u2014PLI callbacks
"""


def test_lrm_labels_for_clause_finds_figures(tmp_path) -> None:
    """Finds figure labels for a clause."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_CLAUSE_WITH_TABLE)
    figs, _ = _lrm_labels_for_clause(lrm, "4")
    assert figs == ["4-1"]


def test_lrm_labels_for_clause_finds_tables(tmp_path) -> None:
    """Finds table labels for a clause."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(_LRM_CLAUSE_WITH_TABLE)
    _, tbls = _lrm_labels_for_clause(lrm, "4")
    assert tbls == ["4-1"]


def test_lrm_labels_for_clause_empty_figures(tmp_path) -> None:
    """Returns empty figure list when no labels exist."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("No figures or tables here.\n")
    figs, _ = _lrm_labels_for_clause(lrm, "99")
    assert figs == []


def test_lrm_labels_for_clause_empty_tables(tmp_path) -> None:
    """Returns empty table list when no labels exist."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("No figures or tables here.\n")
    _, tbls = _lrm_labels_for_clause(lrm, "99")
    assert tbls == []


def test_lrm_labels_for_clause_ignores_other_clause_figures(tmp_path) -> None:
    """Does not pick up figure labels from other clauses."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(
        "Figure 5-1\u2014Something\n"
        "Table 5-1\u2014Other\n"
    )
    figs, _ = _lrm_labels_for_clause(lrm, "4")
    assert figs == []


def test_lrm_labels_for_clause_ignores_other_clause_tables(tmp_path) -> None:
    """Does not pick up table labels from other clauses."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text(
        "Figure 5-1\u2014Something\n"
        "Table 5-1\u2014Other\n"
    )
    _, tbls = _lrm_labels_for_clause(lrm, "4")
    assert tbls == []


# --- parse_args supplementary flags ---


def test_parse_args_figures(tmp_path) -> None:
    """--figures flag is parsed as list of Paths."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    gv = tmp_path / "Figure_4_1.gv"
    gv.write_text("digraph {}")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1", "--organization", "o", "--repo", "r",
        "--figures", str(gv),
    ])
    assert len(args.figures) == 1


def test_parse_args_tables(tmp_path) -> None:
    """--tables flag is parsed as list of Paths."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    md = tmp_path / "TABLE_4_1.md"
    md.write_text("| col |\n")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1", "--organization", "o", "--repo", "r",
        "--tables", str(md),
    ])
    assert len(args.tables) == 1


def test_parse_args_ignore_figures(tmp_path) -> None:
    """--ignore-figures flag is parsed as list of strings."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "4",
        "--issue", "1", "--organization", "o", "--repo", "r",
        "--ignore-figures", "4-1,4-2",
    ])
    assert args.ignore_figures == ["4-1", "4-2"]
