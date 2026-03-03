"""Unit tests for implement_subclause (arg parsing and dispatch)."""

import runpy
from unittest.mock import patch

import pytest

from implement_subclause import clause_depth, main, parse_args


# ---- clause_depth -----------------------------------------------------------


def test_clause_depth_1():
    """Single component has depth 1."""
    assert clause_depth("4") == 1


def test_clause_depth_1_annex():
    """Single letter component has depth 1."""
    assert clause_depth("B") == 1


def test_clause_depth_2():
    """Two components have depth 2."""
    assert clause_depth("4.1") == 2


def test_clause_depth_3():
    """Three components have depth 3."""
    assert clause_depth("6.24.1") == 3


def test_clause_depth_4():
    """Four components have depth 4."""
    assert clause_depth("4.4.3.1") == 4


def test_clause_depth_5():
    """Five components have depth 5."""
    assert clause_depth("4.4.3.1.2") == 5


# ---- parse_args -------------------------------------------------------------


def test_parse_args_requires_issue(tmp_path):
    """--issue is required; omitting it exits."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        parse_args(["--lrm", str(lrm), "--subclause", "4.1"])


def test_parse_args_accepts_issue(tmp_path):
    """--issue is parsed as int."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args(["--lrm", str(lrm), "--subclause", "4.1", "--issue", "8"])
    assert args.issue == 8


def test_parse_args_model_default(tmp_path):
    """--model defaults to 'opus'."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
    ])
    assert args.model == "opus"


def test_parse_args_model_override(tmp_path):
    """--model can be overridden."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
        "--model", "opus",
    ])
    assert args.model == "opus"


def test_parse_args_rejects_bad_clause(tmp_path):
    """Invalid clause format exits."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", str(lrm), "--subclause", "bad", "--issue", "8",
        ])


def test_parse_args_rejects_missing_lrm(tmp_path):
    """Non-existent LRM file exits."""
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", str(tmp_path / "no.txt"), "--subclause", "4.1",
            "--issue", "8",
        ])


def test_parse_args_accepts_annex_clause(tmp_path):
    """Uppercase letter clause is accepted."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--subclause", "B", "--issue", "44",
    ])
    assert (args.subclause, args.issue) == ("B", 44)


def test_parse_args_overviews_default(tmp_path):
    """--overviews defaults to empty list."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
    ])
    assert args.overviews == []


def test_parse_args_overviews_single(tmp_path):
    """--overviews with a single value is parsed into a one-element list."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
        "--overviews", "4.1",
    ])
    assert args.overviews == ["4.1"]


def test_parse_args_overviews_multiple(tmp_path):
    """--overviews with comma-separated values is parsed into a list."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--subclause", "4.4.3.1", "--issue", "6",
        "--overviews", "4.1,4.4",
    ])
    assert args.overviews == ["4.1", "4.4"]


# ---- main ------------------------------------------------------------------


@patch("implement_subclause.run_prompt")
@patch("implement_subclause.check_supplementary_args")
def test_main_dispatches_depth_1(_mock_check, mock_run, tmp_path):
    """main() dispatches depth-1 clause to prompt_v handler."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    main(["--lrm", str(lrm), "--subclause", "4", "--issue", "6", "--model", "opus"])
    assert mock_run.call_args[1]["model"] == "opus"


@patch("implement_subclause.run_prompt")
@patch("implement_subclause.check_supplementary_args")
def test_main_passes_overviews(_mock_check, mock_run, tmp_path):
    """main() includes overview lines in the supplementary string."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    main([
        "--lrm", str(lrm), "--subclause", "4.1", "--issue", "8",
        "--overviews", "4.1,4.4",
    ])
    supp = mock_run.call_args[0][0].keywords["supplementary"]
    assert "Thoroughly understand 4.1" in supp


@patch("implement_subclause.run_prompt")
@patch("implement_subclause.check_supplementary_args")
def test_main_with_figures(_mock_check, mock_run, tmp_path):
    """main() builds supplementary string when --figures is provided."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    gv = tmp_path / "Figure_4_1.gv"
    gv.write_text("digraph {}")
    main([
        "--lrm", str(lrm), "--subclause", "4", "--issue", "6",
        "--figures", str(gv),
    ])
    assert "Figure 4-1" in mock_run.call_args[0][0].keywords["supplementary"]


# ---- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main():
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("implement_subclause", run_name="__main__")
