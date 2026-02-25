"""Unit tests for implement_clause.__init__ (arg parsing and dispatch)."""

import pytest

from implement_clause import clause_depth, parse_args


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
        parse_args(["--lrm", str(lrm), "--clause", "4.1"])


def test_parse_args_accepts_issue(tmp_path):
    """--issue is parsed as int."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args(["--lrm", str(lrm), "--clause", "4.1", "--issue", "8"])
    assert args.issue == 8


def test_parse_args_model_default(tmp_path):
    """--model defaults to 'sonnet'."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "4.1", "--issue", "8",
    ])
    assert args.model == "sonnet"


def test_parse_args_model_override(tmp_path):
    """--model can be overridden."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "4.1", "--issue", "8",
        "--model", "opus",
    ])
    assert args.model == "opus"


def test_parse_args_rejects_bad_clause(tmp_path):
    """Invalid clause format exits."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", str(lrm), "--clause", "bad", "--issue", "8",
        ])


def test_parse_args_rejects_missing_lrm(tmp_path):
    """Non-existent LRM file exits."""
    with pytest.raises(SystemExit):
        parse_args([
            "--lrm", str(tmp_path / "no.txt"), "--clause", "4.1",
            "--issue", "8",
        ])


def test_parse_args_accepts_annex_clause(tmp_path):
    """Uppercase letter clause is accepted."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    args = parse_args([
        "--lrm", str(lrm), "--clause", "B", "--issue", "44",
    ])
    assert (args.clause, args.issue) == ("B", 44)
