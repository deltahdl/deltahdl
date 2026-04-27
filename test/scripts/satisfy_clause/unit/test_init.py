"""Unit tests for the satisfy_clause argparse wrapper."""

import runpy
from unittest.mock import patch

import pytest

import satisfy_clause


# --- parse_args ------------------------------------------------------------


def test_parse_args_default_model(make_lrm) -> None:
    """--model defaults to 'opus'."""
    args = satisfy_clause.parse_args([
        "--lrm", str(make_lrm),
        "--clause", "33",
    ])
    assert args.model == "opus"


def test_parse_args_explicit_model(make_lrm) -> None:
    """--model accepts an explicit value."""
    args = satisfy_clause.parse_args([
        "--lrm", str(make_lrm),
        "--clause", "33",
        "--model", "haiku",
    ])
    assert args.model == "haiku"


def test_parse_args_clause_value(make_lrm) -> None:
    """--clause is preserved verbatim."""
    args = satisfy_clause.parse_args([
        "--lrm", str(make_lrm),
        "--clause", "A",
    ])
    assert args.clause == "A"


def test_parse_args_requires_clause(make_lrm) -> None:
    """--clause is required."""
    with pytest.raises(SystemExit):
        satisfy_clause.parse_args(["--lrm", str(make_lrm)])


def test_parse_args_requires_lrm() -> None:
    """--lrm is required."""
    with pytest.raises(SystemExit):
        satisfy_clause.parse_args(["--clause", "33"])


def test_parse_args_rejects_subclause(make_lrm) -> None:
    """A depth-≥1 subclause id is rejected."""
    with pytest.raises(SystemExit):
        satisfy_clause.parse_args([
            "--lrm", str(make_lrm), "--clause", "33.1",
        ])


def test_parse_args_usage_names_package(make_lrm, capsys) -> None:
    """Error usage line names the package, not __main__.py."""
    try:
        satisfy_clause.parse_args([
            "--lrm", str(make_lrm), "--clause", "33.1",
        ])
    except SystemExit:
        pass
    assert capsys.readouterr().err.startswith("usage: satisfy_clause")


# --- main ------------------------------------------------------------------


def test_main_calls_pipeline(make_lrm) -> None:
    """main() forwards the parsed clause into the pipeline."""
    with patch("satisfy_clause.satisfy_clause") as mock_pipeline:
        satisfy_clause.main([
            "--lrm", str(make_lrm),
            "--clause", "33",
        ])
    assert mock_pipeline.call_args[0][0] == "33"


def test_main_passes_model_to_pipeline(make_lrm) -> None:
    """main() forwards the model arg."""
    with patch("satisfy_clause.satisfy_clause") as mock_pipeline:
        satisfy_clause.main([
            "--lrm", str(make_lrm),
            "--clause", "33",
            "--model", "haiku",
        ])
    assert mock_pipeline.call_args[1]["model"] == "haiku"


# --- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_clause", run_name="__main__")
