"""Unit tests for the satisfy_clauses argparse wrapper."""

import runpy
from unittest.mock import patch

import pytest

import satisfy_clauses


# --- parse_args ------------------------------------------------------------


def test_parse_args_default_model(make_lrm) -> None:
    """--model defaults to 'opus'."""
    args = satisfy_clauses.parse_args([
        "--lrm", str(make_lrm),
        "--clauses", "33",
    ])
    assert args.model == "opus"


def test_parse_args_explicit_model(make_lrm) -> None:
    """--model accepts an explicit value."""
    args = satisfy_clauses.parse_args([
        "--lrm", str(make_lrm),
        "--clauses", "33",
        "--model", "haiku",
    ])
    assert args.model == "haiku"


def test_parse_args_clauses_value(make_lrm) -> None:
    """--clauses is parsed into a list preserving input order."""
    args = satisfy_clauses.parse_args([
        "--lrm", str(make_lrm),
        "--clauses", "32,33,A",
    ])
    assert args.clauses == ["32", "33", "A"]


def test_parse_args_requires_clauses(make_lrm) -> None:
    """--clauses is required."""
    with pytest.raises(SystemExit):
        satisfy_clauses.parse_args(["--lrm", str(make_lrm)])


def test_parse_args_requires_lrm() -> None:
    """--lrm is required."""
    with pytest.raises(SystemExit):
        satisfy_clauses.parse_args(["--clauses", "33"])


def test_parse_args_rejects_subclause_in_list(make_lrm) -> None:
    """A depth-≥1 entry within --clauses is rejected at parse time."""
    with pytest.raises(SystemExit):
        satisfy_clauses.parse_args([
            "--lrm", str(make_lrm), "--clauses", "33,33.1",
        ])


# --- main ------------------------------------------------------------------


def test_main_dispatches_each_entry(make_lrm) -> None:
    """main() forwards the parsed list into the pipeline in input order."""
    with patch("satisfy_clauses.satisfy_clauses") as mock_pipeline:
        satisfy_clauses.main([
            "--lrm", str(make_lrm),
            "--clauses", "32,33",
        ])
    assert mock_pipeline.call_args[0][0] == ["32", "33"]


def test_main_passes_model_to_pipeline(make_lrm) -> None:
    """main() forwards the model arg."""
    with patch("satisfy_clauses.satisfy_clauses") as mock_pipeline:
        satisfy_clauses.main([
            "--lrm", str(make_lrm),
            "--clauses", "33",
            "--model", "haiku",
        ])
    assert mock_pipeline.call_args[1]["model"] == "haiku"


# --- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_clauses", run_name="__main__")
