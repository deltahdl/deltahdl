"""Unit tests for the satisfy_subclauses argparse wrapper."""

import runpy
from unittest.mock import patch

import pytest

import satisfy_subclauses


# --- parse_args ------------------------------------------------------------


def test_parse_args_default_model(make_lrm) -> None:
    """--model defaults to 'opus'."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.4.1.5",
    ])
    assert args.model == "opus"


def test_parse_args_explicit_model(make_lrm) -> None:
    """--model accepts an explicit value."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.4.1.5",
        "--model", "haiku",
    ])
    assert args.model == "haiku"


def test_parse_args_subclauses_value(make_lrm) -> None:
    """--subclauses is parsed into a list preserving input order."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.1,33.4,A.5",
    ])
    assert args.subclauses == ["33.1", "33.4", "A.5"]


def test_parse_args_requires_subclauses(make_lrm) -> None:
    """--subclauses is required."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args(["--lrm", str(make_lrm)])


def test_parse_args_requires_lrm() -> None:
    """--lrm is required."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args(["--subclauses", "33.1"])


def test_parse_args_rejects_top_level_in_list(make_lrm) -> None:
    """A depth-0 entry within --subclauses is rejected at parse time."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm), "--subclauses", "33.1,33",
        ])


def test_parse_args_usage_names_package(make_lrm, capsys) -> None:
    """Error usage line names the package, not __main__.py."""
    try:
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm), "--subclauses", "33.1,33",
        ])
    except SystemExit:
        pass
    assert capsys.readouterr().err.startswith("usage: satisfy_subclauses")


# --- main ------------------------------------------------------------------


def test_main_dispatches_each_entry(make_lrm) -> None:
    """main() forwards the parsed list into the pipeline in input order."""
    with patch("satisfy_subclauses.satisfy_subclauses") as mock_pipeline:
        satisfy_subclauses.main([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1,33.4",
        ])
    assert mock_pipeline.call_args[0][0] == ["33.1", "33.4"]


def test_main_passes_model_to_pipeline(make_lrm) -> None:
    """main() forwards the model arg."""
    with patch("satisfy_subclauses.satisfy_subclauses") as mock_pipeline:
        satisfy_subclauses.main([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1",
            "--model", "haiku",
        ])
    assert mock_pipeline.call_args[1]["model"] == "haiku"


# --- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_subclauses", run_name="__main__")
