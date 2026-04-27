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
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "opus"


def test_parse_args_explicit_model(make_lrm) -> None:
    """--model accepts an explicit value."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.4.1.5",
        "--model", "haiku",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "haiku"


def test_parse_args_subclauses_value(make_lrm) -> None:
    """--subclauses is parsed into a list preserving input order."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.1,33.4,A.5",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.subclauses == ["33.1", "33.4", "A.5"]


def test_parse_args_labels_comma_separated(make_lrm) -> None:
    """--labels splits on commas into an ordered list."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.1",
        "--labels", "IEEE 1800-2023,bug",
    ])
    assert args.labels == ["IEEE 1800-2023", "bug"]


def test_parse_args_requires_labels(make_lrm) -> None:
    """--labels is required."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1",
        ])


def test_parse_args_requires_subclauses(make_lrm) -> None:
    """--subclauses is required."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm),
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_requires_lrm() -> None:
    """--lrm is required."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--subclauses", "33.1",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_rejects_top_level_in_list(make_lrm) -> None:
    """A depth-0 entry within --subclauses is rejected at parse time."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1,33",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_usage_names_package(make_lrm, capsys) -> None:
    """Error usage line names the package, not __main__.py."""
    try:
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1,33",
            "--labels", "IEEE 1800-2023",
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
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[0][0] == ["33.1", "33.4"]


def test_main_passes_model_to_pipeline(make_lrm) -> None:
    """main() forwards the model arg."""
    with patch("satisfy_subclauses.satisfy_subclauses") as mock_pipeline:
        satisfy_subclauses.main([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1",
            "--model", "haiku",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[1]["model"] == "haiku"


def test_main_passes_labels_to_pipeline(make_lrm) -> None:
    """main() forwards the parsed labels list to the pipeline."""
    with patch("satisfy_subclauses.satisfy_subclauses") as mock_pipeline:
        satisfy_subclauses.main([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1",
            "--labels", "IEEE 1800-2023,bug",
        ])
    assert mock_pipeline.call_args[1]["labels"] == ["IEEE 1800-2023", "bug"]


# --- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_subclauses", run_name="__main__")
