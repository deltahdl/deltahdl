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
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "opus"


def test_parse_args_explicit_model(make_lrm) -> None:
    """--model accepts an explicit value."""
    args = satisfy_clauses.parse_args([
        "--lrm", str(make_lrm),
        "--clauses", "33",
        "--model", "haiku",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "haiku"


def test_parse_args_clauses_value(make_lrm) -> None:
    """--clauses is parsed into a list preserving input order."""
    args = satisfy_clauses.parse_args([
        "--lrm", str(make_lrm),
        "--clauses", "32,33,A",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.clauses == ["32", "33", "A"]


def test_parse_args_labels_comma_separated(make_lrm) -> None:
    """--labels splits on commas into an ordered list."""
    args = satisfy_clauses.parse_args([
        "--lrm", str(make_lrm),
        "--clauses", "33",
        "--labels", "IEEE 1800-2023,bug",
    ])
    assert args.labels == ["IEEE 1800-2023", "bug"]


def test_parse_args_requires_labels(make_lrm) -> None:
    """--labels is required."""
    with pytest.raises(SystemExit):
        satisfy_clauses.parse_args([
            "--lrm", str(make_lrm),
            "--clauses", "33",
        ])


def test_parse_args_requires_clauses(make_lrm) -> None:
    """--clauses is required."""
    with pytest.raises(SystemExit):
        satisfy_clauses.parse_args([
            "--lrm", str(make_lrm),
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_requires_lrm() -> None:
    """--lrm is required."""
    with pytest.raises(SystemExit):
        satisfy_clauses.parse_args([
            "--clauses", "33",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_rejects_subclause_in_list(make_lrm) -> None:
    """A depth-≥1 entry within --clauses is rejected at parse time."""
    with pytest.raises(SystemExit):
        satisfy_clauses.parse_args([
            "--lrm", str(make_lrm),
            "--clauses", "33,33.1",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_usage_names_package(make_lrm, capsys) -> None:
    """Error usage line names the package, not __main__.py."""
    try:
        satisfy_clauses.parse_args([
            "--lrm", str(make_lrm),
            "--clauses", "33,33.1",
            "--labels", "IEEE 1800-2023",
        ])
    except SystemExit:
        pass
    assert capsys.readouterr().err.startswith("usage: satisfy_clauses")


# --- main ------------------------------------------------------------------


def test_main_dispatches_each_entry(make_lrm) -> None:
    """main() forwards the parsed list into the pipeline in input order."""
    with patch("satisfy_clauses.satisfy_clauses") as mock_pipeline:
        satisfy_clauses.main([
            "--lrm", str(make_lrm),
            "--clauses", "32,33",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[0][0] == ["32", "33"]


def test_main_passes_model_to_pipeline(make_lrm) -> None:
    """main() forwards the model arg."""
    with patch("satisfy_clauses.satisfy_clauses") as mock_pipeline:
        satisfy_clauses.main([
            "--lrm", str(make_lrm),
            "--clauses", "33",
            "--model", "haiku",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[1]["model"] == "haiku"


def test_main_passes_labels_to_pipeline(make_lrm) -> None:
    """main() forwards the parsed labels list to the pipeline."""
    with patch("satisfy_clauses.satisfy_clauses") as mock_pipeline:
        satisfy_clauses.main([
            "--lrm", str(make_lrm),
            "--clauses", "33",
            "--labels", "IEEE 1800-2023,bug",
        ])
    assert mock_pipeline.call_args[1]["labels"] == ["IEEE 1800-2023", "bug"]


# --- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_clauses", run_name="__main__")
