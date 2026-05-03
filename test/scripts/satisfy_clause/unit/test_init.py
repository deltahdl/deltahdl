"""Unit tests for the satisfy_clause argparse wrapper."""

import runpy
from pathlib import Path
from unittest.mock import patch

import pytest

import satisfy_clause


# --- parse_args ------------------------------------------------------------


def test_parse_args_default_model(make_lrm: Path) -> None:
    """--model defaults to 'opus'."""
    args = satisfy_clause.parse_args([
        "--lrm", str(make_lrm),
        "--clause", "33",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "opus"


def test_parse_args_explicit_model(make_lrm: Path) -> None:
    """--model accepts an explicit value."""
    args = satisfy_clause.parse_args([
        "--lrm", str(make_lrm),
        "--clause", "33",
        "--model", "haiku",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "haiku"


def test_parse_args_clause_value(make_lrm: Path) -> None:
    """--clause is preserved verbatim."""
    args = satisfy_clause.parse_args([
        "--lrm", str(make_lrm),
        "--clause", "A",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.clause == "A"


def test_parse_args_labels_comma_separated(make_lrm: Path) -> None:
    """--labels splits on commas into an ordered list."""
    args = satisfy_clause.parse_args([
        "--lrm", str(make_lrm),
        "--clause", "33",
        "--labels", "IEEE 1800-2023,bug",
    ])
    assert args.labels == ["IEEE 1800-2023", "bug"]


def test_parse_args_requires_labels(make_lrm: Path) -> None:
    """--labels is required."""
    with pytest.raises(SystemExit):
        satisfy_clause.parse_args([
            "--lrm", str(make_lrm),
            "--clause", "33",
        ])


def test_parse_args_requires_clause(make_lrm: Path) -> None:
    """--clause is required."""
    with pytest.raises(SystemExit):
        satisfy_clause.parse_args([
            "--lrm", str(make_lrm),
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_requires_lrm() -> None:
    """--lrm is required."""
    with pytest.raises(SystemExit):
        satisfy_clause.parse_args([
            "--clause", "33",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_rejects_subclause(make_lrm: Path) -> None:
    """A depth-≥1 subclause id is rejected."""
    with pytest.raises(SystemExit):
        satisfy_clause.parse_args([
            "--lrm", str(make_lrm),
            "--clause", "33.1",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_usage_names_package(
    make_lrm: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """Error usage line names the package, not __main__.py."""
    try:
        satisfy_clause.parse_args([
            "--lrm", str(make_lrm),
            "--clause", "33.1",
            "--labels", "IEEE 1800-2023",
        ])
    except SystemExit:
        pass
    assert capsys.readouterr().err.startswith("usage: satisfy_clause")


# --- main ------------------------------------------------------------------


def test_main_calls_pipeline(make_lrm: Path) -> None:
    """main() forwards the parsed clause into the pipeline."""
    with patch("satisfy_clause.satisfy_clause") as mock_pipeline:
        satisfy_clause.main([
            "--lrm", str(make_lrm),
            "--clause", "33",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[0][0] == "33"


def test_main_passes_model_to_pipeline(make_lrm: Path) -> None:
    """main() forwards the model arg."""
    with patch("satisfy_clause.satisfy_clause") as mock_pipeline:
        satisfy_clause.main([
            "--lrm", str(make_lrm),
            "--clause", "33",
            "--model", "haiku",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[1]["model"] == "haiku"


def test_main_passes_labels_to_pipeline(make_lrm: Path) -> None:
    """main() forwards the parsed labels list to the pipeline."""
    with patch("satisfy_clause.satisfy_clause") as mock_pipeline:
        satisfy_clause.main([
            "--lrm", str(make_lrm),
            "--clause", "33",
            "--labels", "IEEE 1800-2023,bug",
        ])
    assert mock_pipeline.call_args[1]["labels"] == ["IEEE 1800-2023", "bug"]


# --- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_clause", run_name="__main__")
