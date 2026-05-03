"""Unit tests for the satisfy_subclause argparse wrapper."""

import runpy
from pathlib import Path
from unittest.mock import patch

import pytest

import satisfy_subclause


# --- parse_args ------------------------------------------------------------


def test_parse_args_default_model(make_lrm: Path) -> None:
    """--model defaults to 'opus'."""
    args = satisfy_subclause.parse_args([
        "--lrm", str(make_lrm),
        "--subclause", "33.4.1.5",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "opus"


def test_parse_args_explicit_model(make_lrm: Path) -> None:
    """--model accepts an explicit value."""
    args = satisfy_subclause.parse_args([
        "--lrm", str(make_lrm),
        "--subclause", "33.4.1.5",
        "--model", "haiku",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "haiku"


def test_parse_args_subclause_value(make_lrm: Path) -> None:
    """--subclause is preserved verbatim."""
    args = satisfy_subclause.parse_args([
        "--lrm", str(make_lrm),
        "--subclause", "33.4.1.5",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.subclause == "33.4.1.5"


def test_parse_args_labels_single_value(make_lrm: Path) -> None:
    """--labels accepts a single label and parses it into a one-element list."""
    args = satisfy_subclause.parse_args([
        "--lrm", str(make_lrm),
        "--subclause", "33.4.1.5",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.labels == ["IEEE 1800-2023"]


def test_parse_args_labels_comma_separated(make_lrm: Path) -> None:
    """--labels splits on commas into an ordered list."""
    args = satisfy_subclause.parse_args([
        "--lrm", str(make_lrm),
        "--subclause", "33.4.1.5",
        "--labels", "IEEE 1800-2023,bug",
    ])
    assert args.labels == ["IEEE 1800-2023", "bug"]


def test_parse_args_requires_labels(make_lrm: Path) -> None:
    """--labels is required."""
    with pytest.raises(SystemExit):
        satisfy_subclause.parse_args([
            "--lrm", str(make_lrm),
            "--subclause", "33.4.1.5",
        ])


def test_parse_args_requires_subclause(make_lrm: Path) -> None:
    """--subclause is required."""
    with pytest.raises(SystemExit):
        satisfy_subclause.parse_args([
            "--lrm", str(make_lrm),
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_requires_lrm() -> None:
    """--lrm is required."""
    with pytest.raises(SystemExit):
        satisfy_subclause.parse_args([
            "--subclause", "4.1",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_rejects_bad_subclause(make_lrm: Path) -> None:
    """An invalid clause string is rejected."""
    with pytest.raises(SystemExit):
        satisfy_subclause.parse_args([
            "--lrm", str(make_lrm),
            "--subclause", "bad",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_usage_names_package(
    make_lrm: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """Error usage line names the package, not __main__.py."""
    try:
        satisfy_subclause.parse_args([
            "--lrm", str(make_lrm),
            "--subclause", "bad",
            "--labels", "IEEE 1800-2023",
        ])
    except SystemExit:
        pass
    assert capsys.readouterr().err.startswith("usage: satisfy_subclause")


# --- main ------------------------------------------------------------------


def test_main_calls_satisfy_subclause(make_lrm: Path) -> None:
    """main() forwards to pipeline.satisfy_subclause."""
    with patch("satisfy_subclause.satisfy_subclause") as mock_pipeline:
        satisfy_subclause.main([
            "--lrm", str(make_lrm),
            "--subclause", "33.4.1.5",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.called


def test_main_passes_subclause_to_pipeline(make_lrm: Path) -> None:
    """main() forwards the subclause arg."""
    with patch("satisfy_subclause.satisfy_subclause") as mock_pipeline:
        satisfy_subclause.main([
            "--lrm", str(make_lrm),
            "--subclause", "33.4.1.5",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[0][0] == "33.4.1.5"


def test_main_passes_model_to_pipeline(make_lrm: Path) -> None:
    """main() forwards the model arg."""
    with patch("satisfy_subclause.satisfy_subclause") as mock_pipeline:
        satisfy_subclause.main([
            "--lrm", str(make_lrm),
            "--subclause", "33.4.1.5",
            "--model", "haiku",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[1]["model"] == "haiku"


def test_main_passes_labels_to_pipeline(make_lrm: Path) -> None:
    """main() forwards the parsed labels list to the pipeline."""
    with patch("satisfy_subclause.satisfy_subclause") as mock_pipeline:
        satisfy_subclause.main([
            "--lrm", str(make_lrm),
            "--subclause", "33.4.1.5",
            "--labels", "IEEE 1800-2023,bug",
        ])
    assert mock_pipeline.call_args[1]["labels"] == ["IEEE 1800-2023", "bug"]


# --- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_subclause", run_name="__main__")
