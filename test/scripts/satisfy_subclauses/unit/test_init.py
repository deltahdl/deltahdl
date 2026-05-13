"""Unit tests for the satisfy_subclauses argparse wrapper."""

import runpy
from pathlib import Path
from typing import Any
from unittest.mock import patch

import pytest

import satisfy_subclauses


# --- parse_args ------------------------------------------------------------


def test_parse_args_default_model(make_lrm: Path) -> None:
    """--model defaults to 'opus'."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.4.1.5",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "opus"


def test_parse_args_explicit_model(make_lrm: Path) -> None:
    """--model accepts an explicit value."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.4.1.5",
        "--model", "haiku",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.model == "haiku"


def test_parse_args_subclauses_value(make_lrm: Path) -> None:
    """--subclauses is parsed into a list preserving input order."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.1,33.4,A.5",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.subclauses == ["33.1", "33.4", "A.5"]


def test_parse_args_labels_comma_separated(make_lrm: Path) -> None:
    """--labels splits on commas into an ordered list."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.1",
        "--labels", "IEEE 1800-2023,bug",
    ])
    assert args.labels == ["IEEE 1800-2023", "bug"]


def test_parse_args_requires_labels(make_lrm: Path) -> None:
    """--labels is required."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1",
        ])


def test_parse_args_requires_one_of_subclauses_or_issue(make_lrm: Path) -> None:
    """At least one of --subclauses or --issue is required."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm),
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_rejects_both_subclauses_and_issue(make_lrm: Path) -> None:
    """--subclauses and --issue are mutually exclusive."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1",
            "--issue", "1",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_issue_value_int(make_lrm: Path) -> None:
    """--issue parses as an int and --subclauses stays unset."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--issue", "1",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.issue == 1 and args.subclauses is None


def test_parse_args_subclauses_mode_leaves_issue_unset(make_lrm: Path) -> None:
    """--subclauses mode leaves args.issue as None."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.1",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.issue is None


def test_parse_args_issue_must_be_int(make_lrm: Path) -> None:
    """--issue value must parse as int."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm),
            "--issue", "foo",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_requires_lrm() -> None:
    """--lrm is required."""
    with pytest.raises(SystemExit):
        satisfy_subclauses.parse_args([
            "--subclauses", "33.1",
            "--labels", "IEEE 1800-2023",
        ])


def test_parse_args_accepts_top_level_in_list(make_lrm: Path) -> None:
    """A depth-0 entry within --subclauses is accepted (e.g. leaf Annex B)."""
    args = satisfy_subclauses.parse_args([
        "--lrm", str(make_lrm),
        "--subclauses", "33.1,B",
        "--labels", "IEEE 1800-2023",
    ])
    assert args.subclauses == ["33.1", "B"]


def test_parse_args_usage_names_package(
    make_lrm: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """Error usage line names the package, not __main__.py."""
    try:
        satisfy_subclauses.parse_args([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1,garbage",
            "--labels", "IEEE 1800-2023",
        ])
    except SystemExit:
        pass
    assert capsys.readouterr().err.startswith("usage: satisfy_subclauses")


# --- main ------------------------------------------------------------------


def test_main_dispatches_each_entry(make_lrm: Path) -> None:
    """main() forwards the parsed list into the pipeline in input order."""
    with patch("satisfy_subclauses.satisfy_subclauses") as mock_pipeline:
        satisfy_subclauses.main([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1,33.4",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[0][0] == ["33.1", "33.4"]


def test_main_passes_model_to_pipeline(make_lrm: Path) -> None:
    """main() forwards the model arg."""
    with patch("satisfy_subclauses.satisfy_subclauses") as mock_pipeline:
        satisfy_subclauses.main([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1",
            "--model", "haiku",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_pipeline.call_args[1]["model"] == "haiku"


def test_main_passes_labels_to_pipeline(make_lrm: Path) -> None:
    """main() forwards the parsed labels list to the pipeline."""
    with patch("satisfy_subclauses.satisfy_subclauses") as mock_pipeline:
        satisfy_subclauses.main([
            "--lrm", str(make_lrm),
            "--subclauses", "33.1",
            "--labels", "IEEE 1800-2023,bug",
        ])
    assert mock_pipeline.call_args[1]["labels"] == ["IEEE 1800-2023", "bug"]


def test_main_issue_mode_dispatches_via_from_issue(make_lrm: Path) -> None:
    """main() with --issue routes through satisfy_subclauses_from_issue."""
    with patch(
        "satisfy_subclauses.satisfy_subclauses_from_issue",
    ) as mock_from_issue:
        satisfy_subclauses.main([
            "--lrm", str(make_lrm),
            "--issue", "1",
            "--labels", "IEEE 1800-2023",
        ])
    assert mock_from_issue.call_args[0][0] == 1


def _capture_from_issue_call(make_lrm: Path) -> Any:
    """Run main() with --issue and return the captured call object."""
    with patch(
        "satisfy_subclauses.satisfy_subclauses_from_issue",
    ) as mock_from_issue:
        satisfy_subclauses.main([
            "--lrm", str(make_lrm),
            "--issue", "1",
            "--model", "haiku",
            "--labels", "IEEE 1800-2023,bug",
        ])
    return mock_from_issue.call_args


def test_main_issue_mode_forwards_lrm(make_lrm: Path) -> None:
    """main() with --issue forwards the resolved --lrm path."""
    call = _capture_from_issue_call(make_lrm)
    assert call[0][1] == str(make_lrm)


def test_main_issue_mode_forwards_model(make_lrm: Path) -> None:
    """main() with --issue forwards the --model value."""
    call = _capture_from_issue_call(make_lrm)
    assert call[1]["model"] == "haiku"


def test_main_issue_mode_forwards_labels(make_lrm: Path) -> None:
    """main() with --issue forwards the parsed labels list."""
    call = _capture_from_issue_call(make_lrm)
    assert call[1]["labels"] == ["IEEE 1800-2023", "bug"]


def test_main_subclauses_mode_does_not_call_from_issue(make_lrm: Path) -> None:
    """main() with --subclauses does not invoke the --issue entry point."""
    with patch(
        "satisfy_subclauses.satisfy_subclauses_from_issue",
    ) as mock_from_issue:
        with patch("satisfy_subclauses.satisfy_subclauses"):
            satisfy_subclauses.main([
                "--lrm", str(make_lrm),
                "--subclauses", "33.1",
                "--labels", "IEEE 1800-2023",
            ])
    assert not mock_from_issue.called


# --- __main__ guard --------------------------------------------------------


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("satisfy_subclauses", run_name="__main__")
