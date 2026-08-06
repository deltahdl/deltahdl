"""Tests for lib.python.cli."""

import argparse
from pathlib import Path

import pytest

from lib.python.cli import (
    add_effort_arg,
    add_labels_arg,
    add_lrm_arg,
    add_model_arg,
    add_subclause_arg,
    parse_and_validate,
    parse_and_validate_subclause,
    parse_labels,
    parse_subclauses,
    validate_lrm,
    validate_subclause,
)


# ---- add_lrm_arg ------------------------------------------------------------


def test_add_lrm_arg() -> None:
    """Adds --lrm as a required Path argument."""
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    args = parser.parse_args(["--lrm", "/tmp/lrm.pdf"])
    assert args.lrm == Path("/tmp/lrm.pdf")


# ---- add_model_arg ----------------------------------------------------------


def test_add_model_arg_default() -> None:
    """Defaults --model to opus."""
    parser = argparse.ArgumentParser()
    add_model_arg(parser)
    args = parser.parse_args([])
    assert args.model == "opus"


def test_add_model_arg_custom() -> None:
    """Accepts a custom --model value."""
    parser = argparse.ArgumentParser()
    add_model_arg(parser)
    args = parser.parse_args(["--model", "sonnet"])
    assert args.model == "sonnet"


def test_add_model_arg_with_default_override() -> None:
    """Caller-supplied default replaces the built-in opus default."""
    parser = argparse.ArgumentParser()
    add_model_arg(parser, default="sonnet")
    args = parser.parse_args([])
    assert args.model == "sonnet"


# ---- add_effort_arg ---------------------------------------------------------


def test_add_effort_arg_default() -> None:
    """Defaults --effort to medium."""
    parser = argparse.ArgumentParser()
    add_effort_arg(parser)
    args = parser.parse_args([])
    assert args.effort == "medium"


def test_add_effort_arg_custom() -> None:
    """Accepts a custom --effort value from the allowed set."""
    parser = argparse.ArgumentParser()
    add_effort_arg(parser)
    args = parser.parse_args(["--effort", "high"])
    assert args.effort == "high"


def test_add_effort_arg_rejects_invalid_choice() -> None:
    """Calls parser.error for an --effort value outside the allowed set."""
    parser = argparse.ArgumentParser()
    add_effort_arg(parser)
    with pytest.raises(SystemExit):
        parser.parse_args(["--effort", "extreme"])


# ---- validate_lrm -----------------------------------------------------------


def test_validate_lrm_file_exists(tmp_path: Path) -> None:
    """Returns without error when file exists."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(lrm=lrm)
    validate_lrm(parser, args)
    assert args.lrm == lrm


def test_validate_lrm_file_missing() -> None:
    """Calls parser.error when file does not exist."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(lrm=Path("/nonexistent/lrm.pdf"))
    with pytest.raises(SystemExit):
        validate_lrm(parser, args)


# ---- add_subclause_arg ------------------------------------------------------


def test_add_subclause_arg_value() -> None:
    """Adds --subclause as a required string argument."""
    parser = argparse.ArgumentParser()
    add_subclause_arg(parser)
    args = parser.parse_args(["--subclause", "33.4.1.5"])
    assert args.subclause == "33.4.1.5"


def test_add_subclause_arg_required() -> None:
    """--subclause is required."""
    parser = argparse.ArgumentParser()
    add_subclause_arg(parser)
    with pytest.raises(SystemExit):
        parser.parse_args([])


# ---- validate_subclause -----------------------------------------------------


def test_validate_subclause_accepts_numeric() -> None:
    """Returns without error for a numeric clause string."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(subclause="6.24.1")
    validate_subclause(parser, args)
    assert args.subclause == "6.24.1"


def test_validate_subclause_accepts_annex_subclause() -> None:
    """Returns without error for an annex-letter subclause."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(subclause="B.1")
    validate_subclause(parser, args)
    assert args.subclause == "B.1"


def test_validate_subclause_rejects_lowercase() -> None:
    """Calls parser.error for a lowercase letter clause."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(subclause="b")
    with pytest.raises(SystemExit):
        validate_subclause(parser, args)


def test_validate_subclause_rejects_garbage() -> None:
    """Calls parser.error for a non-clause string."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(subclause="not-a-clause")
    with pytest.raises(SystemExit):
        validate_subclause(parser, args)


def test_validate_subclause_accepts_top_level_numeric() -> None:
    """Returns without error for a clause with no subclauses (e.g. §41)."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(subclause="41")
    validate_subclause(parser, args)
    assert args.subclause == "41"


def test_validate_subclause_accepts_top_level_annex() -> None:
    """Returns without error for a depth-0 annex letter (e.g. leaf Annex B)."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(subclause="B")
    validate_subclause(parser, args)
    assert args.subclause == "B"


# ---- parse_and_validate_subclause -------------------------------------------


def _subclause_parser() -> argparse.ArgumentParser:
    """Build a minimal parser wired up for parse_and_validate_subclause."""
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    add_subclause_arg(parser)
    return parser


def test_parse_and_validate_subclause_returns_namespace(tmp_path: Path) -> None:
    """Returns the parsed namespace when --lrm and --subclause are valid."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = _subclause_parser()
    args = parse_and_validate_subclause(
        parser, ["--lrm", str(lrm), "--subclause", "33.4.1.5"],
    )
    assert args.subclause == "33.4.1.5"


def test_parse_and_validate_subclause_rejects_missing_lrm(
    tmp_path: Path,
) -> None:
    """Errors out when --lrm points at a non-existent file."""
    parser = _subclause_parser()
    with pytest.raises(SystemExit):
        parse_and_validate_subclause(
            parser,
            ["--lrm", str(tmp_path / "no.pdf"), "--subclause", "4.1"],
        )


def test_parse_and_validate_subclause_rejects_bad_subclause(
    tmp_path: Path,
) -> None:
    """Errors out when --subclause is not a valid clause string."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = _subclause_parser()
    with pytest.raises(SystemExit):
        parse_and_validate_subclause(
            parser,
            ["--lrm", str(lrm), "--subclause", "garbage"],
        )


# ---- parse_and_validate ----------------------------------------------------


def test_parse_and_validate_returns_namespace(tmp_path: Path) -> None:
    """Returns a Namespace with parsed and validated args."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    assert parse_and_validate(parser, ["--lrm", str(lrm)]).lrm == lrm


def test_parse_and_validate_rejects_missing_lrm(tmp_path: Path) -> None:
    """Calls parser.error when LRM file does not exist."""
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    with pytest.raises(SystemExit):
        parse_and_validate(parser, ["--lrm", str(tmp_path / "no.pdf")])


# ---- parse_labels ----------------------------------------------------------


def test_parse_labels_single() -> None:
    """Single label returns a one-element list."""
    assert parse_labels("IEEE 1800-2023") == ["IEEE 1800-2023"]


def test_parse_labels_multiple() -> None:
    """Comma-separated labels are split correctly."""
    assert parse_labels("IEEE 1800-2023,IEEE 1800-2020") == [
        "IEEE 1800-2023", "IEEE 1800-2020",
    ]


def test_parse_labels_strips_whitespace() -> None:
    """Whitespace around commas is stripped."""
    assert parse_labels(" IEEE 1800-2023 , IEEE 1800-2020 ") == [
        "IEEE 1800-2023", "IEEE 1800-2020",
    ]


# ---- add_labels_arg --------------------------------------------------------


def test_add_labels_arg() -> None:
    """Adds --labels as a required argument parsed into a list."""
    parser = argparse.ArgumentParser()
    add_labels_arg(parser)
    args = parser.parse_args(["--labels", "IEEE 1800-2023,bug"])
    assert args.labels == ["IEEE 1800-2023", "bug"]


def test_add_labels_arg_required() -> None:
    """--labels is required."""
    parser = argparse.ArgumentParser()
    add_labels_arg(parser)
    with pytest.raises(SystemExit):
        parser.parse_args([])


# ---- parse_subclauses ------------------------------------------------------


def test_parse_subclauses_single() -> None:
    """Single entry returns a one-element list."""
    assert parse_subclauses("33.1") == ["33.1"]


def test_parse_subclauses_multiple() -> None:
    """Comma-separated entries are split into a list."""
    assert parse_subclauses("33.1,33.4,A.5") == ["33.1", "33.4", "A.5"]


def test_parse_subclauses_strips_whitespace() -> None:
    """Whitespace around commas is stripped."""
    assert parse_subclauses(" 33.1 , 33.4 ") == ["33.1", "33.4"]


def test_parse_subclauses_accepts_top_level_entry() -> None:
    """A depth-0 entry (e.g. leaf Annex 'B') is accepted alongside subclauses."""
    assert parse_subclauses("33.1,B") == ["33.1", "B"]


def test_parse_subclauses_rejects_garbage_entry() -> None:
    """A malformed entry raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        parse_subclauses("garbage")


