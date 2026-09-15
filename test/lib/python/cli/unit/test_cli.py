"""Tests for lib.python.cli."""

import argparse
from pathlib import Path

import pytest

from lib.python.cli import (
    add_effort_arg,
    add_lrm_arg,
    add_model_arg,
    parse_and_validate,
    validate_lrm,
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
