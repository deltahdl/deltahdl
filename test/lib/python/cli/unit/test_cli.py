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


def test_add_lrm_arg() -> None:
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    args = parser.parse_args(["--lrm", "/tmp/lrm.pdf"])
    assert args.lrm == Path("/tmp/lrm.pdf")


def test_add_model_arg_default() -> None:
    parser = argparse.ArgumentParser()
    add_model_arg(parser)
    args = parser.parse_args([])
    assert args.model == "opus"


def test_add_model_arg_custom() -> None:
    parser = argparse.ArgumentParser()
    add_model_arg(parser)
    args = parser.parse_args(["--model", "sonnet"])
    assert args.model == "sonnet"


def test_add_model_arg_with_default_override() -> None:
    parser = argparse.ArgumentParser()
    add_model_arg(parser, default="sonnet")
    args = parser.parse_args([])
    assert args.model == "sonnet"


def test_add_effort_arg_default() -> None:
    parser = argparse.ArgumentParser()
    add_effort_arg(parser)
    args = parser.parse_args([])
    assert args.effort == "medium"


def test_add_effort_arg_custom() -> None:
    parser = argparse.ArgumentParser()
    add_effort_arg(parser)
    args = parser.parse_args(["--effort", "high"])
    assert args.effort == "high"


def test_add_effort_arg_rejects_invalid_choice() -> None:
    parser = argparse.ArgumentParser()
    add_effort_arg(parser)
    with pytest.raises(SystemExit):
        parser.parse_args(["--effort", "extreme"])


def test_validate_lrm_file_exists(tmp_path: Path) -> None:
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(lrm=lrm)
    validate_lrm(parser, args)
    assert args.lrm == lrm


def test_validate_lrm_file_missing() -> None:
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(lrm=Path("/nonexistent/lrm.pdf"))
    with pytest.raises(SystemExit):
        validate_lrm(parser, args)


def test_parse_and_validate_returns_namespace(tmp_path: Path) -> None:
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    assert parse_and_validate(parser, ["--lrm", str(lrm)]).lrm == lrm


def test_parse_and_validate_rejects_missing_lrm(tmp_path: Path) -> None:
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    with pytest.raises(SystemExit):
        parse_and_validate(parser, ["--lrm", str(tmp_path / "no.pdf")])
