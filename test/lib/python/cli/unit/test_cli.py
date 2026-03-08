"""Tests for lib.python.cli."""

import argparse
import sys
from pathlib import Path

import pytest

from lib.python.cli import (
    add_continue_arg,
    add_lrm_arg,
    add_model_arg,
    invoke_implement_subclause,
    validate_lrm,
)
from lib.python.test_fixtures.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
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


# ---- add_continue_arg -------------------------------------------------------


def test_add_continue_arg_default() -> None:
    """Defaults --continue to False with dest=continue_session."""
    parser = argparse.ArgumentParser()
    add_continue_arg(parser)
    args = parser.parse_args([])
    assert args.continue_session is False


def test_add_continue_arg_set() -> None:
    """Sets continue_session to True when --continue is passed."""
    parser = argparse.ArgumentParser()
    add_continue_arg(parser)
    args = parser.parse_args(["--continue"])
    assert args.continue_session is True


# ---- validate_lrm -----------------------------------------------------------


def test_validate_lrm_file_exists(tmp_path) -> None:
    """Returns without error when file exists."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(lrm=lrm)
    assert validate_lrm(parser, args) is None


def test_validate_lrm_file_missing() -> None:
    """Calls parser.error when file does not exist."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(lrm=Path("/nonexistent/lrm.pdf"))
    with pytest.raises(SystemExit):
        validate_lrm(parser, args)


# ---- invoke_implement_subclause ---------------------------------------------


def _invoke_and_capture(monkeypatch, *, continue_session=False):
    """Invoke with stubbed subprocess and return captured command."""
    captured = stub_subprocess_success(monkeypatch)
    invoke_implement_subclause(
        lrm="/tmp/lrm.pdf",
        subclause="6.1",
        issue=42,
        model="opus",
        continue_session=continue_session,
    )
    return captured[0]


def test_invoke_implement_subclause_calls_python(monkeypatch) -> None:
    """Invokes the current Python interpreter."""
    assert _invoke_and_capture(monkeypatch)[0] == sys.executable


def test_invoke_implement_subclause_module(monkeypatch) -> None:
    """Passes -m implement_subclause."""
    assert _invoke_and_capture(monkeypatch)[1:3] == ["-m", "implement_subclause"]


def test_invoke_implement_subclause_lrm(monkeypatch) -> None:
    """Passes --lrm with correct value."""
    cmd = _invoke_and_capture(monkeypatch)
    assert cmd[cmd.index("--lrm") + 1] == "/tmp/lrm.pdf"


def test_invoke_implement_subclause_subclause(monkeypatch) -> None:
    """Passes --subclause with correct value."""
    cmd = _invoke_and_capture(monkeypatch)
    assert cmd[cmd.index("--subclause") + 1] == "6.1"


def test_invoke_implement_subclause_issue(monkeypatch) -> None:
    """Passes --issue as string."""
    cmd = _invoke_and_capture(monkeypatch)
    assert cmd[cmd.index("--issue") + 1] == "42"


def test_invoke_implement_subclause_model(monkeypatch) -> None:
    """Passes --model with correct value."""
    cmd = _invoke_and_capture(monkeypatch)
    assert cmd[cmd.index("--model") + 1] == "opus"


def test_invoke_implement_subclause_no_continue(monkeypatch) -> None:
    """Omits --continue when continue_session is False."""
    assert "--continue" not in _invoke_and_capture(monkeypatch)


def test_invoke_implement_subclause_with_continue(monkeypatch) -> None:
    """Appends --continue when continue_session is True."""
    assert "--continue" in _invoke_and_capture(monkeypatch, continue_session=True)


def test_invoke_implement_subclause_failure(monkeypatch) -> None:
    """Calls sys.exit on nonzero returncode."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        invoke_implement_subclause(
            lrm="/tmp/lrm.pdf",
            subclause="6.1",
            issue=42,
            model="opus",
            continue_session=False,
        )
