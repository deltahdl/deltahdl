"""Tests for lib.python.cli."""

import argparse
import sys
import time
from pathlib import Path
from unittest.mock import patch

import pytest

from lib.python.cli import (
    ClauseParams,
    SubclauseParams,
    add_clauses_arg,
    add_continue_arg,
    add_github_args,
    add_lrm_arg,
    add_model_arg,
    invoke_implement_clause,
    invoke_implement_subclause,
    invoke_implement_subclauses,
    parse_and_validate,
    parse_clause_issues,
    run_claude_cli,
    run_with_dots,
    validate_lrm,
)
from lib.python.test_fixtures.subprocess_stubs import (
    spy_subprocess_run,
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
    validate_lrm(parser, args)
    assert args.lrm == lrm


def test_validate_lrm_file_missing() -> None:
    """Calls parser.error when file does not exist."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(lrm=Path("/nonexistent/lrm.pdf"))
    with pytest.raises(SystemExit):
        validate_lrm(parser, args)


# ---- add_github_args --------------------------------------------------------


def test_add_github_args_master_issue() -> None:
    """Adds --master-issue as required int."""
    parser = argparse.ArgumentParser()
    add_github_args(parser)
    args = parser.parse_args(["--master-issue", "1", "--organization", "o", "--repo", "r"])
    assert args.master_issue == 1


def test_add_github_args_organization() -> None:
    """Adds --organization as required string."""
    parser = argparse.ArgumentParser()
    add_github_args(parser)
    args = parser.parse_args(["--master-issue", "1", "--organization", "myorg", "--repo", "r"])
    assert args.organization == "myorg"


def test_add_github_args_repo() -> None:
    """Adds --repo as required string."""
    parser = argparse.ArgumentParser()
    add_github_args(parser)
    args = parser.parse_args(["--master-issue", "1", "--organization", "o", "--repo", "myrepo"])
    assert args.repo == "myrepo"


# ---- invoke_implement_subclause ---------------------------------------------


_SC_PARAMS = SubclauseParams(lrm="/tmp/lrm.pdf", issue=42, model="opus")


def _invoke_and_capture(monkeypatch, *, continue_session=False):
    """Invoke with stubbed subprocess and return captured command."""
    captured = stub_subprocess_success(monkeypatch)
    invoke_implement_subclause(_SC_PARAMS, "6.1", continue_session)
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


def test_invoke_implement_subclause_no_exclude(monkeypatch) -> None:
    """Omits --exclude when exclude is empty."""
    assert "--exclude" not in _invoke_and_capture(monkeypatch)


def test_invoke_implement_subclause_with_exclude(monkeypatch) -> None:
    """Appends --exclude when exclude is non-empty."""
    captured = stub_subprocess_success(monkeypatch)
    invoke_implement_subclause(_SC_PARAMS, "6.1", False, exclude="6.1.1,6.1.2")
    cmd = captured[0]
    assert cmd[cmd.index("--exclude") + 1] == "6.1.1,6.1.2"


def test_invoke_implement_subclause_failure(monkeypatch) -> None:
    """Calls sys.exit on nonzero returncode."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        invoke_implement_subclause(_SC_PARAMS, "6.1", False)


# ---- parse_clause_issues ----------------------------------------------------


def test_parse_clause_issues_single() -> None:
    """Single pair returns a one-element dict."""
    assert parse_clause_issues("15=17") == {"15": 17}


def test_parse_clause_issues_multiple() -> None:
    """Comma-separated pairs are split correctly."""
    assert parse_clause_issues("15=17,16=18") == {"15": 17, "16": 18}


def test_parse_clause_issues_strips_whitespace() -> None:
    """Whitespace around pairs is stripped."""
    assert parse_clause_issues(" 15 = 17 , 16 = 18 ") == {"15": 17, "16": 18}


def test_parse_clause_issues_rejects_no_equals() -> None:
    """Missing = sign raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        parse_clause_issues("15")


def test_parse_clause_issues_rejects_non_int_issue() -> None:
    """Non-integer issue number raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        parse_clause_issues("15=abc")


def test_parse_clause_issues_non_int_chains_cause() -> None:
    """Non-integer issue number chains the original ValueError."""
    cause = None
    try:
        parse_clause_issues("15=abc")
    except argparse.ArgumentTypeError as exc:
        cause = exc.__cause__
    assert isinstance(cause, ValueError)


def test_parse_clause_issues_rejects_invalid_clause() -> None:
    """Invalid clause format raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        parse_clause_issues("bad=17")


def test_add_clauses_arg() -> None:
    """Adds --clauses as a required argument."""
    parser = argparse.ArgumentParser()
    add_clauses_arg(parser)
    args = parser.parse_args(["--clauses", "15=17"])
    assert args.clauses == {"15": 17}


# ---- invoke_implement_clause ------------------------------------------------


_CL_PARAMS = ClauseParams(
    lrm="/tmp/lrm.pdf", master_issue=1,
    organization="deltahdl", repo="deltahdl",
)


def _invoke_clause_and_capture(monkeypatch):
    """Invoke with stubbed subprocess and return captured command."""
    captured = stub_subprocess_success(monkeypatch)
    invoke_implement_clause(_CL_PARAMS, "15", 17)
    return captured[0]


def test_invoke_implement_clause_module(monkeypatch) -> None:
    """Passes -m implement_clause."""
    assert _invoke_clause_and_capture(monkeypatch)[1:3] == ["-m", "implement_clause"]


def test_invoke_implement_clause_clause(monkeypatch) -> None:
    """Passes --clause with correct value."""
    cmd = _invoke_clause_and_capture(monkeypatch)
    assert cmd[cmd.index("--clause") + 1] == "15"


def test_invoke_implement_clause_sub_issue(monkeypatch) -> None:
    """Passes --sub-issue as string."""
    cmd = _invoke_clause_and_capture(monkeypatch)
    assert cmd[cmd.index("--sub-issue") + 1] == "17"


def test_invoke_implement_clause_master_issue(monkeypatch) -> None:
    """Passes --master-issue as string."""
    cmd = _invoke_clause_and_capture(monkeypatch)
    assert cmd[cmd.index("--master-issue") + 1] == "1"


def test_invoke_implement_clause_organization(monkeypatch) -> None:
    """Passes --organization with correct value."""
    cmd = _invoke_clause_and_capture(monkeypatch)
    assert cmd[cmd.index("--organization") + 1] == "deltahdl"


def test_invoke_implement_clause_repo(monkeypatch) -> None:
    """Passes --repo with correct value."""
    cmd = _invoke_clause_and_capture(monkeypatch)
    assert cmd[cmd.index("--repo") + 1] == "deltahdl"


def test_invoke_implement_clause_failure(monkeypatch) -> None:
    """Calls sys.exit on nonzero returncode."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        invoke_implement_clause(_CL_PARAMS, "15", 17)


# ---- invoke_implement_subclauses -------------------------------------------


def _invoke_subclauses_and_capture(monkeypatch):
    """Invoke with stubbed subprocess and return captured command."""
    captured = stub_subprocess_success(monkeypatch)
    invoke_implement_subclauses(
        "/tmp/lrm.pdf", [100, 101],
        organization="deltahdl", repo="deltahdl",
    )
    return captured[0]


def test_invoke_implement_subclauses_calls_python(monkeypatch) -> None:
    """Invokes the current Python interpreter."""
    assert _invoke_subclauses_and_capture(monkeypatch)[0] == sys.executable


def test_invoke_implement_subclauses_module(monkeypatch) -> None:
    """Passes -m implement_subclauses."""
    cmd = _invoke_subclauses_and_capture(monkeypatch)
    assert cmd[1:3] == ["-m", "implement_subclauses"]


def test_invoke_implement_subclauses_lrm(monkeypatch) -> None:
    """Passes --lrm with correct value."""
    cmd = _invoke_subclauses_and_capture(monkeypatch)
    assert cmd[cmd.index("--lrm") + 1] == "/tmp/lrm.pdf"


def test_invoke_implement_subclauses_issues(monkeypatch) -> None:
    """Passes --issues as comma-joined string."""
    cmd = _invoke_subclauses_and_capture(monkeypatch)
    assert cmd[cmd.index("--issues") + 1] == "100,101"


def test_invoke_implement_subclauses_organization(monkeypatch) -> None:
    """Passes --organization with correct value."""
    cmd = _invoke_subclauses_and_capture(monkeypatch)
    assert cmd[cmd.index("--organization") + 1] == "deltahdl"


def test_invoke_implement_subclauses_repo(monkeypatch) -> None:
    """Passes --repo with correct value."""
    cmd = _invoke_subclauses_and_capture(monkeypatch)
    assert cmd[cmd.index("--repo") + 1] == "deltahdl"


def test_invoke_implement_subclauses_model(monkeypatch) -> None:
    """Passes --model with default opus."""
    cmd = _invoke_subclauses_and_capture(monkeypatch)
    assert cmd[cmd.index("--model") + 1] == "opus"


def test_invoke_implement_subclauses_failure(monkeypatch) -> None:
    """Calls sys.exit on nonzero returncode."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        invoke_implement_subclauses(
            "/tmp/lrm.pdf", [100],
            organization="o", repo="r",
        )


# ---- parse_and_validate ----------------------------------------------------


def test_parse_and_validate_returns_namespace(tmp_path) -> None:
    """Returns a Namespace with parsed and validated args."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    assert parse_and_validate(parser, ["--lrm", str(lrm)]).lrm == lrm


def test_parse_and_validate_rejects_missing_lrm(tmp_path) -> None:
    """Calls parser.error when LRM file does not exist."""
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    with pytest.raises(SystemExit):
        parse_and_validate(parser, ["--lrm", str(tmp_path / "no.pdf")])


# ---- run_claude_cli -------------------------------------------------------


def test_run_claude_cli_calls_subprocess_run(monkeypatch):
    """run_claude_cli delegates to subprocess.run."""
    captured = stub_subprocess_success(monkeypatch)
    run_claude_cli(["claude", "-p"], "hello", env={"K": "V"})
    assert captured[0] == ["claude", "-p"]


def test_run_claude_cli_passes_timeout(monkeypatch):
    """run_claude_cli forwards the timeout parameter."""
    kwargs_log = spy_subprocess_run(monkeypatch)
    run_claude_cli(["true"], "", env={}, timeout=600)
    assert kwargs_log[0]["timeout"] == 600


def test_run_claude_cli_returns_completed_process(monkeypatch):
    """run_claude_cli returns the subprocess.CompletedProcess object."""
    stub_subprocess_success(monkeypatch)
    result = run_claude_cli(["true"], "", env={})
    assert result.returncode == 0


# ---- run_with_dots --------------------------------------------------------


def test_run_with_dots_returns_result():
    """run_with_dots returns the function result."""
    assert run_with_dots(lambda: 42) == 42


def test_run_with_dots_calls_function():
    """run_with_dots calls the provided function."""
    calls = []
    run_with_dots(lambda: calls.append(1))
    assert len(calls) == 1


def test_run_with_dots_prints_dots(capsys):
    """run_with_dots prints dots while the function runs."""
    with patch("lib.python.cli._DOT_INTERVAL_SECONDS", 0.05):
        run_with_dots(lambda: time.sleep(0.15))
    assert "." in capsys.readouterr().out
