"""Tests for lib.python.cli."""

import argparse
import time
from pathlib import Path
from unittest.mock import patch

import pytest

from lib.python.cli import (
    add_clause_arg,
    add_clauses_arg,
    add_continue_arg,
    add_github_args,
    add_labels_arg,
    add_lrm_arg,
    add_model_arg,
    add_subclause_arg,
    add_subclauses_arg,
    parse_and_validate,
    parse_and_validate_clause,
    parse_and_validate_subclause,
    parse_clauses,
    parse_labels,
    parse_subclauses,
    run_claude_cli,
    run_with_dots,
    validate_clause,
    validate_lrm,
    validate_subclause,
)
from lib.python.test_fixtures.subprocess_stubs import (
    spy_subprocess_run,
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


def test_validate_subclause_rejects_top_level_numeric() -> None:
    """Calls parser.error for a depth-0 numeric clause."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(subclause="33")
    with pytest.raises(SystemExit):
        validate_subclause(parser, args)


def test_validate_subclause_rejects_top_level_annex() -> None:
    """Calls parser.error for a depth-0 annex letter."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(subclause="A")
    with pytest.raises(SystemExit):
        validate_subclause(parser, args)


def test_validate_subclause_error_routes_to_satisfy_clause(capsys) -> None:
    """Depth-0 rejection message names ``satisfy_clause``."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(subclause="33")
    try:
        validate_subclause(parser, args)
    except SystemExit:
        pass
    assert "satisfy_clause" in capsys.readouterr().err


# ---- parse_and_validate_subclause -------------------------------------------


def _subclause_parser():
    """Build a minimal parser wired up for parse_and_validate_subclause."""
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    add_subclause_arg(parser)
    return parser


def test_parse_and_validate_subclause_returns_namespace(tmp_path) -> None:
    """Returns the parsed namespace when --lrm and --subclause are valid."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = _subclause_parser()
    args = parse_and_validate_subclause(
        parser, ["--lrm", str(lrm), "--subclause", "33.4.1.5"],
    )
    assert args.subclause == "33.4.1.5"


def test_parse_and_validate_subclause_rejects_missing_lrm(tmp_path) -> None:
    """Errors out when --lrm points at a non-existent file."""
    parser = _subclause_parser()
    with pytest.raises(SystemExit):
        parse_and_validate_subclause(
            parser,
            ["--lrm", str(tmp_path / "no.pdf"), "--subclause", "4.1"],
        )


def test_parse_and_validate_subclause_rejects_bad_subclause(tmp_path) -> None:
    """Errors out when --subclause is not a valid clause string."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = _subclause_parser()
    with pytest.raises(SystemExit):
        parse_and_validate_subclause(
            parser,
            ["--lrm", str(lrm), "--subclause", "garbage"],
        )


# ---- add_clause_arg ---------------------------------------------------------


def test_add_clause_arg_value() -> None:
    """Adds --clause as a required string argument."""
    parser = argparse.ArgumentParser()
    add_clause_arg(parser)
    args = parser.parse_args(["--clause", "33"])
    assert args.clause == "33"


def test_add_clause_arg_required() -> None:
    """--clause is required."""
    parser = argparse.ArgumentParser()
    add_clause_arg(parser)
    with pytest.raises(SystemExit):
        parser.parse_args([])


# ---- validate_clause --------------------------------------------------------


def test_validate_clause_accepts_numeric() -> None:
    """Returns without error for a depth-0 numeric clause."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(clause="33")
    validate_clause(parser, args)
    assert args.clause == "33"


def test_validate_clause_accepts_annex() -> None:
    """Returns without error for a single annex letter."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(clause="A")
    validate_clause(parser, args)
    assert args.clause == "A"


def test_validate_clause_rejects_subclause() -> None:
    """Calls parser.error for a depth-≥1 subclause id."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(clause="33.1")
    with pytest.raises(SystemExit):
        validate_clause(parser, args)


def test_validate_clause_rejects_lowercase() -> None:
    """Calls parser.error for a lowercase letter."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(clause="a")
    with pytest.raises(SystemExit):
        validate_clause(parser, args)


def test_validate_clause_rejects_garbage() -> None:
    """Calls parser.error for a non-clause string."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(clause="not-a-clause")
    with pytest.raises(SystemExit):
        validate_clause(parser, args)


def test_validate_clause_subclause_error_routes_to_satisfy_subclause(capsys) -> None:
    """Subclause-shaped rejection message names ``satisfy_subclause``."""
    parser = argparse.ArgumentParser()
    args = argparse.Namespace(clause="33.1")
    try:
        validate_clause(parser, args)
    except SystemExit:
        pass
    assert "satisfy_subclause" in capsys.readouterr().err


# ---- parse_and_validate_clause ----------------------------------------------


def _clause_parser():
    """Build a minimal parser wired up for parse_and_validate_clause."""
    parser = argparse.ArgumentParser()
    add_lrm_arg(parser)
    add_clause_arg(parser)
    return parser


def test_parse_and_validate_clause_returns_namespace(tmp_path) -> None:
    """Returns the parsed namespace when --lrm and --clause are valid."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = _clause_parser()
    args = parse_and_validate_clause(
        parser, ["--lrm", str(lrm), "--clause", "33"],
    )
    assert args.clause == "33"


def test_parse_and_validate_clause_rejects_missing_lrm(tmp_path) -> None:
    """Errors out when --lrm points at a non-existent file."""
    parser = _clause_parser()
    with pytest.raises(SystemExit):
        parse_and_validate_clause(
            parser,
            ["--lrm", str(tmp_path / "no.pdf"), "--clause", "33"],
        )


def test_parse_and_validate_clause_rejects_bad_clause(tmp_path) -> None:
    """Errors out when --clause is not a valid depth-0 string."""
    lrm = tmp_path / "lrm.pdf"
    lrm.touch()
    parser = _clause_parser()
    with pytest.raises(SystemExit):
        parse_and_validate_clause(
            parser,
            ["--lrm", str(lrm), "--clause", "33.1"],
        )


# ---- add_github_args --------------------------------------------------------


def test_add_github_args_organization() -> None:
    """Adds --organization as required string."""
    parser = argparse.ArgumentParser()
    add_github_args(parser)
    args = parser.parse_args(["--organization", "myorg", "--repo", "r"])
    assert args.organization == "myorg"


def test_add_github_args_repo() -> None:
    """Adds --repo as required string."""
    parser = argparse.ArgumentParser()
    add_github_args(parser)
    args = parser.parse_args(["--organization", "o", "--repo", "myrepo"])
    assert args.repo == "myrepo"


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


def test_parse_subclauses_rejects_top_level_entry() -> None:
    """A depth-0 entry raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        parse_subclauses("33.1,33")


def test_parse_subclauses_rejects_garbage_entry() -> None:
    """A malformed entry raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        parse_subclauses("garbage")


# ---- add_subclauses_arg ----------------------------------------------------


def test_add_subclauses_arg() -> None:
    """Adds --subclauses parsed into a validated list."""
    parser = argparse.ArgumentParser()
    add_subclauses_arg(parser)
    args = parser.parse_args(["--subclauses", "33.1,33.4"])
    assert args.subclauses == ["33.1", "33.4"]


def test_add_subclauses_arg_required() -> None:
    """--subclauses is required."""
    parser = argparse.ArgumentParser()
    add_subclauses_arg(parser)
    with pytest.raises(SystemExit):
        parser.parse_args([])


# ---- parse_clauses ---------------------------------------------------------


def test_parse_clauses_single() -> None:
    """Single entry returns a one-element list."""
    assert parse_clauses("33") == ["33"]


def test_parse_clauses_multiple() -> None:
    """Comma-separated entries are split into a list."""
    assert parse_clauses("32,33,A") == ["32", "33", "A"]


def test_parse_clauses_strips_whitespace() -> None:
    """Whitespace around commas is stripped."""
    assert parse_clauses(" 32 , A ") == ["32", "A"]


def test_parse_clauses_rejects_subclause_entry() -> None:
    """A depth-≥1 entry raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        parse_clauses("32,33.1")


def test_parse_clauses_subclause_error_routes_to_satisfy_subclauses() -> None:
    """Subclause-shaped entry's error names ``satisfy_subclauses``."""
    with pytest.raises(argparse.ArgumentTypeError, match="satisfy_subclauses"):
        parse_clauses("33.1")


def test_parse_clauses_rejects_garbage_entry() -> None:
    """A malformed entry raises ArgumentTypeError."""
    with pytest.raises(argparse.ArgumentTypeError):
        parse_clauses("garbage")


# ---- add_clauses_arg -------------------------------------------------------


def test_add_clauses_arg() -> None:
    """Adds --clauses parsed into a validated list."""
    parser = argparse.ArgumentParser()
    add_clauses_arg(parser)
    args = parser.parse_args(["--clauses", "32,33,A"])
    assert args.clauses == ["32", "33", "A"]


def test_add_clauses_arg_required() -> None:
    """--clauses is required."""
    parser = argparse.ArgumentParser()
    add_clauses_arg(parser)
    with pytest.raises(SystemExit):
        parser.parse_args([])
