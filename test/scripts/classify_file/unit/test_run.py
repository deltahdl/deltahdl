"""Unit tests for run-flow functions in classify_file."""

import subprocess
import sys
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

import classify_file

from helpers import (
    make_test_file,
    stub_subprocess_failure,
    stub_subprocess_mixed,
    stub_subprocess_success,
)

_parse_args = getattr(classify_file, "_parse_args")
_build_command = getattr(classify_file, "_build_command")
_run = getattr(classify_file, "_run")


# ---- Shared helpers --------------------------------------------------------


_BASE_ARGV = [
    "prog", "--file", "f.cpp",
    "--output-dir", "/out",
    "--lrm", "/lrm.txt",
]


def _make_args(**overrides):
    """Build a SimpleNamespace with all required args."""
    defaults = {
        "file": "/path/to/test.cpp",
        "output_dir": "/out",
        "lrm": "/lrm.txt",
        "issue": None,
        "organization": None,
        "repo": None,
        "dry_run": False,
        "no_commit": False,
        "max_lines": None,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


def _make_run_args(tmp_path, **overrides):
    """Build args for _run with a real test file."""
    defaults = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path),
        "lrm": str(tmp_path / "lrm.txt"),
        "issue": None,
        "organization": None,
        "repo": None,
        "dry_run": False,
        "no_commit": False,
        "max_lines": None,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


# ---- _parse_args -----------------------------------------------------------


def test_parse_args_file(monkeypatch):
    """Parses --file flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().file == "f.cpp"


def test_parse_args_output_dir(monkeypatch):
    """Parses --output-dir flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().output_dir == "/out"


def test_parse_args_lrm(monkeypatch):
    """Parses --lrm flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().lrm == "/lrm.txt"


def test_parse_args_issue(monkeypatch):
    """Parses --issue as integer."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--issue", "42"],
    )
    assert _parse_args().issue == 42


def test_parse_args_issue_default(monkeypatch):
    """Defaults --issue to None when not provided."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().issue is None


def test_parse_args_organization(monkeypatch):
    """Parses --organization flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--organization", "myorg"],
    )
    assert _parse_args().organization == "myorg"


def test_parse_args_organization_default(monkeypatch):
    """Defaults --organization to None when not provided."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().organization is None


def test_parse_args_repo(monkeypatch):
    """Parses --repo flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--repo", "myrepo"],
    )
    assert _parse_args().repo == "myrepo"


def test_parse_args_repo_default(monkeypatch):
    """Defaults --repo to None when not provided."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().repo is None


def test_parse_args_dry_run(monkeypatch):
    """Parses --dry-run flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--dry-run"],
    )
    assert _parse_args().dry_run is True


def test_parse_args_dry_run_default(monkeypatch):
    """Defaults --dry-run to False."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().dry_run is False


def test_parse_args_no_commit(monkeypatch):
    """Parses --no-commit flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--no-commit"],
    )
    assert _parse_args().no_commit is True


def test_parse_args_no_commit_default(monkeypatch):
    """Defaults --no-commit to False."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().no_commit is False


def test_parse_args_max_lines(monkeypatch):
    """Parses --max-lines as integer."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--max-lines", "500"],
    )
    assert _parse_args().max_lines == 500


def test_parse_args_max_lines_default(monkeypatch):
    """Defaults --max-lines to None."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert _parse_args().max_lines is None


def test_parse_args_no_test_flag(monkeypatch):
    """Rejects the --test flag since classify_file does not accept it."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--test", "T"],
    )
    with pytest.raises(SystemExit):
        _parse_args()


# ---- _build_command --------------------------------------------------------


def test_build_command_basic():
    """Command starts with python -m classify_test."""
    cmd = _build_command(_make_args(), "T")
    assert cmd[:3] == [sys.executable, "-m", "classify_test"]


def test_build_command_file_flag():
    """Command includes --file with correct value."""
    cmd = _build_command(_make_args(file="/a/b.cpp"), "T")
    assert cmd[cmd.index("--file") + 1] == "/a/b.cpp"


def test_build_command_output_dir_flag():
    """Command includes --output-dir with correct value."""
    cmd = _build_command(_make_args(output_dir="/out"), "T")
    assert cmd[cmd.index("--output-dir") + 1] == "/out"


def test_build_command_lrm_flag():
    """Command includes --lrm with correct value."""
    cmd = _build_command(_make_args(lrm="/lrm.txt"), "T")
    assert cmd[cmd.index("--lrm") + 1] == "/lrm.txt"


def test_build_command_test_flag():
    """Command includes --test with the given test name."""
    cmd = _build_command(_make_args(), "FooBar")
    assert cmd[cmd.index("--test") + 1] == "FooBar"


def test_build_command_issue_included():
    """Command includes --issue when set."""
    args = _make_args(issue=42, organization="org", repo="repo")
    cmd = _build_command(args, "T")
    assert "--issue" in cmd


def test_build_command_issue_omitted():
    """Command omits --issue when not set."""
    cmd = _build_command(_make_args(), "T")
    assert "--issue" not in cmd


def test_build_command_dry_run_included():
    """Command includes --dry-run when set."""
    cmd = _build_command(_make_args(dry_run=True), "T")
    assert "--dry-run" in cmd


def test_build_command_dry_run_omitted():
    """Command omits --dry-run when not set."""
    cmd = _build_command(_make_args(), "T")
    assert "--dry-run" not in cmd


def test_build_command_no_commit_included():
    """Command includes --no-commit when set."""
    cmd = _build_command(_make_args(no_commit=True), "T")
    assert "--no-commit" in cmd


def test_build_command_no_commit_omitted():
    """Command omits --no-commit when not set."""
    cmd = _build_command(_make_args(), "T")
    assert "--no-commit" not in cmd


def test_build_command_max_lines_included():
    """Command includes --max-lines when set."""
    cmd = _build_command(_make_args(max_lines=500), "T")
    assert cmd[cmd.index("--max-lines") + 1] == "500"


def test_build_command_max_lines_omitted():
    """Command omits --max-lines when not set."""
    cmd = _build_command(_make_args(), "T")
    assert "--max-lines" not in cmd


# ---- run_classify_test -----------------------------------------------------


def test_run_classify_test_returns_true_on_success(monkeypatch):
    """Returns True when subprocess exits with 0."""
    stub_subprocess_success(monkeypatch)
    assert classify_file.run_classify_test(
        _make_args(), "T", 1, 1,
    ) is True


def test_run_classify_test_returns_false_on_failure(monkeypatch):
    """Returns False when subprocess exits with non-zero."""
    stub_subprocess_failure(monkeypatch)
    assert classify_file.run_classify_test(
        _make_args(), "T", 1, 1,
    ) is False


def test_run_classify_test_prints_progress(monkeypatch, capsys):
    """Prints progress line with index and name."""
    stub_subprocess_success(monkeypatch)
    classify_file.run_classify_test(_make_args(), "Alpha", 3, 10)
    assert "Processing test 3/10: Alpha" in capsys.readouterr().out


def test_run_classify_test_passes_test_name(monkeypatch):
    """Subprocess receives --test with the correct name."""
    captured = stub_subprocess_success(monkeypatch)
    classify_file.run_classify_test(_make_args(), "FooBar", 1, 1)
    assert captured[0][captured[0].index("--test") + 1] == "FooBar"


def test_run_classify_test_forwards_stdout(monkeypatch, capsys):
    """Forwards subprocess stdout to parent stdout."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "classified OK\n"
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    classify_file.run_classify_test(_make_args(), "T", 1, 1)
    assert "classified OK" in capsys.readouterr().out


def test_run_classify_test_prints_stderr_on_failure(
    monkeypatch, capsys,
):
    """Forwards subprocess stderr on failure."""
    stub_subprocess_failure(monkeypatch)
    classify_file.run_classify_test(_make_args(), "T", 1, 1)
    assert "error" in capsys.readouterr().err


# ---- print_summary ---------------------------------------------------------


def test_print_summary_all_succeeded(capsys):
    """Prints N/N tests succeeded when all pass."""
    classify_file.print_summary(3, 0, [])
    assert "3/3 tests succeeded" in capsys.readouterr().out


def test_print_summary_some_failed(capsys):
    """Prints N/M tests succeeded when some fail."""
    classify_file.print_summary(2, 1, ["BadTest"])
    assert "2/3 tests succeeded" in capsys.readouterr().out


def test_print_summary_lists_failures(capsys):
    """Prints failed test names."""
    classify_file.print_summary(1, 2, ["Bad1", "Bad2"])
    assert "Bad1" in capsys.readouterr().out


def test_print_summary_no_failures_omits_list(capsys):
    """Does not print failure header when all tests pass."""
    classify_file.print_summary(3, 0, [])
    assert "Failed:" not in capsys.readouterr().out


def test_print_summary_lists_all_failures(capsys):
    """Lists every failed test name in output."""
    classify_file.print_summary(0, 2, ["A", "B"])
    out = capsys.readouterr().out
    assert "B" in out


# ---- _run ------------------------------------------------------------------


def test_run_file_not_found(tmp_path):
    """Exits when input file does not exist."""
    args = _make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
    )
    with pytest.raises(SystemExit):
        _run(args)


def test_run_no_tests(tmp_path):
    """Exits when file has no TEST blocks."""
    make_test_file(tmp_path, "#include <gtest/gtest.h>\n")
    with pytest.raises(SystemExit):
        _run(_make_run_args(tmp_path))


def test_run_all_succeed(tmp_path, monkeypatch, capsys):
    """Does not exit when all tests succeed."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    make_test_file(tmp_path, body)
    stub_subprocess_success(monkeypatch)
    _run(_make_run_args(tmp_path))
    assert "2/2 tests succeeded" in capsys.readouterr().out


def test_run_some_fail_exits(tmp_path, monkeypatch):
    """Exits when any test fails."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    make_test_file(tmp_path, body)
    stub_subprocess_mixed(monkeypatch, {"B"})
    with pytest.raises(SystemExit):
        _run(_make_run_args(tmp_path))


def test_run_continues_after_failure(tmp_path, monkeypatch, capsys):
    """Processes remaining tests after a failure."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\nTEST(S, C) {\n}\n"
    make_test_file(tmp_path, body)
    stub_subprocess_mixed(monkeypatch, {"A"})
    try:
        _run(_make_run_args(tmp_path))
    except SystemExit:
        pass
    assert "Processing test 3/3: C" in capsys.readouterr().out


def test_run_summary_shows_failures(tmp_path, monkeypatch, capsys):
    """Summary lists failed test names."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    make_test_file(tmp_path, body)
    stub_subprocess_mixed(monkeypatch, {"B"})
    try:
        _run(_make_run_args(tmp_path))
    except SystemExit:
        pass
    assert "B" in capsys.readouterr().out


def test_run_invokes_per_test(tmp_path, monkeypatch):
    """Invokes classify_test once per test name."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\nTEST(S, C) {\n}\n"
    make_test_file(tmp_path, body)
    captured = stub_subprocess_success(monkeypatch)
    _run(_make_run_args(tmp_path))
    assert len(captured) == 3


# ---- main ------------------------------------------------------------------


def test_main_calls_run(monkeypatch):
    """Calls _run with parsed args."""
    ran = []
    monkeypatch.setattr(
        classify_file, "_run",
        lambda args: ran.append(True),
    )
    monkeypatch.setattr(
        classify_file, "_parse_args", _make_args,
    )
    classify_file.main()
    assert ran == [True]


def test_main_enables_line_buffering(monkeypatch):
    """Reconfigures stdout to line-buffered mode."""
    configured = []
    original = sys.stdout.reconfigure

    def mock_reconfigure(**kwargs):
        configured.append(kwargs)
        return original(**kwargs)

    monkeypatch.setattr(sys.stdout, "reconfigure", mock_reconfigure)
    monkeypatch.setattr(classify_file, "_run", lambda _: None)
    monkeypatch.setattr(
        classify_file, "_parse_args", _make_args,
    )
    classify_file.main()
    assert any(k.get("line_buffering") for k in configured)
