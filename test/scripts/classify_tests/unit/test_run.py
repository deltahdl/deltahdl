"""Unit tests for classify_tests."""

import subprocess
import sys
from types import SimpleNamespace

import pytest

from lib.python.test_fixtures import (
    CLASSIFY_BASE_ARGV,
    argv_without_flag,
    main_enables_line_buffering,
    capture_help_output,
    make_classify_args,
)
from lib.python.test_fixtures.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
)


# ---- Shared helpers --------------------------------------------------------


_BASE_ARGV = [
    "prog", "--file", "f.cpp",
    "--tests", "S.A,S.B",
    *CLASSIFY_BASE_ARGV,
]


def _make_args(**overrides):
    """Build args with classify_tests-specific defaults."""
    defaults = {"tests": "S.A,S.B,S.C", "issue": None}
    defaults.update(overrides)
    return make_classify_args(**defaults)


# ---- _parse_args -----------------------------------------------------------


def test_parse_args_file(monkeypatch, cts):
    """Parses --file flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cts, "_parse_args")().file == "f.cpp"


def test_parse_args_tests(monkeypatch, cts):
    """Parses --tests flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cts, "_parse_args")().tests == "S.A,S.B"


def test_parse_args_issue_optional(monkeypatch, cts):
    """--issue defaults to None."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cts, "_parse_args")().issue is None


def test_parse_args_issue_with_value(monkeypatch, cts):
    """Parses --issue as integer."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--issue", "42"],
    )
    assert getattr(cts, "_parse_args")().issue == 42


def test_parse_args_prog_name(monkeypatch, cts, capsys):
    """Usage line shows 'classify_tests' as program name."""
    assert "classify_tests" in capture_help_output(
        getattr(cts, "_parse_args"), monkeypatch, capsys,
    )


def test_parse_args_file_required(monkeypatch, cts):
    """Rejects missing --file flag."""
    monkeypatch.setattr(
        sys, "argv", argv_without_flag(_BASE_ARGV, "--file"),
    )
    with pytest.raises(SystemExit):
        getattr(cts, "_parse_args")()


def test_parse_args_tests_required(monkeypatch, cts):
    """Rejects missing --tests flag."""
    monkeypatch.setattr(
        sys, "argv", argv_without_flag(_BASE_ARGV, "--tests"),
    )
    with pytest.raises(SystemExit):
        getattr(cts, "_parse_args")()


# ---- _build_command --------------------------------------------------------


def test_build_command_basic(cts):
    """Command starts with python -m classify_test."""
    cmd = getattr(cts, "_build_command")(_make_args(), "S.T")
    assert cmd[:3] == [sys.executable, "-m", "classify_test"]


def test_build_command_file_flag(cts):
    """Command includes --file with correct value."""
    cmd = getattr(cts, "_build_command")(_make_args(file="/a/b.cpp"), "S.T")
    assert cmd[cmd.index("--file") + 1] == "/a/b.cpp"


def test_build_command_suite_flag(cts):
    """Command includes --suite extracted from Suite.Test entry."""
    cmd = getattr(cts, "_build_command")(_make_args(), "MySuite.FooBar")
    assert cmd[cmd.index("--suite") + 1] == "MySuite"


def test_build_command_test_flag(cts):
    """Command includes --test extracted from Suite.Test entry."""
    cmd = getattr(cts, "_build_command")(_make_args(), "MySuite.FooBar")
    assert cmd[cmd.index("--test") + 1] == "FooBar"


def test_build_command_issue_included(cts):
    """Command includes --issue when set."""
    cmd = getattr(cts, "_build_command")(_make_args(issue=42), "S.T")
    assert cmd[cmd.index("--issue") + 1] == "42"


def test_build_command_issue_omitted(cts):
    """Command omits --issue when None."""
    cmd = getattr(cts, "_build_command")(_make_args(issue=None), "S.T")
    assert "--issue" not in cmd


def test_build_command_output_dir_flag(cts):
    """Command includes --output-dir with correct value."""
    cmd = getattr(cts, "_build_command")(_make_args(output_dir="/out"), "S.T")
    assert cmd[cmd.index("--output-dir") + 1] == "/out"


def test_build_command_lrm_flag(cts):
    """Command includes --lrm with correct value."""
    cmd = getattr(cts, "_build_command")(_make_args(lrm="/lrm.txt"), "S.T")
    assert cmd[cmd.index("--lrm") + 1] == "/lrm.txt"


def test_build_command_organization(cts):
    """Command includes --organization."""
    cmd = getattr(cts, "_build_command")(_make_args(), "S.T")
    assert cmd[cmd.index("--organization") + 1] == "testorg"


def test_build_command_repo(cts):
    """Command includes --repo."""
    cmd = getattr(cts, "_build_command")(_make_args(), "S.T")
    assert cmd[cmd.index("--repo") + 1] == "testrepo"


def test_build_command_max_lines(cts):
    """Command includes --max-lines."""
    cmd = getattr(cts, "_build_command")(_make_args(), "S.T")
    assert cmd[cmd.index("--max-lines") + 1] == "1000"


def test_build_command_dry_run_included(cts):
    """Command includes --dry-run when set."""
    cmd = getattr(cts, "_build_command")(_make_args(dry_run=True), "S.T")
    assert "--dry-run" in cmd


def test_build_command_dry_run_omitted(cts):
    """Command omits --dry-run when not set."""
    cmd = getattr(cts, "_build_command")(_make_args(), "S.T")
    assert "--dry-run" not in cmd


def test_build_command_no_commit_included(cts):
    """Command includes --no-commit when set."""
    cmd = getattr(cts, "_build_command")(_make_args(no_commit=True), "S.T")
    assert "--no-commit" in cmd


def test_build_command_no_commit_omitted(cts):
    """Command omits --no-commit when not set."""
    cmd = getattr(cts, "_build_command")(_make_args(), "S.T")
    assert "--no-commit" not in cmd


# ---- run_classify_test -----------------------------------------------------


def test_run_classify_test_returns_true_on_success(monkeypatch, cts):
    """Returns True when subprocess exits with 0."""
    stub_subprocess_success(monkeypatch)
    assert cts.run_classify_test(_make_args(), "S.T", 1, 1) is True


def test_run_classify_test_returns_false_on_failure(monkeypatch, cts):
    """Returns False when subprocess exits with non-zero."""
    stub_subprocess_failure(monkeypatch)
    assert cts.run_classify_test(_make_args(), "S.T", 1, 1) is False


def test_run_classify_test_prints_progress(monkeypatch, cts, capsys):
    """Prints progress line with index and name."""
    stub_subprocess_success(monkeypatch)
    cts.run_classify_test(_make_args(), "S.Alpha", 3, 10)
    assert "Processing test 3/10: S.Alpha\n" in capsys.readouterr().out


# ---- _run ------------------------------------------------------------------


def test_run_loops_all_tests(monkeypatch, cts):
    """Invokes classify_test once per comma-separated name."""
    captured = stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_make_args(tests="S.A,S.B,S.C"))
    assert len(captured) == 3


def test_run_exits_on_failure(monkeypatch, cts):
    """Exits when a test fails."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        getattr(cts, "_run")(_make_args(tests="S.A,S.B"))


def test_run_stops_after_failure(monkeypatch, cts):
    """Does not invoke further tests after failure."""
    captured = []

    def failing_run(cmd, **_kw):
        captured.append(cmd)
        return SimpleNamespace(returncode=1)

    monkeypatch.setattr(subprocess, "run", failing_run)
    try:
        getattr(cts, "_run")(_make_args(tests="S.A,S.B,S.C"))
    except SystemExit:
        pass
    assert len(captured) == 1


# ---- main ------------------------------------------------------------------


def test_main_calls_run(monkeypatch, cts):
    """Calls _run with parsed args."""
    ran = []
    monkeypatch.setattr(cts, "_run", lambda args: ran.append(True))
    monkeypatch.setattr(cts, "_parse_args", _make_args)
    cts.main()
    assert ran == [True]


def test_main_enables_line_buffering(monkeypatch, cts):
    """Reconfigures stdout to line-buffered mode."""
    assert main_enables_line_buffering(monkeypatch, cts, _make_args)
