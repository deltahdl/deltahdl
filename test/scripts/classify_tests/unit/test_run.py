"""Unit tests for classify_tests."""

import sys
from types import SimpleNamespace

import pytest

from lib.python.test_fixtures import capture_help_output
from lib.python.test_fixtures.subprocess_stubs import spy_subprocess_run


# ---- Shared helpers --------------------------------------------------------


_BASE_ARGV = [
    "prog", "--file", "f.cpp",
    "--tests", "A,B",
    "--output-dir", "/out",
    "--lrm", "/lrm.txt",
    "--organization", "testorg",
    "--repo", "testrepo",
    "--max-lines", "1000",
]


def _make_args(**overrides):
    """Build a SimpleNamespace with all required args."""
    defaults = {
        "file": "/path/to/test.cpp",
        "tests": "A,B,C",
        "issue": None,
        "output_dir": "/out",
        "lrm": "/lrm.txt",
        "organization": "testorg",
        "repo": "testrepo",
        "dry_run": False,
        "no_commit": False,
        "max_lines": 1000,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


def _stub_subprocess_success(monkeypatch):
    """Stub subprocess.run to always succeed. Returns captured commands."""
    import subprocess
    captured = []

    def fake_run(cmd, **kwargs):
        captured.append(cmd)
        return SimpleNamespace(returncode=0)

    monkeypatch.setattr(subprocess, "run", fake_run)
    return captured


def _stub_subprocess_failure(monkeypatch):
    """Stub subprocess.run to always fail."""
    import subprocess

    def fake_run(cmd, **kwargs):
        return SimpleNamespace(returncode=1)

    monkeypatch.setattr(subprocess, "run", fake_run)


def _argv_without_flag(base, flag):
    """Return *base* with *flag* and its value removed."""
    return [v for i, v in enumerate(base)
            if flag not in (base[max(0, i - 1)], v)]


# ---- _parse_args -----------------------------------------------------------


def test_parse_args_file(monkeypatch, cts):
    """Parses --file flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cts, "_parse_args")().file == "f.cpp"


def test_parse_args_tests(monkeypatch, cts):
    """Parses --tests flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cts, "_parse_args")().tests == "A,B"


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
        sys, "argv", _argv_without_flag(_BASE_ARGV, "--file"),
    )
    with pytest.raises(SystemExit):
        getattr(cts, "_parse_args")()


def test_parse_args_tests_required(monkeypatch, cts):
    """Rejects missing --tests flag."""
    monkeypatch.setattr(
        sys, "argv", _argv_without_flag(_BASE_ARGV, "--tests"),
    )
    with pytest.raises(SystemExit):
        getattr(cts, "_parse_args")()


# ---- _build_command --------------------------------------------------------


def test_build_command_basic(cts):
    """Command starts with python -m classify_test."""
    cmd = getattr(cts, "_build_command")(_make_args(), "T")
    assert cmd[:3] == [sys.executable, "-m", "classify_test"]


def test_build_command_file_flag(cts):
    """Command includes --file with correct value."""
    cmd = getattr(cts, "_build_command")(_make_args(file="/a/b.cpp"), "T")
    assert cmd[cmd.index("--file") + 1] == "/a/b.cpp"


def test_build_command_test_flag(cts):
    """Command includes --test with the given test name."""
    cmd = getattr(cts, "_build_command")(_make_args(), "FooBar")
    assert cmd[cmd.index("--test") + 1] == "FooBar"


def test_build_command_issue_included(cts):
    """Command includes --issue when set."""
    cmd = getattr(cts, "_build_command")(_make_args(issue=42), "T")
    assert cmd[cmd.index("--issue") + 1] == "42"


def test_build_command_issue_omitted(cts):
    """Command omits --issue when None."""
    cmd = getattr(cts, "_build_command")(_make_args(issue=None), "T")
    assert "--issue" not in cmd


def test_build_command_output_dir_flag(cts):
    """Command includes --output-dir with correct value."""
    cmd = getattr(cts, "_build_command")(_make_args(output_dir="/out"), "T")
    assert cmd[cmd.index("--output-dir") + 1] == "/out"


def test_build_command_lrm_flag(cts):
    """Command includes --lrm with correct value."""
    cmd = getattr(cts, "_build_command")(_make_args(lrm="/lrm.txt"), "T")
    assert cmd[cmd.index("--lrm") + 1] == "/lrm.txt"


def test_build_command_organization(cts):
    """Command includes --organization."""
    cmd = getattr(cts, "_build_command")(_make_args(), "T")
    assert cmd[cmd.index("--organization") + 1] == "testorg"


def test_build_command_repo(cts):
    """Command includes --repo."""
    cmd = getattr(cts, "_build_command")(_make_args(), "T")
    assert cmd[cmd.index("--repo") + 1] == "testrepo"


def test_build_command_max_lines(cts):
    """Command includes --max-lines."""
    cmd = getattr(cts, "_build_command")(_make_args(), "T")
    assert cmd[cmd.index("--max-lines") + 1] == "1000"


def test_build_command_dry_run_included(cts):
    """Command includes --dry-run when set."""
    cmd = getattr(cts, "_build_command")(_make_args(dry_run=True), "T")
    assert "--dry-run" in cmd


def test_build_command_dry_run_omitted(cts):
    """Command omits --dry-run when not set."""
    cmd = getattr(cts, "_build_command")(_make_args(), "T")
    assert "--dry-run" not in cmd


def test_build_command_no_commit_included(cts):
    """Command includes --no-commit when set."""
    cmd = getattr(cts, "_build_command")(_make_args(no_commit=True), "T")
    assert "--no-commit" in cmd


def test_build_command_no_commit_omitted(cts):
    """Command omits --no-commit when not set."""
    cmd = getattr(cts, "_build_command")(_make_args(), "T")
    assert "--no-commit" not in cmd


# ---- run_classify_test -----------------------------------------------------


def test_run_classify_test_returns_true_on_success(monkeypatch, cts):
    """Returns True when subprocess exits with 0."""
    _stub_subprocess_success(monkeypatch)
    assert cts.run_classify_test(_make_args(), "T", 1, 1) is True


def test_run_classify_test_returns_false_on_failure(monkeypatch, cts):
    """Returns False when subprocess exits with non-zero."""
    _stub_subprocess_failure(monkeypatch)
    assert cts.run_classify_test(_make_args(), "T", 1, 1) is False


def test_run_classify_test_prints_progress(monkeypatch, cts, capsys):
    """Prints progress line with index and name."""
    _stub_subprocess_success(monkeypatch)
    cts.run_classify_test(_make_args(), "Alpha", 3, 10)
    assert "Processing test 3/10: Alpha\n" in capsys.readouterr().out


# ---- _run ------------------------------------------------------------------


def test_run_loops_all_tests(monkeypatch, cts):
    """Invokes classify_test once per comma-separated name."""
    captured = _stub_subprocess_success(monkeypatch)
    getattr(cts, "_run")(_make_args(tests="A,B,C"))
    assert len(captured) == 3


def test_run_exits_on_failure(monkeypatch, cts):
    """Exits when a test fails."""
    _stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        getattr(cts, "_run")(_make_args(tests="A,B"))


def test_run_stops_after_failure(monkeypatch, cts):
    """Does not invoke further tests after failure."""
    import subprocess
    captured = []

    def fake_run(cmd, **kwargs):
        captured.append(cmd)
        return SimpleNamespace(returncode=1)

    monkeypatch.setattr(subprocess, "run", fake_run)
    try:
        getattr(cts, "_run")(_make_args(tests="A,B,C"))
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
    configured = []
    original = sys.stdout.reconfigure

    def mock_reconfigure(**kwargs):
        configured.append(kwargs)
        return original(**kwargs)

    monkeypatch.setattr(sys.stdout, "reconfigure", mock_reconfigure)
    monkeypatch.setattr(cts, "_run", lambda _: None)
    monkeypatch.setattr(cts, "_parse_args", _make_args)
    cts.main()
    assert any(k.get("line_buffering") for k in configured)
