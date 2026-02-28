"""Integration tests for the classify_file pipeline."""

import subprocess
from types import SimpleNamespace
from unittest.mock import MagicMock

import classify_file

_run = getattr(classify_file, "_run")


# ---- Helpers ---------------------------------------------------------------


_ARGS_DEFAULTS = {
    "issue": 99, "create_issue": False,
    "organization": "testorg", "repo": "testrepo",
    "dry_run": False, "no_commit": False, "max_lines": 1000,
}


def _pipeline_args(tmp_path, **overrides):
    """Build args pointing at test_input.cpp inside *tmp_path*."""
    result = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path),
        "lrm": str(tmp_path / "lrm.txt"),
        **_ARGS_DEFAULTS, **overrides,
    }
    return SimpleNamespace(**result)


def _write_and_args(tmp_path, body, **overrides):
    """Write test_input.cpp and return args for _run."""
    (tmp_path / "test_input.cpp").write_text(
        body, encoding="utf-8",
    )
    return _pipeline_args(tmp_path, **overrides)


def _mock_run_ok(monkeypatch):
    """Stub subprocess.run to succeed; return command log."""
    log: list[list[str]] = []

    def ok_run(cmd, **_kw):
        log.append(list(cmd))
        m = MagicMock()
        m.returncode, m.stdout, m.stderr = 0, "", ""
        return m

    monkeypatch.setattr(subprocess, "run", ok_run)
    return log


def _mock_run_selective(monkeypatch, fail_set):
    """Stub subprocess.run to fail only for names in *fail_set*."""

    def sel_run(cmd, **_kw):
        m = MagicMock()
        m.stdout, m.stderr = "", ""
        name = cmd[cmd.index("--test") + 1]
        m.returncode = 1 if name in fail_set else 0
        return m

    monkeypatch.setattr(subprocess, "run", sel_run)


def _stub_close(monkeypatch):
    """Stub close_issue; return True-appending call log."""
    called: list[bool] = []
    monkeypatch.setattr(
        classify_file, "close_issue",
        lambda _a: called.append(True),
    )
    return called


def _stub_create(monkeypatch, number=42):
    """Stub create_issue; return number-appending call log."""
    called: list[int] = []

    def fake(_args, _names):
        called.append(number)
        return number

    monkeypatch.setattr(classify_file, "create_issue", fake)
    return called


# ---- Multi-test batch processing -------------------------------------------


def test_processes_all_three_tests(tmp_path, monkeypatch):
    """Pipeline invokes classify_test for each of three tests."""
    body = (
        "TEST(S, Alpha) {\n}\n"
        "TEST(S, Beta) {\n}\n"
        "TEST(S, Gamma) {\n}\n"
    )
    log = _mock_run_ok(monkeypatch)
    _stub_close(monkeypatch)
    _run(_write_and_args(tmp_path, body))
    assert len(log) == 3


def test_each_call_has_distinct_test_name(tmp_path, monkeypatch):
    """Each subprocess call targets a different test name."""
    body = (
        "TEST(S, Alpha) {\n}\n"
        "TEST(S, Beta) {\n}\n"
    )
    log = _mock_run_ok(monkeypatch)
    _stub_close(monkeypatch)
    _run(_write_and_args(tmp_path, body))
    names = [c[c.index("--test") + 1] for c in log]
    assert names == ["Alpha", "Beta"]


def test_flags_propagated_to_subprocess(tmp_path, monkeypatch):
    """Optional flags are forwarded to classify_test calls."""
    log = _mock_run_ok(monkeypatch)
    _run(_write_and_args(tmp_path, "TEST(S, T) {\n}\n", dry_run=True))
    assert "--dry-run" in log[0]


def test_continues_after_first_failure(
    tmp_path, monkeypatch, capsys,
):
    """Pipeline processes all tests even when first fails."""
    body = (
        "TEST(S, Fail1) {\n}\n"
        "TEST(S, Pass1) {\n}\n"
        "TEST(S, Fail2) {\n}\n"
    )
    _mock_run_selective(monkeypatch, {"Fail1", "Fail2"})
    try:
        _run(_write_and_args(tmp_path, body))
    except SystemExit:
        pass
    assert "Processing test 2/3: Pass1" in capsys.readouterr().out


def test_summary_counts_correct(tmp_path, monkeypatch, capsys):
    """Summary shows correct success/failure counts."""
    body = (
        "TEST(S, A) {\n}\n"
        "TEST(S, B) {\n}\n"
        "TEST(S, C) {\n}\n"
    )
    _mock_run_selective(monkeypatch, {"B"})
    try:
        _run(_write_and_args(tmp_path, body))
    except SystemExit:
        pass
    assert "2/3 tests succeeded" in capsys.readouterr().out


def test_single_test_file(tmp_path, monkeypatch, capsys):
    """Single-test file succeeds without error."""
    _mock_run_ok(monkeypatch)
    _stub_close(monkeypatch)
    _run(_write_and_args(tmp_path, "TEST(S, Only) {\n}\n"))
    assert "1/1 tests succeeded" in capsys.readouterr().out


def test_closes_issue_after_all_pass(tmp_path, monkeypatch):
    """Pipeline closes the issue after all tests succeed."""
    _mock_run_ok(monkeypatch)
    log = _stub_close(monkeypatch)
    _run(_write_and_args(tmp_path, "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"))
    assert len(log) == 1


def test_create_issue_then_process(tmp_path, monkeypatch):
    """Pipeline creates issue then processes all tests."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    log = _mock_run_ok(monkeypatch)
    _stub_close(monkeypatch)
    _stub_create(monkeypatch, 55)
    _run(_write_and_args(
        tmp_path, body, issue=None, create_issue=True,
    ))
    assert len(log) == 2
