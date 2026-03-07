"""Integration tests for the classify_file pipeline."""

import subprocess
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

from lib.python.test_fixtures.subprocess_stubs import stub_subprocess_success


# ---- Helpers ---------------------------------------------------------------


_ARGS_DEFAULTS = {
    "issue": 99, "create_issue": False,
    "organization": "testorg", "repo": "testrepo",
    "dry_run": False, "no_commit": False, "max_lines": 1000,
}


def _pipeline_args(tmp_path: Path, **overrides: object) -> SimpleNamespace:
    """Build args pointing at test_input.cpp inside *tmp_path*."""
    result = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path),
        "lrm": str(tmp_path / "lrm.txt"),
        **_ARGS_DEFAULTS, **overrides,
    }
    return SimpleNamespace(**result)


def _write_and_args(tmp_path: Path, body: str, **overrides: object) -> SimpleNamespace:
    """Write test_input.cpp and return args for _run."""
    (tmp_path / "test_input.cpp").write_text(
        body, encoding="utf-8",
    )
    return _pipeline_args(tmp_path, **overrides)


def _mock_run_selective(monkeypatch: pytest.MonkeyPatch, fail_set: set[str]) -> None:
    """Stub subprocess.run to fail only for names in *fail_set*."""

    def sel_run(cmd: list[str], **_kw: object) -> MagicMock:
        m = MagicMock()
        m.stdout, m.stderr = "", ""
        name = cmd[cmd.index("--test") + 1]
        m.returncode = 1 if name in fail_set else 0
        return m

    monkeypatch.setattr(subprocess, "run", sel_run)


def _stub_close(monkeypatch: pytest.MonkeyPatch, cf) -> list[bool]:
    """Stub close_issue; return True-appending call log."""
    called: list[bool] = []
    monkeypatch.setattr(
        cf, "close_issue",
        lambda _o, _r, _i, _reason: called.append(True),
    )
    return called


def _stub_create(monkeypatch: pytest.MonkeyPatch, cf, number: int = 42) -> list[int]:
    """Stub create_issue; return number-appending call log."""
    called: list[int] = []

    def fake(_args: object, _names: object) -> int:
        called.append(number)
        return number

    monkeypatch.setattr(cf, "create_issue", fake)
    return called


def _stub_ensure(monkeypatch: pytest.MonkeyPatch, cf) -> list[bool]:
    """Stub sync_issue_rows; return call log."""
    called: list[bool] = []

    def fake(_a: object, _n: object) -> set[str]:
        called.append(True)
        return set()

    monkeypatch.setattr(cf, "sync_issue_rows", fake)
    return called


# ---- Multi-test batch processing -------------------------------------------


def test_processes_all_three_tests(tmp_path, monkeypatch, cf):
    """Pipeline invokes classify_test for each of three tests."""
    body = (
        "TEST(S, Alpha) {\n}\n"
        "TEST(S, Beta) {\n}\n"
        "TEST(S, Gamma) {\n}\n"
    )
    _stub_ensure(monkeypatch, cf)
    log = stub_subprocess_success(monkeypatch)
    _stub_close(monkeypatch, cf)
    getattr(cf, "_run")(_write_and_args(tmp_path, body))
    assert len(log) == 3


def test_each_call_has_distinct_test_name(tmp_path, monkeypatch, cf):
    """Each subprocess call targets a different test name."""
    body = (
        "TEST(S, Alpha) {\n}\n"
        "TEST(S, Beta) {\n}\n"
    )
    _stub_ensure(monkeypatch, cf)
    log = stub_subprocess_success(monkeypatch)
    _stub_close(monkeypatch, cf)
    getattr(cf, "_run")(_write_and_args(tmp_path, body))
    names = [c[c.index("--test") + 1] for c in log]
    assert names == ["Alpha", "Beta"]


def test_flags_propagated_to_subprocess(tmp_path, monkeypatch, cf):
    """Optional flags are forwarded to classify_test calls."""
    _stub_ensure(monkeypatch, cf)
    log = stub_subprocess_success(monkeypatch)
    getattr(cf, "_run")(
        _write_and_args(tmp_path, "TEST(S, T) {\n}\n", dry_run=True),
    )
    assert "--dry-run" in log[0]


def test_stops_after_first_failure(
    tmp_path, monkeypatch, cf, capsys,
):
    """Pipeline stops immediately when first test fails."""
    body = (
        "TEST(S, Fail1) {\n}\n"
        "TEST(S, Pass1) {\n}\n"
    )
    _stub_ensure(monkeypatch, cf)
    _mock_run_selective(monkeypatch, {"Fail1"})
    try:
        getattr(cf, "_run")(_write_and_args(tmp_path, body))
    except SystemExit:
        pass
    assert "Pass1" not in capsys.readouterr().out


def test_single_test_file(tmp_path, monkeypatch, cf):
    """Single-test file succeeds without error."""
    _stub_ensure(monkeypatch, cf)
    log = stub_subprocess_success(monkeypatch)
    _stub_close(monkeypatch, cf)
    getattr(cf, "_run")(
        _write_and_args(tmp_path, "TEST(S, Only) {\n}\n"),
    )
    assert len(log) == 1


def test_closes_issue_after_all_pass(tmp_path, monkeypatch, cf):
    """Pipeline closes the issue after all tests succeed."""
    _stub_ensure(monkeypatch, cf)
    stub_subprocess_success(monkeypatch)
    log = _stub_close(monkeypatch, cf)
    getattr(cf, "_run")(
        _write_and_args(
            tmp_path, "TEST(S, A) {\n}\nTEST(S, B) {\n}\n",
        ),
    )
    assert len(log) == 1


def test_create_issue_then_process(tmp_path, monkeypatch, cf):
    """Pipeline creates issue then processes all tests."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    log = stub_subprocess_success(monkeypatch)
    _stub_close(monkeypatch, cf)
    _stub_create(monkeypatch, cf, 55)
    getattr(cf, "_run")(_write_and_args(
        tmp_path, body, issue=None, create_issue=True,
    ))
    assert len(log) == 2


# ---- sync_issue_rows integration ------------------------------------------


def _sync_order_log(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch, cf,
) -> list[str]:
    """Run pipeline recording sync vs subprocess call order."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    order: list[str] = []
    def fake_sync(_a: object, _n: object) -> set[str]:
        order.append("sync")
        return set()

    monkeypatch.setattr(cf, "sync_issue_rows", fake_sync)

    def log_run(_cmd, **_kw):
        order.append("subprocess")
        m = MagicMock()
        m.returncode, m.stdout, m.stderr = 0, "", ""
        return m

    monkeypatch.setattr(subprocess, "run", log_run)
    _stub_close(monkeypatch, cf)
    getattr(cf, "_run")(_write_and_args(tmp_path, body))
    return order


def test_sync_issue_rows_runs_first(
    tmp_path, monkeypatch, cf,
):
    """Pipeline calls sync_issue_rows before subprocess calls."""
    order = _sync_order_log(tmp_path, monkeypatch, cf)
    assert order[0] == "sync"


def test_subprocess_runs_after_sync(
    tmp_path, monkeypatch, cf,
):
    """All calls after sync_issue_rows are subprocess calls."""
    order = _sync_order_log(tmp_path, monkeypatch, cf)
    assert all(e == "subprocess" for e in order[1:])
