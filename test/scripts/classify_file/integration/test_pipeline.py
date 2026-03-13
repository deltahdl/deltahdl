"""Integration tests for the classify_file pipeline."""

import subprocess
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

from lib.python.test_fixtures.subprocess_stubs import (
    stub_subprocess_failure,
    stub_subprocess_success,
)


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


# ---- Batch processing via classify_tests ----------------------------------


def test_invokes_classify_tests_once(tmp_path, monkeypatch, cf):
    """Pipeline invokes classify_tests exactly once for all tests."""
    body = (
        "TEST(S, Alpha) {\n}\n"
        "TEST(S, Beta) {\n}\n"
        "TEST(S, Gamma) {\n}\n"
    )
    _stub_ensure(monkeypatch, cf)
    log = stub_subprocess_success(monkeypatch)
    _stub_close(monkeypatch, cf)
    getattr(cf, "_run")(_write_and_args(tmp_path, body))
    assert len(log) == 1


def test_tests_flag_contains_all_names(tmp_path, monkeypatch, cf):
    """The --tests flag includes all test names comma-separated."""
    body = (
        "TEST(S, Alpha) {\n}\n"
        "TEST(S, Beta) {\n}\n"
    )
    _stub_ensure(monkeypatch, cf)
    log = stub_subprocess_success(monkeypatch)
    _stub_close(monkeypatch, cf)
    getattr(cf, "_run")(_write_and_args(tmp_path, body))
    assert log[0][log[0].index("--tests") + 1] == "S.Alpha,S.Beta"


def test_flags_propagated_to_subprocess(tmp_path, monkeypatch, cf):
    """Optional flags are forwarded to classify_tests call."""
    _stub_ensure(monkeypatch, cf)
    log = stub_subprocess_success(monkeypatch)
    getattr(cf, "_run")(
        _write_and_args(tmp_path, "TEST(S, T) {\n}\n", dry_run=True),
    )
    assert "--dry-run" in log[0]


def test_exits_on_classify_tests_failure(tmp_path, monkeypatch, cf):
    """Pipeline exits when classify_tests returns non-zero."""
    _stub_ensure(monkeypatch, cf)
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        getattr(cf, "_run")(
            _write_and_args(tmp_path, "TEST(S, A) {\n}\n"),
        )


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
    """Pipeline closes the issue after classify_tests succeeds."""
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
    """Pipeline creates issue then invokes classify_tests once."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    log = stub_subprocess_success(monkeypatch)
    _stub_close(monkeypatch, cf)
    _stub_create(monkeypatch, cf, 55)
    getattr(cf, "_run")(_write_and_args(
        tmp_path, body, issue=None, create_issue=True,
    ))
    assert len(log) == 1


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
