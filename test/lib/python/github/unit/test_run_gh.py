"""Tests for the _is_transient classifier and _run_gh retry helper.

Covers the bounded exponential-backoff retry layer added to the gh CLI
wrapper after a production timeout (``dial tcp ... i/o timeout``) crashed
the satisfy_subclauses orchestrator mid-recursion.
"""

import subprocess
import time
from typing import Any

import pytest

from lib.python.github import _is_transient, _rng, _run_gh


# ---------------------------------------------------------------------------
# Phase A — _is_transient classifier
# ---------------------------------------------------------------------------


_PROD_INCIDENT_STDERR = (
    "Post \"https://api.github.com/graphql\":"
    " dial tcp 140.82.114.5:443: i/o timeout"
)


@pytest.mark.parametrize("stderr", [
    _PROD_INCIDENT_STDERR,
    "dial tcp 1.2.3.4:443: some error",
    "connection refused",
    "connection reset by peer",
    "unexpected EOF",
    "You have exceeded a secondary rate limit",
    "HTTP 502",
    "HTTP 503",
    "HTTP 504",
    "Bad Gateway",
    "Service Unavailable",
    "Gateway Timeout",
    "Temporary failure in name resolution",
    "I/O TIMEOUT",
])
def test_is_transient_classifies_transient_stderr_as_true(stderr: str) -> None:
    """Each transport-layer pattern is recognised as transient."""
    assert _is_transient(1, stderr) is True


@pytest.mark.parametrize("stderr", [
    "",
    "warning: variable redefined",
    "HTTP 404: Not Found",
    "HTTP 401: Unauthorized",
    "HTTP 403: Forbidden",
    "HTTP 422: Unprocessable Entity",
    "Bad credentials",
    "Validation Failed",
])
def test_is_transient_classifies_non_transient_stderr_as_false(
    stderr: str,
) -> None:
    """Logic errors and empty stderr never trigger a retry."""
    assert _is_transient(1, stderr) is False


def test_is_transient_returns_false_on_returncode_zero() -> None:
    """Success exit codes are never transient regardless of stderr."""
    assert _is_transient(0, "i/o timeout") is False


# ---------------------------------------------------------------------------
# Phase B — _run_gh retry helper
# ---------------------------------------------------------------------------


def _stub_sleep(monkeypatch: pytest.MonkeyPatch) -> list[float]:
    sleeps: list[float] = []
    monkeypatch.setattr(time, "sleep", sleeps.append)
    return sleeps


def _pin_jitter(monkeypatch: pytest.MonkeyPatch) -> None:
    """Pin jitter to its upper bound so backoff is deterministic."""
    monkeypatch.setattr(_rng, "uniform", lambda _a, b: b)


def _completed(
    returncode: int = 0, stderr: str = "",
) -> subprocess.CompletedProcess[str]:
    return subprocess.CompletedProcess(
        args=[], returncode=returncode, stdout="", stderr=stderr,
    )


def _stub_run(
    monkeypatch: pytest.MonkeyPatch,
    sequence: list[subprocess.CompletedProcess[str]],
) -> list[list[str]]:
    """Stub subprocess.run to consume *sequence* in order; capture argv list."""
    calls: list[list[str]] = []

    def fake_run(cmd: list[str], **_kw: Any) -> subprocess.CompletedProcess[str]:
        calls.append(cmd)
        return sequence.pop(0) if len(sequence) > 1 else sequence[0]

    monkeypatch.setattr(subprocess, "run", fake_run)
    return calls


def test_run_gh_returns_success_returncode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Successful first attempt returns returncode 0."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    _stub_run(monkeypatch, [_completed(returncode=0)])
    assert _run_gh(["gh", "api", "x"]).returncode == 0


def test_run_gh_makes_one_call_on_success(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Successful first attempt does not retry."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    calls = _stub_run(monkeypatch, [_completed(returncode=0)])
    _run_gh(["gh", "api", "x"])
    assert len(calls) == 1


def test_run_gh_does_not_sleep_on_success(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Successful first attempt does not call time.sleep."""
    sleeps = _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    _stub_run(monkeypatch, [_completed(returncode=0)])
    _run_gh(["gh", "api", "x"])
    assert not sleeps


def test_run_gh_returns_permanent_failure_returncode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """HTTP 404 returns immediately so the caller's sys.exit branch fires."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    _stub_run(monkeypatch, [_completed(returncode=1, stderr="HTTP 404")])
    assert _run_gh(["gh", "api", "x"]).returncode == 1


def test_run_gh_makes_one_call_on_permanent_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A non-transient failure is not retried."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    calls = _stub_run(
        monkeypatch, [_completed(returncode=1, stderr="HTTP 404")],
    )
    _run_gh(["gh", "api", "x"])
    assert len(calls) == 1


def test_run_gh_does_not_sleep_on_permanent_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A non-transient failure does not call time.sleep."""
    sleeps = _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    _stub_run(monkeypatch, [_completed(returncode=1, stderr="HTTP 404")])
    _run_gh(["gh", "api", "x"])
    assert not sleeps


def test_run_gh_recovers_from_one_transient_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Regression test for the prod incident: one i/o timeout, then success."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    _stub_run(monkeypatch, [
        _completed(returncode=1, stderr="dial tcp 1.2.3.4:443: i/o timeout"),
        _completed(returncode=0),
    ])
    assert _run_gh(["gh", "api", "x"]).returncode == 0


def test_run_gh_makes_two_calls_when_retrying_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """One transient failure → one retry → two total subprocess.run calls."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    calls = _stub_run(monkeypatch, [
        _completed(returncode=1, stderr="i/o timeout"),
        _completed(returncode=0),
    ])
    _run_gh(["gh", "api", "x"])
    assert len(calls) == 2


def test_run_gh_sleeps_once_when_retrying_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """One transient failure causes exactly one sleep, with delay = 1.0."""
    sleeps = _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    _stub_run(monkeypatch, [
        _completed(returncode=1, stderr="i/o timeout"),
        _completed(returncode=0),
    ])
    _run_gh(["gh", "api", "x"])
    assert sleeps == [1.0]


def test_run_gh_exhausts_retries_returning_failure_returncode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """After MAX_ATTEMPTS transient failures, last failure returncode is returned."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    _stub_run(monkeypatch, [_completed(returncode=1, stderr="i/o timeout")])
    assert _run_gh(["gh", "api", "x"]).returncode == 1


def test_run_gh_exhausts_retries_with_ten_calls(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Persistent transient failure produces exactly _MAX_ATTEMPTS calls."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    calls = _stub_run(
        monkeypatch, [_completed(returncode=1, stderr="i/o timeout")],
    )
    _run_gh(["gh", "api", "x"])
    assert len(calls) == 10


def test_run_gh_backoff_delays_escalate(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Pinned jitter yields the exact escalating schedule 1..256."""
    sleeps = _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    _stub_run(monkeypatch, [_completed(returncode=1, stderr="i/o timeout")])
    _run_gh(["gh", "api", "x"])
    assert sleeps == [1, 2, 4, 8, 16, 32, 64, 128, 256]


def _capture_subprocess_kwargs(
    monkeypatch: pytest.MonkeyPatch,
) -> dict[str, Any]:
    """Stub subprocess.run as success; return a dict populated with its kwargs."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    captured: dict[str, Any] = {}

    def fake_run(_cmd: list[str], **kwargs: Any) -> subprocess.CompletedProcess[str]:
        captured.update(kwargs)
        return _completed(returncode=0)

    monkeypatch.setattr(subprocess, "run", fake_run)
    return captured


def test_run_gh_passes_stdin_text_as_subprocess_input(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """stdin_text= is forwarded to subprocess.run as input=."""
    captured = _capture_subprocess_kwargs(monkeypatch)
    _run_gh(["gh", "api", "x"], stdin_text="payload")
    assert captured.get("input") == "payload"


def test_run_gh_uses_capture_output(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """capture_output=True is always passed to subprocess.run."""
    captured = _capture_subprocess_kwargs(monkeypatch)
    _run_gh(["gh", "api", "x"])
    assert captured["capture_output"] is True


def test_run_gh_uses_text_mode(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """text=True is always passed to subprocess.run."""
    captured = _capture_subprocess_kwargs(monkeypatch)
    _run_gh(["gh", "api", "x"])
    assert captured["text"] is True


def test_run_gh_stops_retrying_when_transient_becomes_permanent(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Transient on attempt 1 then 404 on attempt 2 exits via classifier."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    calls = _stub_run(monkeypatch, [
        _completed(returncode=1, stderr="i/o timeout"),
        _completed(returncode=1, stderr="HTTP 404"),
    ])
    _run_gh(["gh", "api", "x"])
    assert len(calls) == 2


def test_run_gh_returns_final_permanent_stderr_after_one_retry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The second (permanent) result is the one returned to the caller."""
    _stub_sleep(monkeypatch)
    _pin_jitter(monkeypatch)
    _stub_run(monkeypatch, [
        _completed(returncode=1, stderr="i/o timeout"),
        _completed(returncode=1, stderr="HTTP 404"),
    ])
    assert _run_gh(["gh", "api", "x"]).stderr == "HTTP 404"
