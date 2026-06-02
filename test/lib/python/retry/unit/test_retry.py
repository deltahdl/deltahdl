"""Tests for the shared transient-retry primitives.

The backoff/jitter mechanism was extracted from the gh CLI wrapper so the
Claude CLI streaming runner could reuse it without copy-pasting (which the
jscpd duplicate-code gate forbids). These tests pin the module's RNG and
stub ``time.sleep`` so the schedule is deterministic.
"""

import time

import pytest

from lib.python.retry import (
    DEFAULT_MAX_ATTEMPTS,
    _rng,
    contains_transient_marker,
    sleep_before_retry,
)


# ---------------------------------------------------------------------------
# contains_transient_marker
# ---------------------------------------------------------------------------


def test_contains_transient_marker_finds_substring() -> None:
    """A present marker is detected."""
    assert contains_transient_marker("the socket hang up", ("socket hang up",))


def test_contains_transient_marker_is_case_insensitive() -> None:
    """Matching ignores case on both sides."""
    assert contains_transient_marker("SOCKET HANG UP", ("socket hang up",))


def test_contains_transient_marker_absent_returns_false() -> None:
    """No marker present yields False."""
    assert contains_transient_marker("all good", ("socket hang up",)) is False


def test_contains_transient_marker_empty_substrings_returns_false() -> None:
    """An empty marker list never matches."""
    assert contains_transient_marker("anything", ()) is False


# ---------------------------------------------------------------------------
# sleep_before_retry
# ---------------------------------------------------------------------------


def _stub_sleep(monkeypatch: pytest.MonkeyPatch) -> list[float]:
    sleeps: list[float] = []
    monkeypatch.setattr(time, "sleep", sleeps.append)
    return sleeps


def test_sleep_before_retry_calls_sleep_once(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """One call results in exactly one time.sleep."""
    sleeps = _stub_sleep(monkeypatch)
    monkeypatch.setattr(_rng, "uniform", lambda _a, b: b)
    sleep_before_retry(0)
    assert len(sleeps) == 1


def test_sleep_before_retry_upper_bound_is_two_pow_attempt(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Jitter upper bound for attempt n is 2**n."""
    sleeps = _stub_sleep(monkeypatch)
    monkeypatch.setattr(_rng, "uniform", lambda _a, b: b)
    sleep_before_retry(3)
    assert sleeps == [8]


def test_sleep_before_retry_upper_bound_at_attempt_nine_is_two_pow_nine(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The top of the schedule (attempt 9) bounds jitter at 2**9 = 512."""
    sleeps = _stub_sleep(monkeypatch)
    monkeypatch.setattr(_rng, "uniform", lambda _a, b: b)
    sleep_before_retry(9)
    assert sleeps == [512]


def test_sleep_before_retry_lower_bound_is_zero(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Jitter lower bound is always zero."""
    sleeps = _stub_sleep(monkeypatch)
    monkeypatch.setattr(_rng, "uniform", lambda a, _b: a)
    sleep_before_retry(5)
    assert sleeps == [0]


# ---------------------------------------------------------------------------
# constants
# ---------------------------------------------------------------------------


def test_default_max_attempts_is_ten() -> None:
    """The shared attempt budget matches the gh wrapper's original 10."""
    assert DEFAULT_MAX_ATTEMPTS == 10
