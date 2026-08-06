"""Tests for lib.python.test_fixtures.subprocess_stubs.

These stubs stand in for ``subprocess.run`` in the suites that cover
``lib.python.git`` and ``lib.python.github``, so what they return decides
what those suites conclude about code that shells out. A stub reporting
success where it meant to report failure turns a test of an error path
into a test of nothing, and the suite it serves cannot notice: it is
asserting about the module under test, not about the stub. The claims are
made here instead.
"""

import subprocess

import pytest

from lib.python.test_fixtures.subprocess_stubs import (
    make_stub_completed,
    stub_subprocess_failure,
    stub_subprocess_success,
)


def test_make_stub_completed_defaults_to_success() -> None:
    """An unqualified stub stands for a command that worked."""
    assert make_stub_completed().returncode == 0


def test_make_stub_completed_carries_stdout() -> None:
    """Output handed in comes back on the stub."""
    assert make_stub_completed(stdout="out").stdout == "out"


def test_make_stub_completed_carries_stderr() -> None:
    """Error text handed in comes back on the stub."""
    assert make_stub_completed(stderr="bad").stderr == "bad"


def test_make_stub_completed_carries_returncode() -> None:
    """A non-zero code handed in comes back on the stub."""
    assert make_stub_completed(returncode=2).returncode == 2


def test_stub_subprocess_success_reports_success(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The patched ``subprocess.run`` answers zero, so callers take the
    success path.
    """
    stub_subprocess_success(monkeypatch)
    assert subprocess.run(["true"], check=False).returncode == 0


def test_stub_subprocess_success_captures_the_command(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The returned list records what each call asked to run."""
    captured = stub_subprocess_success(monkeypatch)
    subprocess.run(["gh", "issue", "list"], check=False)
    assert captured == [["gh", "issue", "list"]]


def test_stub_subprocess_success_captures_every_call(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A second call appends rather than replacing the first."""
    captured = stub_subprocess_success(monkeypatch)
    subprocess.run(["one"], check=False)
    subprocess.run(["two"], check=False)
    assert captured == [["one"], ["two"]]


def test_stub_subprocess_failure_reports_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """The patched ``subprocess.run`` answers non-zero, which is the whole
    point of the stub: a test of an error path is only testing one while
    this holds.
    """
    stub_subprocess_failure(monkeypatch)
    assert subprocess.run(["false"], check=False).returncode == 1


def test_stub_subprocess_failure_supplies_stderr(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """A caller printing the failure has something to print."""
    stub_subprocess_failure(monkeypatch)
    assert subprocess.run(["false"], check=False).stderr == "error"
