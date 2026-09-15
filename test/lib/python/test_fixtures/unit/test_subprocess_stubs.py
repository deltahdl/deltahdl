"""Tests for lib.python.test_fixtures.subprocess_stubs.

The stub stands in for a ``subprocess.run`` result in the suite that covers
``lib.python.github``, so what it carries decides what that suite concludes
about code that shells out. A stub reporting success where it meant to
report failure turns a test of an error path into a test of nothing, and
the suite it serves cannot notice: it is asserting about the module under
test, not about the stub. The claims are made here instead.
"""

from lib.python.test_fixtures.subprocess_stubs import make_stub_completed


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
