"""Shared fixtures for scripts test suite."""

import stat
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

# Add scripts/ to sys.path so we can import the modules under test.
SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))


def _shell_quote(s):
    """Quote a string for use in a shell script."""
    return "'" + s.replace("'", "'\\''") + "'"


@pytest.fixture()
def stub_binary(tmp_path):
    """Create a stub deltahdl binary for testing.

    Returns a factory function: call it with (exit_code, stdout, stderr)
    to get a Path to an executable shell script that behaves accordingly.
    """

    def _make(exit_code=0, stdout="", stderr=""):
        binary = tmp_path / "deltahdl"
        lines = ["#!/usr/bin/env bash"]
        if stdout:
            lines.append(f'printf "%s" {_shell_quote(stdout)}')
        if stderr:
            lines.append(f'printf "%s" {_shell_quote(stderr)} >&2')
        lines.append(f"exit {exit_code}")
        binary.write_text("\n".join(lines) + "\n")
        binary.chmod(binary.stat().st_mode | stat.S_IEXEC)
        return binary

    return _make


@pytest.fixture()
def patch_binary(request):
    """Patch test_common.BINARY to point at a stub binary.

    Returns a factory: call it with (exit_code, stdout, stderr) and the
    patch is applied for the duration of the test.
    """
    make_stub = request.getfixturevalue("stub_binary")
    patches = []

    def _make(exit_code=0, stdout="", stderr=""):
        binary = make_stub(exit_code, stdout, stderr)
        p = patch("test_common.BINARY", binary)
        p.start()
        patches.append(p)
        return binary

    yield _make

    for p in patches:
        p.stop()


@pytest.fixture()
def get_exit_code():
    """Return a helper that calls func() and captures its SystemExit code.

    Returns None if func() returns normally (no SystemExit raised).
    """

    def _capture(func):
        try:
            func()
        except SystemExit as exc:
            return exc.code
        return None

    return _capture
