"""Shared fixtures for scripts test suite."""

import os
import stat
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

# Add scripts/ to sys.path so we can import the modules under test.
SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent / "scripts"
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))


@pytest.fixture()
def stub_binary(tmp_path):
    """Create a stub deltahdl binary for testing.

    Returns a factory function: call it with (exit_code, stdout, stderr)
    to get a Path to an executable shell script that behaves accordingly.
    The returned path is also patched into test_common.BINARY.
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
def patch_binary(stub_binary):
    """Patch test_common.BINARY to point at a stub binary.

    Returns a factory: call it with (exit_code, stdout, stderr) and the
    patch is applied for the duration of the test.
    """
    patches = []

    def _make(exit_code=0, stdout="", stderr=""):
        binary = stub_binary(exit_code, stdout, stderr)
        p = patch("test_common.BINARY", binary)
        p.start()
        patches.append(p)
        return binary

    yield _make

    for p in patches:
        p.stop()


def _shell_quote(s):
    """Quote a string for use in a shell script."""
    return "'" + s.replace("'", "'\\''") + "'"
