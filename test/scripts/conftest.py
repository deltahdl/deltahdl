"""Shared fixtures for scripts test suite."""

import stat
import sys
from collections.abc import Callable, Iterator
from pathlib import Path
from types import ModuleType
from typing import Any, cast
from unittest.mock import patch

import pytest

from lib.python.test_utils import load_module_from_path



# Add repo root (for lib/) and scripts/ to sys.path so we can import
# the modules under test.
REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))


@pytest.fixture()
def module_loader() -> Callable[[str, Path], ModuleType]:
    """Return load_module_from_path for dynamically loading modules."""
    return load_module_from_path


def _shell_quote(s: str) -> str:
    """Quote a string for use in a shell script."""
    return "'" + s.replace("'", "'\\''") + "'"


@pytest.fixture()
def stub_binary(tmp_path: Path) -> Callable[..., Path]:
    """Create a stub deltahdl binary for testing.

    Returns a factory function: call it with (exit_code, stdout, stderr)
    to get a Path to an executable shell script that behaves accordingly.
    """

    def _make(
        exit_code: int = 0, stdout: str = "", stderr: str = "",
    ) -> Path:
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
def patch_binary(
    request: pytest.FixtureRequest,
) -> Iterator[Callable[..., Path]]:
    """Patch lib.python.run_tests_common.BINARY to point at a stub binary.

    Returns a factory: call it with (exit_code, stdout, stderr) and the
    patch is applied for the duration of the test.
    """
    make_stub = cast(
        Callable[..., Path], request.getfixturevalue("stub_binary"),
    )
    patches: list[Any] = []

    def _make(
        exit_code: int = 0, stdout: str = "", stderr: str = "",
    ) -> Path:
        binary = make_stub(exit_code, stdout, stderr)
        p = patch("lib.python.run_tests_common.BINARY", binary)
        p.start()
        patches.append(p)
        return binary

    yield _make

    for p in patches:
        p.stop()


@pytest.fixture()
def get_exit_code() -> Callable[[Callable[[], object]], int | str | None]:
    """Return a helper that calls func() and captures its SystemExit code.

    Returns None if func() returns normally (no SystemExit raised).
    """

    def _capture(func: Callable[[], object]) -> int | str | None:
        try:
            func()
        except SystemExit as exc:
            return exc.code
        return None

    return _capture
