import stat
import sys
from collections.abc import Callable, Iterator
from pathlib import Path
from types import ModuleType
from typing import Any, cast
from unittest.mock import patch

import pytest

from lib.python.test_utils import load_module_from_path


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))


@pytest.fixture()
def module_loader() -> Callable[[str, Path], ModuleType]:
    return load_module_from_path


def _shell_quote(s: str) -> str:
    return "'" + s.replace("'", "'\\''") + "'"


@pytest.fixture()
def stub_binary(tmp_path: Path) -> Callable[..., Path]:
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
    def _capture(func: Callable[[], object]) -> int | str | None:
        try:
            func()
        except SystemExit as exc:
            return exc.code
        return None

    return _capture
