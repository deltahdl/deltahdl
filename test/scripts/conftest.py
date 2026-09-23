import runpy
import stat
import subprocess
import sys
import textwrap
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


@pytest.fixture()
def calls_made_by_running_as_a_module(
    monkeypatch: pytest.MonkeyPatch,
) -> Callable[[ModuleType], list[str]]:
    def run(module: ModuleType) -> list[str]:
        calls: list[str] = []
        monkeypatch.setattr(module, "main", lambda: calls.append("main"))
        runpy.run_path(
            str(Path(module.__file__ or "").with_name("__main__.py")),
            run_name=f"{module.__name__}.__main__",
        )
        return calls

    return run


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
def run_runner_main() -> Callable[
    [str, Path, Path], subprocess.CompletedProcess[str]
]:
    def _run(
        package: str, test_dir: Path, binary: Path,
    ) -> subprocess.CompletedProcess[str]:
        code = textwrap.dedent(f"""\
            import importlib
            import sys
            from pathlib import Path
            sys.path[:0] = [{str(REPO_ROOT)!r}, {str(SCRIPTS_DIR)!r}]
            common = importlib.import_module("lib.python.run_tests_common")
            runner = importlib.import_module({package!r})
            runner.TEST_DIR = Path({str(test_dir)!r})
            common.BINARY = runner.BINARY = Path({str(binary)!r})
            runner.main()
        """)
        return subprocess.run(
            [sys.executable, "-c", code],
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )

    return _run


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
