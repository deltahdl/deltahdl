"""Fixtures specific to run_sv_tests tests."""

from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

_PKG = Path(__file__).resolve().parents[3] / "scripts" / "run_sv_tests"


@pytest.fixture()
def rst(module_loader: Callable[[str, Path], ModuleType]) -> ModuleType:
    """Load the run_sv_tests module."""
    return module_loader("run_sv_tests", _PKG / "__init__.py")


@pytest.fixture()
def capture_run_cmd() -> Callable[[ModuleType, Callable[[], Any]], list[str]]:
    """Return a helper giving the command line a call asked subprocess to run.

    It lives here rather than in either test module because both need it: the
    cases over what the runner does with a corpus file read the command
    deltahdl was given, and the case over the corpus revision reads the command
    git was given.
    """
    def capture(module: ModuleType, call: Callable[[], Any]) -> list[str]:
        mock_result = MagicMock(returncode=0, stderr="")
        with patch.object(
            module.subprocess, "run", return_value=mock_result,
        ) as mock_run:
            call()
        cmd: list[str] = mock_run.call_args[0][0]
        return cmd

    return capture


@pytest.fixture()
def sv_test_tree(tmp_path: Path) -> Path:
    """Create a fake sv-tests directory tree with chapter dirs and .sv files.

    Returns the tmp_path containing:
      chapter-5/alpha.sv
      chapter-5/beta.sv
      chapter-6/gamma.sv
    """
    ch5 = tmp_path / "chapter-5"
    ch5.mkdir()
    (ch5 / "alpha.sv").write_text("module alpha; endmodule\n")
    (ch5 / "beta.sv").write_text("module beta; endmodule\n")

    ch6 = tmp_path / "chapter-6"
    ch6.mkdir()
    (ch6 / "gamma.sv").write_text("module gamma; endmodule\n")

    return tmp_path
