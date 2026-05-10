"""Shared fixtures and helpers for satisfy_subclause tests."""

from collections.abc import Callable
from pathlib import Path
from unittest.mock import MagicMock

import pytest


@pytest.fixture()
def stub_completed() -> Callable[..., MagicMock]:
    """Return a factory building stubbed ``CompletedProcess`` mocks."""

    def _make(
        stdout: str = "", returncode: int = 0, stderr: str = "",
    ) -> MagicMock:
        completed = MagicMock()
        completed.returncode = returncode
        completed.stdout = stdout
        completed.stderr = stderr
        return completed

    return _make


@pytest.fixture()
def make_lrm(tmp_path: Path) -> Path:
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm
