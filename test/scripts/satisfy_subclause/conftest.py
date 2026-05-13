"""Shared fixtures and helpers for satisfy_subclause tests."""

from collections.abc import Callable
from pathlib import Path
from unittest.mock import MagicMock

import pytest

from lib.python.test_fixtures.subprocess_stubs import make_stub_completed


@pytest.fixture()
def stub_completed() -> Callable[..., MagicMock]:
    """Return a factory building stubbed ``CompletedProcess`` mocks."""
    return make_stub_completed


@pytest.fixture()
def make_lrm(tmp_path: Path) -> Path:
    """Create an empty placeholder LRM file and return its path."""
    lrm = tmp_path / "lrm.txt"
    lrm.write_text("")
    return lrm
