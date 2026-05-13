"""Shared fixtures for lib.github unit tests."""

from collections.abc import Callable
from unittest.mock import MagicMock

import pytest

from lib.python.test_fixtures.subprocess_stubs import make_stub_completed


@pytest.fixture()
def stub_completed() -> Callable[..., MagicMock]:
    """Return a factory building stubbed ``CompletedProcess`` mocks."""
    return make_stub_completed
