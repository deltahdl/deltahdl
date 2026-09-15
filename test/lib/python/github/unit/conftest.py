from collections.abc import Callable
from unittest.mock import MagicMock

import pytest

from lib.python.test_fixtures.subprocess_stubs import make_stub_completed


@pytest.fixture()
def stub_completed() -> Callable[..., MagicMock]:
    return make_stub_completed
