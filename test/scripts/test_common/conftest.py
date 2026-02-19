"""Fixtures specific to test_common tests."""

import importlib
import os
from unittest.mock import patch

import pytest

from lib import test_common


@pytest.fixture()
def reload_no_color():
    """Reload test_common with NO_COLOR=1 and return the reloaded module."""
    env = os.environ.copy()
    env["NO_COLOR"] = "1"
    env.pop("CI", None)
    with patch.dict(os.environ, env, clear=True):
        yield importlib.reload(test_common)


@pytest.fixture()
def reload_with_colors():
    """Reload test_common with CI=true on a tty and return the module."""
    env = os.environ.copy()
    env.pop("NO_COLOR", None)
    env["CI"] = "true"
    with patch.dict(os.environ, env, clear=True), \
         patch("sys.stdout") as mock_stdout:
        mock_stdout.isatty.return_value = True
        yield importlib.reload(test_common)
