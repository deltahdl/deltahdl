import importlib
import os
from collections.abc import Iterator
from types import ModuleType
from unittest.mock import patch

import pytest

from lib.python import run_tests_common


@pytest.fixture()
def reload_no_color() -> Iterator[ModuleType]:
    env = os.environ.copy()
    env["NO_COLOR"] = "1"
    env.pop("CI", None)
    with patch.dict(os.environ, env, clear=True):
        yield importlib.reload(run_tests_common)


@pytest.fixture()
def reload_with_colors() -> Iterator[ModuleType]:
    env = os.environ.copy()
    env.pop("NO_COLOR", None)
    env["CI"] = "true"
    with patch.dict(os.environ, env, clear=True), \
         patch("sys.stdout") as mock_stdout:
        mock_stdout.isatty.return_value = True
        yield importlib.reload(run_tests_common)
