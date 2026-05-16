"""Shared fixtures for lib.python.claude_cli_streaming tests.

The ``streaming`` fixture returns the imported module so test bodies
can reference attributes via a parameter name rather than a long
qualified path. The ``make_settings`` factory writes a deny-hook
settings file, parses it, and registers the temp file for cleanup
at fixture teardown.
"""

import json
import os
from collections.abc import Callable, Iterator
from types import ModuleType
from typing import Any

import pytest

from lib.python import claude_cli_streaming as _streaming


@pytest.fixture()
def streaming() -> ModuleType:
    """Return the lib.python.claude_cli_streaming module."""
    return _streaming


@pytest.fixture()
def make_settings() -> Iterator[Callable[[list[str]], dict[str, Any]]]:
    """Return a factory that writes settings, parses them, and cleans up.

    Each call writes a fresh temp file via ``write_deny_hook_settings``
    and registers it for cleanup at fixture teardown, so test bodies
    can stay one-assert without try/finally bookkeeping.
    """
    paths: list[str] = []

    def _make(patterns: list[str]) -> dict[str, Any]:
        path = _streaming.write_deny_hook_settings(patterns)
        paths.append(path)
        with open(path, encoding="utf-8") as handle:
            data: dict[str, Any] = json.load(handle)
        return data

    yield _make

    for path in paths:
        os.unlink(path)
