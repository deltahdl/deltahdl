"""Shared fixtures for lib.python.claude_cli_streaming tests.

The ``streaming`` fixture returns the imported module so test bodies
can reference attributes via a parameter name rather than a long
qualified path.
"""

from types import ModuleType

import pytest

from lib.python import claude_cli_streaming as _streaming


@pytest.fixture()
def streaming() -> ModuleType:
    """Return the lib.python.claude_cli_streaming module."""
    return _streaming
