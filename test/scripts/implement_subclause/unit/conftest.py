"""Shared fixtures for implement_subclause unit tests."""

from unittest.mock import MagicMock, patch

import pytest


@pytest.fixture()
def popen_ok():
    """Patch subprocess.Popen with a successful mock process."""
    with patch("implement_subclause.subprocess.Popen") as mock_popen:
        proc = MagicMock()
        proc.communicate.return_value = (None, None)
        proc.returncode = 0
        proc.__enter__ = MagicMock(return_value=proc)
        proc.__exit__ = MagicMock(return_value=False)
        mock_popen.return_value = proc
        yield mock_popen
