"""Shared fixtures for implement_subclause unit tests."""

from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def isc(module_loader):
    """Load the implement_subclause module."""
    return module_loader(
        "implement_subclause",
        SCRIPTS_DIR / "implement_subclause" / "__init__.py",
    )


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
