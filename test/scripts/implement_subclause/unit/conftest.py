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
def run_ok():
    """Patch run_claude_cli with a successful mock result."""
    with patch("implement_subclause.run_claude_cli") as mock_run:
        mock_run.return_value = MagicMock(
            returncode=0,
            stdout='{"result":"done"}',
            stderr="",
        )
        yield mock_run
