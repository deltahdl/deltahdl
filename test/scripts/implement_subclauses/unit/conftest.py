"""Shared fixtures for implement_subclauses unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def iscs(module_loader):
    """Load the implement_subclauses module."""
    return module_loader(
        "implement_subclauses",
        SCRIPTS_DIR / "implement_subclauses" / "__init__.py",
    )
