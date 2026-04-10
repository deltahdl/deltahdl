"""Shared fixtures for implement_subclause unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def isc(module_loader):
    """Load the implement_subclause module."""
    return module_loader(
        "implement_subclause",
        SCRIPTS_DIR / "implement_subclause" / "__init__.py",
    )
