"""Shared fixtures for is_subclause_satisfied unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_ISS_PKG = SCRIPTS_DIR / "is_subclause_satisfied"


@pytest.fixture()
def iss(module_loader):
    """Load the is_subclause_satisfied module."""
    return module_loader(
        "is_subclause_satisfied",
        _ISS_PKG / "__init__.py",
    )
