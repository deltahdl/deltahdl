"""Shared fixtures for satisfy_subclause unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_PKG = SCRIPTS_DIR / "satisfy_subclause"


@pytest.fixture()
def ssc(module_loader):
    """Load the satisfy_subclause module."""
    return module_loader(
        "satisfy_subclause",
        _PKG / "__init__.py",
    )
