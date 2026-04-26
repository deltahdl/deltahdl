"""Shared fixtures for satisfy_unsatisfied_subclause unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_PKG = SCRIPTS_DIR / "satisfy_unsatisfied_subclause"


@pytest.fixture()
def sus(module_loader):
    """Load the satisfy_unsatisfied_subclause module."""
    return module_loader(
        "satisfy_unsatisfied_subclause",
        _PKG / "__init__.py",
    )
