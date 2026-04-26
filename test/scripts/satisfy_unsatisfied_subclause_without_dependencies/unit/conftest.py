"""Shared fixtures for satisfy_unsatisfied_subclause_without_dependencies unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_PKG = SCRIPTS_DIR / "satisfy_unsatisfied_subclause_without_dependencies"


@pytest.fixture()
def sus(module_loader):
    """Load the satisfy_unsatisfied_subclause_without_dependencies module."""
    return module_loader(
        "satisfy_unsatisfied_subclause_without_dependencies",
        _PKG / "__init__.py",
    )
