"""Shared fixtures for the cycle-set mutator unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_PKG = SCRIPTS_DIR / "satisfy_unsatisfied_subclause_set_with_satisfied_dependencies"


@pytest.fixture()
def sset(module_loader):
    """Load the cycle-set mutator module."""
    return module_loader(
        "satisfy_unsatisfied_subclause_set_with_satisfied_dependencies",
        _PKG / "__init__.py",
    )
