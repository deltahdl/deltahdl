"""Shared fixtures for satisfy_unsatisfied_subclause_with_satisfied_dependencies unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_PKG = SCRIPTS_DIR / "satisfy_unsatisfied_subclause_with_satisfied_dependencies"


@pytest.fixture()
def swd(module_loader):
    """Load the satisfy_unsatisfied_subclause_with_satisfied_dependencies module."""
    return module_loader(
        "satisfy_unsatisfied_subclause_with_satisfied_dependencies",
        _PKG / "__init__.py",
    )
