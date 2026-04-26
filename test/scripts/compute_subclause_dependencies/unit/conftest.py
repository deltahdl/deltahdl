"""Shared fixtures for compute_subclause_dependencies unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_CSD_PKG = SCRIPTS_DIR / "compute_subclause_dependencies"


@pytest.fixture()
def csd(module_loader):
    """Load the compute_subclause_dependencies module."""
    return module_loader(
        "compute_subclause_dependencies",
        _CSD_PKG / "__init__.py",
    )
