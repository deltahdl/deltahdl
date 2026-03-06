"""Fixtures for run_sv_tests unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def rst(module_loader):
    """Load the run_sv_tests module."""
    return module_loader(
        "run_sv_tests",
        SCRIPTS_DIR / "run_sv_tests" / "__init__.py",
    )
