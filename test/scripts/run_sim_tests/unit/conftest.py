"""Fixtures for run_sim_tests unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def rst(module_loader):
    """Load the run_sim_tests module."""
    return module_loader(
        "run_sim_tests",
        SCRIPTS_DIR / "run_sim_tests" / "__init__.py",
    )
