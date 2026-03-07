"""Shared fixtures for classify_test integration tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def ct(module_loader):
    """Load the classify_test module."""
    return module_loader(
        "classify_test",
        SCRIPTS_DIR / "classify_test" / "__init__.py",
    )
