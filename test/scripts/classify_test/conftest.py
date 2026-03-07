"""Shared fixtures for classify_test tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent / "scripts"


@pytest.fixture()
def ct(module_loader):
    """Load the classify_test module."""
    return module_loader(
        "classify_test",
        SCRIPTS_DIR / "classify_test" / "__init__.py",
    )


@pytest.fixture()
def _ct(module_loader):
    """Order-only dependency so submodule fixtures load after classify_test."""
    return module_loader(
        "classify_test",
        SCRIPTS_DIR / "classify_test" / "__init__.py",
    )
