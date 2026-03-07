"""Shared fixtures for implement_clause tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent / "scripts"


@pytest.fixture()
def ic(module_loader):
    """Load the implement_clause module."""
    return module_loader(
        "implement_clause",
        SCRIPTS_DIR / "implement_clause" / "__init__.py",
    )


@pytest.fixture()
def _ic(request):
    """Order-only dependency so submodule fixtures load after implement_clause."""
    return request.getfixturevalue("ic")
