"""Shared fixtures for implement_clauses unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def icls(module_loader):
    """Load the implement_clauses module."""
    return module_loader(
        "implement_clauses",
        SCRIPTS_DIR / "implement_clauses" / "__init__.py",
    )
