"""Shared fixtures for implement_subclause unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_ISC_PKG = SCRIPTS_DIR / "implement_subclause"


@pytest.fixture()
def isc(module_loader):
    """Load the implement_subclause module."""
    return module_loader(
        "implement_subclause",
        _ISC_PKG / "__init__.py",
    )


@pytest.fixture()
def _isc(request):
    """Order-only dep so submodule fixtures load after implement_subclause."""
    return request.getfixturevalue("isc")


@pytest.fixture()
def streaming(_isc, module_loader):
    """Load the implement_subclause.streaming submodule."""
    return module_loader(
        "implement_subclause.streaming",
        _ISC_PKG / "streaming.py",
    )
