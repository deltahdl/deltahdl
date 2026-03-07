"""Unit-test conftest for classify_file."""

from pathlib import Path

import pytest

_SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_CF_PKG = _SCRIPTS_DIR / "classify_file"


@pytest.fixture()
def cf_helpers(_cf, module_loader):
    """Load the classify_file.test_helpers module."""
    return module_loader("classify_file.test_helpers", _CF_PKG / "test_helpers.py")
