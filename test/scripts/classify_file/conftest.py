"""Top-level conftest for classify_file tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent / "scripts"


@pytest.fixture()
def cf(module_loader):
    """Load the classify_file module."""
    return module_loader(
        "classify_file",
        SCRIPTS_DIR / "classify_file" / "__init__.py",
    )


@pytest.fixture()
def _cf(request):
    """Order-only dependency so submodule fixtures load after classify_file."""
    return request.getfixturevalue("cf")
