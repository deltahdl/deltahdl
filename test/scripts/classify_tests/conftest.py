"""Top-level conftest for classify_tests tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent / "scripts"


@pytest.fixture()
def cts(module_loader):
    """Load the classify_tests module."""
    return module_loader(
        "classify_tests",
        SCRIPTS_DIR / "classify_tests" / "__init__.py",
    )


@pytest.fixture()
def _cts(request):
    """Order-only dependency so submodule fixtures load after classify_tests."""
    return request.getfixturevalue("cts")
