"""Top-level conftest for classify_tests tests."""

from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import cast

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent / "scripts"


@pytest.fixture()
def cts(
    module_loader: Callable[[str, Path], ModuleType],
) -> ModuleType:
    """Load the classify_tests module."""
    return module_loader(
        "classify_tests",
        SCRIPTS_DIR / "classify_tests" / "__init__.py",
    )


@pytest.fixture()
def _cts(request: pytest.FixtureRequest) -> ModuleType:
    """Order-only dependency so submodule fixtures load after classify_tests."""
    return cast(ModuleType, request.getfixturevalue("cts"))
