"""Shared fixtures for classify_test tests."""

from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import cast

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent / "scripts"


@pytest.fixture()
def ct(
    module_loader: Callable[[str, Path], ModuleType],
) -> ModuleType:
    """Load the classify_test module."""
    return module_loader(
        "classify_test",
        SCRIPTS_DIR / "classify_test" / "__init__.py",
    )


@pytest.fixture()
def _ct(request: pytest.FixtureRequest) -> ModuleType:
    """Order-only dependency so submodule fixtures load after classify_test."""
    return cast(ModuleType, request.getfixturevalue("ct"))
