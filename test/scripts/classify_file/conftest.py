"""Top-level conftest for classify_file tests."""

from collections.abc import Callable
from pathlib import Path
from types import ModuleType
from typing import cast

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent / "scripts"


@pytest.fixture()
def cf(
    module_loader: Callable[[str, Path], ModuleType],
) -> ModuleType:
    """Load the classify_file module."""
    return module_loader(
        "classify_file",
        SCRIPTS_DIR / "classify_file" / "__init__.py",
    )


@pytest.fixture()
def _cf(request: pytest.FixtureRequest) -> ModuleType:
    """Order-only dependency so submodule fixtures load after classify_file."""
    return cast(ModuleType, request.getfixturevalue("cf"))
