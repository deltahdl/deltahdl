"""Shared fixtures for classify_test unit tests."""

from pathlib import Path

import pytest

SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"


@pytest.fixture()
def ct(module_loader):
    """Load the classify_test module."""
    return module_loader(
        "classify_test",
        SCRIPTS_DIR / "classify_test" / "__init__.py",
    )


@pytest.fixture()
def ct_git(_ct, module_loader):
    """Load the classify_test._git module."""
    return module_loader(
        "classify_test._git",
        SCRIPTS_DIR / "classify_test" / "_git.py",
    )


@pytest.fixture()
def ct_github(_ct, module_loader):
    """Load the classify_test._github module."""
    return module_loader(
        "classify_test._github",
        SCRIPTS_DIR / "classify_test" / "_github.py",
    )


@pytest.fixture()
def ct_output(_ct, module_loader):
    """Load the classify_test._output module."""
    return module_loader(
        "classify_test._output",
        SCRIPTS_DIR / "classify_test" / "_output.py",
    )


@pytest.fixture()
def ct_helpers(_ct, module_loader):
    """Load the classify_test.test_helpers module."""
    return module_loader(
        "classify_test.test_helpers",
        SCRIPTS_DIR / "classify_test" / "test_helpers.py",
    )
