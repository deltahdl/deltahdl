"""Shared fixtures for classify_test unit tests."""

from pathlib import Path

import pytest

_SCRIPTS_DIR = Path(__file__).resolve().parent.parent.parent.parent.parent / "scripts"
_CT_PKG = _SCRIPTS_DIR / "classify_test"


@pytest.fixture()
def ct_git(_ct, module_loader):
    """Load the classify_test._git module."""
    return module_loader("classify_test._git", _CT_PKG / "_git.py")


@pytest.fixture()
def ct_github(_ct, module_loader):
    """Load the classify_test._github module."""
    return module_loader("classify_test._github", _CT_PKG / "_github.py")


@pytest.fixture()
def ct_output(_ct, module_loader):
    """Load the classify_test._output module."""
    return module_loader("classify_test._output", _CT_PKG / "_output.py")


@pytest.fixture()
def ct_helpers(_ct, module_loader):
    """Load the classify_test.test_helpers module."""
    return module_loader("classify_test.test_helpers", _CT_PKG / "test_helpers.py")
