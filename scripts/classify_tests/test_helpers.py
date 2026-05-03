"""Shared test helpers for classify_tests unit and integration tests."""

from types import SimpleNamespace
from typing import Any

from lib.python.test_fixtures import make_classify_args


def make_args(**overrides: Any) -> SimpleNamespace:
    """Build args with classify_tests-specific defaults."""
    defaults: dict[str, Any] = {
        "tests": "S.A,S.B,S.C", "issue": None,
        "continue_session": False,
    }
    defaults.update(overrides)
    return make_classify_args(**defaults)
