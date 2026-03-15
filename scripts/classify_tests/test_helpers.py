"""Shared test helpers for classify_tests unit and integration tests."""

from lib.python.test_fixtures import make_classify_args


def make_args(**overrides):
    """Build args with classify_tests-specific defaults."""
    defaults = {
        "tests": "S.A,S.B,S.C", "issue": None,
        "continue_session": False,
    }
    defaults.update(overrides)
    return make_classify_args(**defaults)
