"""Shared fixtures for implement_subclauses tests."""

from unittest.mock import MagicMock

import pytest


@pytest.fixture()
def base_argv(tmp_path):
    """Return minimal valid argv for implement_subclauses."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--issues", "100,101",
        "--organization", "o", "--repo", "r",
    ]


def _fake_title(_o, _r, n):
    """Return a fake issue title with a subclause number."""
    return (
        f"Ensure IEEE 1800-2023 §6.{n - 99}"
        " functionalities and tests are implemented"
    )


@pytest.fixture()
def patch_main():
    """Return a helper that patches fetch_issue_title and invoke."""
    def _apply(monkeypatch, iscs):
        monkeypatch.setattr(iscs, "fetch_issue_title", _fake_title)
        mock_invoke = MagicMock()
        monkeypatch.setattr(iscs, "invoke_implement_subclause", mock_invoke)
        return mock_invoke
    return _apply
