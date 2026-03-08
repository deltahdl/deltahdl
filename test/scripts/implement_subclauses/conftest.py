"""Shared fixtures for implement_subclauses tests."""

import pytest


@pytest.fixture()
def base_argv(tmp_path):
    """Return minimal valid argv for implement_subclauses."""
    lrm = tmp_path / "lrm.pdf"
    lrm.write_text("")
    return [
        "--lrm", str(lrm), "--subclauses", "6.1,6.2",
        "--clause-issue", "8", "--master-issue", "1",
        "--organization", "o", "--repo", "r",
    ]


@pytest.fixture()
def patch_completion():
    """Return a helper that patches fetch_issue_body and next_unchecked."""
    def _apply(monkeypatch, iscs, *, all_complete):
        if all_complete:
            monkeypatch.setattr(
                iscs, "fetch_issue_body", lambda *_a: "- [x] done\n",
            )
            monkeypatch.setattr(iscs, "next_unchecked", lambda _b: None)
        else:
            monkeypatch.setattr(
                iscs, "fetch_issue_body", lambda *_a: "- [ ] 6.3\n",
            )
            monkeypatch.setattr(iscs, "next_unchecked", lambda _b: "6.3")
    return _apply
