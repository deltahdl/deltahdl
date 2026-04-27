"""Unit tests for the satisfy_clauses pipeline."""

from satisfy_clauses.pipeline import satisfy_clauses


def test_satisfy_clauses_dispatches_each_entry(monkeypatch) -> None:
    """Calls satisfy_clause once per entry in input order."""
    calls = []
    monkeypatch.setattr(
        "satisfy_clauses.pipeline.satisfy_clause",
        lambda c, lrm, *, model: calls.append((c, lrm, model)),
    )
    satisfy_clauses(["32", "33"], "lrm.pdf", model="opus")
    assert calls == [("32", "lrm.pdf", "opus"), ("33", "lrm.pdf", "opus")]


def test_satisfy_clauses_empty_list_no_dispatch(monkeypatch) -> None:
    """An empty list invokes satisfy_clause zero times."""
    calls = []
    monkeypatch.setattr(
        "satisfy_clauses.pipeline.satisfy_clause",
        lambda c, lrm, *, model: calls.append((c, lrm, model)),
    )
    satisfy_clauses([], "lrm.pdf", model="opus")
    assert not calls
