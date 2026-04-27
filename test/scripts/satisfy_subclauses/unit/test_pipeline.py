"""Unit tests for the satisfy_subclauses pipeline."""

from satisfy_subclauses.pipeline import satisfy_subclauses


def test_satisfy_subclauses_dispatches_each_entry(monkeypatch) -> None:
    """Calls satisfy_subclause once per entry in input order."""
    calls = []
    monkeypatch.setattr(
        "satisfy_subclauses.pipeline.satisfy_subclause",
        lambda s, lrm, *, model: calls.append((s, lrm, model)),
    )
    satisfy_subclauses(["33.1", "33.4"], "lrm.pdf", model="opus")
    assert calls == [
        ("33.1", "lrm.pdf", "opus"),
        ("33.4", "lrm.pdf", "opus"),
    ]


def test_satisfy_subclauses_empty_list_no_dispatch(monkeypatch) -> None:
    """An empty list invokes satisfy_subclause zero times."""
    calls = []
    monkeypatch.setattr(
        "satisfy_subclauses.pipeline.satisfy_subclause",
        lambda s, lrm, *, model: calls.append((s, lrm, model)),
    )
    satisfy_subclauses([], "lrm.pdf", model="opus")
    assert not calls
