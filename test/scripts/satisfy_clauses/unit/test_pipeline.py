"""Unit tests for the satisfy_clauses pipeline."""

from satisfy_clauses.pipeline import satisfy_clauses


def test_satisfy_clauses_dispatches_each_entry(monkeypatch) -> None:
    """Calls satisfy_clause once per entry in input order."""
    calls = []
    monkeypatch.setattr(
        "satisfy_clauses.pipeline.satisfy_clause",
        lambda c, lrm, *, model, labels:
            calls.append((c, lrm, model, labels)),
    )
    satisfy_clauses(
        ["32", "33"], "lrm.pdf", model="opus", labels=["IEEE 1800-2023"],
    )
    assert calls == [
        ("32", "lrm.pdf", "opus", ["IEEE 1800-2023"]),
        ("33", "lrm.pdf", "opus", ["IEEE 1800-2023"]),
    ]


def test_satisfy_clauses_passes_labels_through(monkeypatch) -> None:
    """Forwards the labels list verbatim to each satisfy_clause call."""
    seen = []
    monkeypatch.setattr(
        "satisfy_clauses.pipeline.satisfy_clause",
        lambda c, lrm, *, model, labels: seen.append(labels),
    )
    satisfy_clauses(
        ["32", "33"], "lrm.pdf", model="opus",
        labels=["IEEE 1800-2023", "bug"],
    )
    assert seen == [["IEEE 1800-2023", "bug"], ["IEEE 1800-2023", "bug"]]


def test_satisfy_clauses_empty_list_no_dispatch(monkeypatch) -> None:
    """An empty list invokes satisfy_clause zero times."""
    calls = []
    monkeypatch.setattr(
        "satisfy_clauses.pipeline.satisfy_clause",
        lambda c, lrm, *, model, labels:
            calls.append((c, lrm, model, labels)),
    )
    satisfy_clauses(
        [], "lrm.pdf", model="opus", labels=["IEEE 1800-2023"],
    )
    assert not calls
