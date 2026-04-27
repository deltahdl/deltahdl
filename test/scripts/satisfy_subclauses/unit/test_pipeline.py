"""Unit tests for the satisfy_subclauses pipeline."""

from satisfy_subclauses.pipeline import satisfy_subclauses


def test_satisfy_subclauses_dispatches_each_entry(monkeypatch) -> None:
    """Calls satisfy_subclause once per entry in input order."""
    calls = []
    monkeypatch.setattr(
        "satisfy_subclauses.pipeline.satisfy_subclause",
        lambda s, lrm, *, model, labels:
            calls.append((s, lrm, model, labels)),
    )
    satisfy_subclauses(
        ["33.1", "33.4"], "lrm.pdf", model="opus",
        labels=["IEEE 1800-2023"],
    )
    assert calls == [
        ("33.1", "lrm.pdf", "opus", ["IEEE 1800-2023"]),
        ("33.4", "lrm.pdf", "opus", ["IEEE 1800-2023"]),
    ]


def test_satisfy_subclauses_passes_labels_through(monkeypatch) -> None:
    """Forwards the labels list verbatim to each satisfy_subclause call."""
    seen = []
    monkeypatch.setattr(
        "satisfy_subclauses.pipeline.satisfy_subclause",
        lambda s, lrm, *, model, labels: seen.append(labels),
    )
    satisfy_subclauses(
        ["33.1", "33.4"], "lrm.pdf", model="opus",
        labels=["IEEE 1800-2023", "bug"],
    )
    assert seen == [["IEEE 1800-2023", "bug"], ["IEEE 1800-2023", "bug"]]


def test_satisfy_subclauses_empty_list_no_dispatch(monkeypatch) -> None:
    """An empty list invokes satisfy_subclause zero times."""
    calls = []
    monkeypatch.setattr(
        "satisfy_subclauses.pipeline.satisfy_subclause",
        lambda s, lrm, *, model, labels:
            calls.append((s, lrm, model, labels)),
    )
    satisfy_subclauses(
        [], "lrm.pdf", model="opus", labels=["IEEE 1800-2023"],
    )
    assert not calls
