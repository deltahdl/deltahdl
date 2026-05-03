"""Unit tests for the satisfy_clauses pipeline."""

from typing import Any

import pytest

from satisfy_clauses.pipeline import satisfy_clauses

_Call = tuple[str, str, str, list[str]]


def _stub_dispatch(
    monkeypatch: pytest.MonkeyPatch, sink: list[Any],
    *, capture: str = "all",
) -> None:
    """Replace the inner dispatcher; capture either full calls or labels."""
    def fake(
        c: str, lrm: str, *, model: str, labels: list[str],
    ) -> None:
        sink.append(
            (c, lrm, model, labels) if capture == "all" else labels,
        )
    monkeypatch.setattr(
        "satisfy_clauses.pipeline.satisfy_clause", fake,
    )


def test_satisfy_clauses_dispatches_each_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Calls satisfy_clause once per entry in input order."""
    calls: list[_Call] = []
    _stub_dispatch(monkeypatch, calls)
    satisfy_clauses(
        ["32", "33"], "lrm.pdf", model="opus", labels=["IEEE 1800-2023"],
    )
    assert calls == [
        ("32", "lrm.pdf", "opus", ["IEEE 1800-2023"]),
        ("33", "lrm.pdf", "opus", ["IEEE 1800-2023"]),
    ]


def test_satisfy_clauses_passes_labels_through(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Forwards the labels list verbatim to each satisfy_clause call."""
    seen: list[list[str]] = []
    _stub_dispatch(monkeypatch, seen, capture="labels")
    satisfy_clauses(
        ["32", "33"], "lrm.pdf", model="opus",
        labels=["IEEE 1800-2023", "bug"],
    )
    assert seen == [["IEEE 1800-2023", "bug"], ["IEEE 1800-2023", "bug"]]


def test_satisfy_clauses_empty_list_no_dispatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An empty list invokes satisfy_clause zero times."""
    calls: list[_Call] = []
    _stub_dispatch(monkeypatch, calls)
    satisfy_clauses(
        [], "lrm.pdf", model="opus", labels=["IEEE 1800-2023"],
    )
    assert not calls
