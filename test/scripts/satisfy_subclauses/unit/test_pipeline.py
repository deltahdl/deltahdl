"""Unit tests for the satisfy_subclauses pipeline."""

from typing import Any

import pytest

from satisfy_subclauses.pipeline import satisfy_subclauses

_Call = tuple[str, str, str, list[str]]


def _stub_dispatch(
    monkeypatch: pytest.MonkeyPatch, sink: list[Any],
    *, capture: str = "all",
) -> None:
    """Replace the inner dispatcher; capture either full calls or labels."""
    def fake(
        s: str, lrm: str, *, model: str, labels: list[str],
    ) -> None:
        sink.append(
            (s, lrm, model, labels) if capture == "all" else labels,
        )
    monkeypatch.setattr(
        "satisfy_subclauses.pipeline.satisfy_subclause", fake,
    )


def test_satisfy_subclauses_dispatches_each_entry(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Calls satisfy_subclause once per entry in input order."""
    calls: list[_Call] = []
    _stub_dispatch(monkeypatch, calls)
    satisfy_subclauses(
        ["33.1", "33.4"], "lrm.pdf", model="opus",
        labels=["IEEE 1800-2023"],
    )
    assert calls == [
        ("33.1", "lrm.pdf", "opus", ["IEEE 1800-2023"]),
        ("33.4", "lrm.pdf", "opus", ["IEEE 1800-2023"]),
    ]


def test_satisfy_subclauses_passes_labels_through(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Forwards the labels list verbatim to each satisfy_subclause call."""
    seen: list[list[str]] = []
    _stub_dispatch(monkeypatch, seen, capture="labels")
    satisfy_subclauses(
        ["33.1", "33.4"], "lrm.pdf", model="opus",
        labels=["IEEE 1800-2023", "bug"],
    )
    assert seen == [["IEEE 1800-2023", "bug"], ["IEEE 1800-2023", "bug"]]


def test_satisfy_subclauses_empty_list_no_dispatch(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """An empty list invokes satisfy_subclause zero times."""
    calls: list[_Call] = []
    _stub_dispatch(monkeypatch, calls)
    satisfy_subclauses(
        [], "lrm.pdf", model="opus", labels=["IEEE 1800-2023"],
    )
    assert not calls
