"""Unit tests for the satisfy_clause pipeline."""

import pytest

from satisfy_clause.pipeline import descendants_of, satisfy_clause


# --- descendants_of --------------------------------------------------------


def test_descendants_of_filters_by_clause_prefix() -> None:
    """Excludes keys that do not begin with ``<clause>.``."""
    toc = {"33": (1, 1), "33.1": (1, 1), "34.1": (1, 1)}
    assert descendants_of("33", toc) == ["33.1"]


def test_descendants_of_excludes_clause_itself() -> None:
    """The clause id itself is not a descendant of itself."""
    toc = {"33": (1, 1), "33.1": (1, 1)}
    assert "33" not in descendants_of("33", toc)


def test_descendants_of_sorts_numerically() -> None:
    """Sort segment-by-segment as integers, so 33.10 follows 33.9."""
    toc = {"33.10": (1, 1), "33.2": (1, 1), "33.1": (1, 1), "33.9": (1, 1)}
    assert descendants_of("33", toc) == ["33.1", "33.2", "33.9", "33.10"]


def test_descendants_of_handles_deep_descendants() -> None:
    """Multi-level descendants are returned in document order."""
    toc = {
        "33.1": (1, 1),
        "33.1.10": (1, 1),
        "33.1.2": (1, 1),
        "33.2": (1, 1),
    }
    assert descendants_of("33", toc) == [
        "33.1", "33.1.2", "33.1.10", "33.2",
    ]


def test_descendants_of_annex() -> None:
    """Annex-letter clauses use the same prefix rule."""
    toc = {"A": (1, 1), "A.1": (1, 1), "B.1": (1, 1)}
    assert descendants_of("A", toc) == ["A.1"]


def test_descendants_of_no_match_returns_empty() -> None:
    """A clause with no descendants in the TOC returns an empty list."""
    toc = {"33": (1, 1)}
    assert not descendants_of("33", toc)


# --- satisfy_clause --------------------------------------------------------


def test_satisfy_clause_dispatches_to_satisfy_subclauses(monkeypatch) -> None:
    """Hands the descendant list to satisfy_subclauses with lrm, model, labels."""
    captured = []
    monkeypatch.setattr(
        "satisfy_clause.pipeline.load_toc",
        lambda _lrm: {"33": (1, 1), "33.1": (1, 1), "33.2": (1, 1)},
    )
    monkeypatch.setattr(
        "satisfy_clause.pipeline.satisfy_subclauses",
        lambda subs, lrm, *, model, labels:
            captured.append((subs, lrm, model, labels)),
    )
    satisfy_clause(
        "33", "lrm.pdf", model="opus", labels=["IEEE 1800-2023"],
    )
    assert captured == [
        (["33.1", "33.2"], "lrm.pdf", "opus", ["IEEE 1800-2023"]),
    ]


def test_satisfy_clause_passes_labels_through(monkeypatch) -> None:
    """The labels list is forwarded verbatim to satisfy_subclauses."""
    captured = []
    monkeypatch.setattr(
        "satisfy_clause.pipeline.load_toc",
        lambda _lrm: {"33.1": (1, 1)},
    )
    monkeypatch.setattr(
        "satisfy_clause.pipeline.satisfy_subclauses",
        lambda subs, lrm, *, model, labels: captured.append(labels),
    )
    satisfy_clause(
        "33", "lrm.pdf", model="opus", labels=["IEEE 1800-2023", "bug"],
    )
    assert captured == [["IEEE 1800-2023", "bug"]]


def test_satisfy_clause_empty_descendants_exits(monkeypatch) -> None:
    """A clause with no descendants in the TOC exits non-zero."""
    monkeypatch.setattr(
        "satisfy_clause.pipeline.load_toc", lambda _lrm: {"33": (1, 1)},
    )
    monkeypatch.setattr(
        "satisfy_clause.pipeline.satisfy_subclauses",
        lambda *_args, **_kwargs: None,
    )
    with pytest.raises(SystemExit):
        satisfy_clause(
            "33", "lrm.pdf", model="opus", labels=["IEEE 1800-2023"],
        )


def test_satisfy_clause_empty_descendants_message_names_clause(
    monkeypatch,
) -> None:
    """The exit message names the requested clause."""
    monkeypatch.setattr(
        "satisfy_clause.pipeline.load_toc", lambda _lrm: {},
    )
    with pytest.raises(SystemExit, match="§33"):
        satisfy_clause(
            "33", "lrm.pdf", model="opus", labels=["IEEE 1800-2023"],
        )


def test_satisfy_clause_empty_descendants_message_names_lrm(
    monkeypatch,
) -> None:
    """The exit message names the LRM path so the caller can fix --lrm."""
    monkeypatch.setattr(
        "satisfy_clause.pipeline.load_toc", lambda _lrm: {},
    )
    with pytest.raises(SystemExit, match="missing.pdf"):
        satisfy_clause(
            "33", "missing.pdf", model="opus", labels=["IEEE 1800-2023"],
        )
