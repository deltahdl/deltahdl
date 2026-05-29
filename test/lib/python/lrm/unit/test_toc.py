"""Tests for lib.lrm.load_toc."""

from collections.abc import Callable, Sequence
from pathlib import Path
from typing import Any

import pytest
from pypdf import PdfReader

from lib.python.lrm import (
    direct_numbered_children,
    is_sub_level_parent,
    is_top_level_aggregate,
    load_toc,
)

PdfBuilder = Callable[[str, int, Sequence[tuple[int, str, int]]], str]


def test_leaf_clause_maps_to_start_page(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    """A leaf bookmark resolves to its 1-indexed start page."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23.2.2"][0] == 112


def test_sibling_boundary_sets_end_page(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    """End page = next-sibling-start − 1 for a sibling boundary."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23.2.1"][1] == 111


def test_ancestor_boundary_sets_end_page(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    """End page crosses subtree boundary to next non-descendant."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23.2.2"][1] == 129


def test_parent_clause_spans_subtree(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    """A parent clause's end page reaches the start of the next sibling."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23"][1] == 129


def test_last_entry_ends_at_document_end(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    """The final outline entry ends at the last PDF page."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["24"][1] == 200


def test_short_subclause_clamps_end_to_start(make_pdf: PdfBuilder) -> None:
    """A subclause whose next non-descendant shares its start page
    yields ``(start, start)``, not an underflowed ``(start, start - 1)``.
    """
    outline = [
        (1, "33 Configuration", 935),
        (2, "33.1 Introduction", 935),
        (2, "33.2 Configuration", 935),
        (1, "34 Protected envelope", 950),
    ]
    path = make_pdf("a.pdf", 1000, outline)
    assert load_toc(path)["33.1"] == (935, 935)


def test_non_clause_titles_are_skipped(make_pdf: PdfBuilder) -> None:
    """Bookmark titles without a leading clause token are ignored."""
    outline = [
        (1, "Front matter", 1),
        (1, "1 Overview", 5),
    ]
    path = make_pdf("a.pdf", 10, outline)
    assert "Front matter" not in load_toc(path)


def test_empty_outline_returns_empty_dict(blank_pdf: str) -> None:
    """A PDF with no outline yields an empty mapping."""
    assert load_toc(blank_pdf) == {}


def test_missing_path_returns_empty_dict(tmp_path: Path) -> None:
    """A nonexistent file path yields an empty mapping."""
    assert load_toc(str(tmp_path / "does-not-exist.pdf")) == {}


def test_corrupt_pdf_returns_empty_dict(tmp_path: Path) -> None:
    """A non-PDF file yields an empty mapping rather than raising."""
    path = tmp_path / "corrupt.pdf"
    path.write_bytes(b"not a pdf")
    assert load_toc(str(path)) == {}


def test_repeat_call_returns_same_object(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    """Memoization: a second call returns the identical dict object."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path) is load_toc(path)


def test_unresolvable_destination_is_skipped(
    make_pdf: PdfBuilder,
    nested_outline: list[tuple[int, str, int]],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Bookmarks whose destination page can't be resolved are skipped."""
    path = make_pdf("unresolvable_all.pdf", 200, nested_outline)
    monkeypatch.setattr(
        PdfReader, "get_destination_page_number",
        lambda *_a, **_kw: None,
    )
    assert load_toc(path) == {}


def test_unresolvable_destination_skips_only_that_entry(
    make_pdf: PdfBuilder,
    nested_outline: list[tuple[int, str, int]],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """Other bookmarks still resolve when one destination is None."""
    path = make_pdf("unresolvable_one.pdf", 200, nested_outline)
    real = PdfReader.get_destination_page_number

    def stub(self: Any, item: Any) -> int | None:
        if str(item.title or "").startswith("23.2.1"):
            return None
        return real(self, item)
    monkeypatch.setattr(
        PdfReader, "get_destination_page_number", stub,
    )
    assert "23.2.1" not in load_toc(path)


# --- annex headings ---------------------------------------------------------


def test_annex_heading_with_subclauses_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    """An ``Annex A …`` heading surfaces as the single-letter identifier ``A``."""
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "A" in load_toc(path)


def test_annex_heading_with_subclauses_starts_at_heading_page(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    """``Annex A`` starts at the page of its outline entry."""
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert load_toc(path)["A"][0] == 900


def test_annex_heading_with_subclauses_spans_subtree(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    """``Annex A`` end page reaches the start of the next non-descendant."""
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert load_toc(path)["A"][1] == 939


def test_annex_subclauses_still_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    """The annex subclause ``A.1`` is still in the TOC alongside ``A``."""
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "A.1" in load_toc(path)


def test_annex_heading_keywords_singleton_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    """``Annex B Keywords``, which has no numbered subclauses, surfaces as ``B``."""
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "B" in load_toc(path)


def test_annex_keywords_singleton_pages(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    """Childless Annex B's end page reaches the start of the next non-descendant."""
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert load_toc(path)["B"] == (940, 949)


def test_annex_glossary_singleton_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    """``Annex P Glossary`` surfaces as ``P``."""
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "P" in load_toc(path)


def test_annex_bibliography_singleton_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    """``Annex Q Bibliography`` surfaces as ``Q``."""
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "Q" in load_toc(path)


def test_annex_singleton_at_document_end_uses_total_pages(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    """A childless annex at end-of-document ends at the last PDF page."""
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert load_toc(path)["Q"][1] == 1000


# --- is_top_level_aggregate -------------------------------------------------


def test_is_top_level_aggregate_chapter_with_subclauses_true() -> None:
    """A chapter with at least one numbered subclause is an aggregate."""
    toc = {"23": (100, 129), "23.1": (100, 109)}
    assert is_top_level_aggregate("23", toc) is True


def test_is_top_level_aggregate_singleton_chapter_false() -> None:
    """A top-level chapter with no numbered subclauses is not an aggregate."""
    toc = {"2": (10, 12), "3": (15, 20)}
    assert is_top_level_aggregate("2", toc) is False


def test_is_top_level_aggregate_annex_with_subclauses_true() -> None:
    """An annex with numbered subclauses is an aggregate."""
    toc = {"A": (900, 939), "A.1": (900, 919)}
    assert is_top_level_aggregate("A", toc) is True


def test_is_top_level_aggregate_singleton_annex_false() -> None:
    """A childless annex (Annex B / P / Q) is not an aggregate."""
    toc = {"B": (940, 949), "P": (950, 959)}
    assert is_top_level_aggregate("B", toc) is False


def test_is_top_level_aggregate_subclause_false() -> None:
    """A sub-level entry is never an aggregate, even with descendants."""
    toc = {"23": (100, 129), "23.2": (110, 129), "23.2.1": (110, 111)}
    assert is_top_level_aggregate("23.2", toc) is False


def test_is_top_level_aggregate_missing_clause_false() -> None:
    """A clause not present in the TOC is not an aggregate."""
    toc = {"23": (100, 129)}
    assert is_top_level_aggregate("99", toc) is False


def test_is_top_level_aggregate_does_not_match_prefix_substring() -> None:
    """``2`` is not an aggregate when only ``20.1`` is present (not ``2.x``)."""
    toc = {"2": (10, 12), "20": (100, 130), "20.1": (100, 105)}
    assert is_top_level_aggregate("2", toc) is False


# --- is_sub_level_parent ----------------------------------------------------


def test_is_sub_level_parent_with_subclauses_true() -> None:
    """A sub-level entry that has at least one numbered subclause is a parent."""
    toc = {"23.2": (110, 129), "23.2.1": (110, 111)}
    assert is_sub_level_parent("23.2", toc) is True


def test_is_sub_level_parent_leaf_false() -> None:
    """A sub-level entry with no descendants in the TOC is not a parent."""
    toc = {"23.2.1": (110, 111)}
    assert is_sub_level_parent("23.2.1", toc) is False


def test_is_sub_level_parent_top_level_with_children_false() -> None:
    """A top-level entry with children is an aggregate, not a sub-level parent."""
    toc = {"23": (100, 129), "23.2": (110, 129)}
    assert is_sub_level_parent("23", toc) is False


def test_is_sub_level_parent_top_level_singleton_false() -> None:
    """A top-level singleton is neither aggregate nor sub-level parent."""
    toc = {"2": (10, 12)}
    assert is_sub_level_parent("2", toc) is False


def test_is_sub_level_parent_missing_clause_false() -> None:
    """A clause not in the TOC is not a sub-level parent."""
    toc = {"23.2": (110, 129)}
    assert is_sub_level_parent("99.9", toc) is False


def test_is_sub_level_parent_does_not_match_prefix_substring() -> None:
    """``23.2`` is not a parent when only ``23.20.1`` exists (not ``23.2.x``)."""
    toc = {"23.2": (110, 119), "23.20": (200, 210), "23.20.1": (200, 205)}
    assert is_sub_level_parent("23.2", toc) is False


def test_is_sub_level_parent_annex_subclause_with_children_true() -> None:
    """An annex sub-level entry with numbered children is a sub-level parent."""
    toc = {"A.1": (900, 920), "A.1.1": (900, 905)}
    assert is_sub_level_parent("A.1", toc) is True


# --- direct_numbered_children -----------------------------------------------


def test_direct_numbered_children_returns_immediate_children() -> None:
    """A chapter's direct numbered children are returned in order."""
    toc = {
        "13": (336, 354),
        "13.1": (336, 336), "13.2": (336, 336), "13.3": (336, 340),
    }
    assert direct_numbered_children("13", toc) == ["13.1", "13.2", "13.3"]


def test_direct_numbered_children_excludes_grandchildren() -> None:
    """A grandchild like ``13.3.1`` is excluded from the direct-children list."""
    toc = {
        "13": (336, 354),
        "13.3": (336, 340), "13.3.1": (340, 340), "13.3.2": (340, 340),
    }
    assert direct_numbered_children("13", toc) == ["13.3"]


def test_direct_numbered_children_excludes_prefix_substring_collision() -> None:
    """``2`` does not pick up ``20.1`` (substring prefix is not a child)."""
    toc = {"2": (10, 12), "20": (100, 130), "20.1": (100, 105)}
    assert direct_numbered_children("2", toc) == []


def test_direct_numbered_children_returns_empty_for_singleton() -> None:
    """A top-level singleton with no numbered subclauses produces an empty list."""
    toc = {"2": (10, 12), "3": (15, 20)}
    assert direct_numbered_children("2", toc) == []


def test_direct_numbered_children_works_for_annex() -> None:
    """An annex's direct numbered children are returned just like a chapter's."""
    toc = {"A": (900, 939), "A.1": (900, 919), "A.2": (920, 939)}
    assert direct_numbered_children("A", toc) == ["A.1", "A.2"]


def test_direct_numbered_children_preserves_toc_order() -> None:
    """Output preserves the TOC's insertion (document) order."""
    toc = {
        "13": (336, 354),
        "13.3": (336, 340), "13.1": (341, 341), "13.2": (342, 342),
    }
    assert direct_numbered_children("13", toc) == ["13.3", "13.1", "13.2"]


def test_direct_numbered_children_works_for_sub_level_parent() -> None:
    """A sub-level parent's direct numbered children are returned in order."""
    toc = {
        "13.3": (336, 340), "13.3.1": (340, 340), "13.3.2": (340, 340),
    }
    assert direct_numbered_children("13.3", toc) == ["13.3.1", "13.3.2"]
