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


def test_leaf_subclause_maps_to_start_page(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23.2.2"][0] == 112


def test_sibling_boundary_sets_end_page(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23.2.1"][1] == 111


def test_ancestor_boundary_sets_end_page(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23.2.2"][1] == 129


def test_parent_clause_spans_subtree(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23"][1] == 129


def test_last_entry_ends_at_document_end(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["24"][1] == 200


def test_short_subclause_clamps_end_to_start(make_pdf: PdfBuilder) -> None:
    outline = [
        (1, "33 Configuration", 935),
        (2, "33.1 Introduction", 935),
        (2, "33.2 Configuration", 935),
        (1, "34 Protected envelope", 950),
    ]
    path = make_pdf("a.pdf", 1000, outline)
    assert load_toc(path)["33.1"] == (935, 935)


def test_non_clause_titles_are_skipped(make_pdf: PdfBuilder) -> None:
    outline = [
        (1, "Front matter", 1),
        (1, "1 Overview", 5),
    ]
    path = make_pdf("a.pdf", 10, outline)
    assert "Front matter" not in load_toc(path)


def test_empty_outline_returns_empty_dict(blank_pdf: str) -> None:
    assert load_toc(blank_pdf) == {}


def test_missing_path_returns_empty_dict(tmp_path: Path) -> None:
    assert load_toc(str(tmp_path / "does-not-exist.pdf")) == {}


def test_corrupt_pdf_returns_empty_dict(tmp_path: Path) -> None:
    path = tmp_path / "corrupt.pdf"
    path.write_bytes(b"not a pdf")
    assert load_toc(str(path)) == {}


def test_repeat_call_returns_same_object(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path) is load_toc(path)


def test_unresolvable_destination_is_skipped(
    make_pdf: PdfBuilder,
    nested_outline: list[tuple[int, str, int]],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
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


def test_annex_heading_with_subclauses_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "A" in load_toc(path)


def test_annex_heading_with_subclauses_starts_at_heading_page(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert load_toc(path)["A"][0] == 900


def test_annex_heading_with_subclauses_spans_subtree(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert load_toc(path)["A"][1] == 939


def test_annex_subclauses_still_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "A.1" in load_toc(path)


def test_annex_heading_keywords_singleton_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "B" in load_toc(path)


def test_annex_keywords_singleton_pages(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert load_toc(path)["B"] == (940, 949)


def test_annex_glossary_singleton_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "P" in load_toc(path)


def test_annex_bibliography_singleton_present(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert "Q" in load_toc(path)


def test_annex_singleton_at_document_end_uses_total_pages(
    make_pdf: PdfBuilder,
    annex_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("annex.pdf", 1000, annex_outline)
    assert load_toc(path)["Q"][1] == 1000


def test_is_top_level_aggregate_chapter_with_subclauses_true() -> None:
    toc = {"23": (100, 129), "23.1": (100, 109)}
    assert is_top_level_aggregate("23", toc) is True


def test_is_top_level_aggregate_singleton_chapter_false() -> None:
    toc = {"2": (10, 12), "3": (15, 20)}
    assert is_top_level_aggregate("2", toc) is False


def test_is_top_level_aggregate_annex_with_subclauses_true() -> None:
    toc = {"A": (900, 939), "A.1": (900, 919)}
    assert is_top_level_aggregate("A", toc) is True


def test_is_top_level_aggregate_singleton_annex_false() -> None:
    toc = {"B": (940, 949), "P": (950, 959)}
    assert is_top_level_aggregate("B", toc) is False


def test_is_top_level_aggregate_subclause_false() -> None:
    toc = {"23": (100, 129), "23.2": (110, 129), "23.2.1": (110, 111)}
    assert is_top_level_aggregate("23.2", toc) is False


def test_is_top_level_aggregate_missing_clause_false() -> None:
    toc = {"23": (100, 129)}
    assert is_top_level_aggregate("99", toc) is False


def test_is_top_level_aggregate_does_not_match_prefix_substring() -> None:
    toc = {"2": (10, 12), "20": (100, 130), "20.1": (100, 105)}
    assert is_top_level_aggregate("2", toc) is False


def test_is_sub_level_parent_with_subclauses_true() -> None:
    toc = {"23.2": (110, 129), "23.2.1": (110, 111)}
    assert is_sub_level_parent("23.2", toc) is True


def test_is_sub_level_parent_leaf_false() -> None:
    toc = {"23.2.1": (110, 111)}
    assert is_sub_level_parent("23.2.1", toc) is False


def test_is_sub_level_parent_top_level_with_children_false() -> None:
    toc = {"23": (100, 129), "23.2": (110, 129)}
    assert is_sub_level_parent("23", toc) is False


def test_is_sub_level_parent_top_level_singleton_false() -> None:
    toc = {"2": (10, 12)}
    assert is_sub_level_parent("2", toc) is False


def test_is_sub_level_parent_missing_subclause_false() -> None:
    toc = {"23.2": (110, 129)}
    assert is_sub_level_parent("99.9", toc) is False


def test_is_sub_level_parent_does_not_match_prefix_substring() -> None:
    toc = {"23.2": (110, 119), "23.20": (200, 210), "23.20.1": (200, 205)}
    assert is_sub_level_parent("23.2", toc) is False


def test_is_sub_level_parent_annex_subclause_with_children_true() -> None:
    toc = {"A.1": (900, 920), "A.1.1": (900, 905)}
    assert is_sub_level_parent("A.1", toc) is True


def test_direct_numbered_children_returns_immediate_children() -> None:
    toc = {
        "13": (336, 354),
        "13.1": (336, 336), "13.2": (336, 336), "13.3": (336, 340),
    }
    assert direct_numbered_children("13", toc) == ["13.1", "13.2", "13.3"]


def test_direct_numbered_children_excludes_grandchildren() -> None:
    toc = {
        "13": (336, 354),
        "13.3": (336, 340), "13.3.1": (340, 340), "13.3.2": (340, 340),
    }
    assert direct_numbered_children("13", toc) == ["13.3"]


def test_direct_numbered_children_excludes_prefix_substring_collision() -> None:
    toc = {"2": (10, 12), "20": (100, 130), "20.1": (100, 105)}
    assert direct_numbered_children("2", toc) == []


def test_direct_numbered_children_returns_empty_for_singleton() -> None:
    toc = {"2": (10, 12), "3": (15, 20)}
    assert direct_numbered_children("2", toc) == []


def test_direct_numbered_children_works_for_annex() -> None:
    toc = {"A": (900, 939), "A.1": (900, 919), "A.2": (920, 939)}
    assert direct_numbered_children("A", toc) == ["A.1", "A.2"]


def test_direct_numbered_children_preserves_toc_order() -> None:
    toc = {
        "13": (336, 354),
        "13.3": (336, 340), "13.1": (341, 341), "13.2": (342, 342),
    }
    assert direct_numbered_children("13", toc) == ["13.3", "13.1", "13.2"]


def test_direct_numbered_children_works_for_sub_level_parent() -> None:
    toc = {
        "13.3": (336, 340), "13.3.1": (340, 340), "13.3.2": (340, 340),
    }
    assert direct_numbered_children("13.3", toc) == ["13.3.1", "13.3.2"]
