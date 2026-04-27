"""Tests for lib.lrm.load_toc."""

from lib.python.lrm import load_toc


def test_leaf_clause_maps_to_start_page(make_pdf, nested_outline):
    """A leaf bookmark resolves to its 1-indexed start page."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23.2.2"][0] == 112


def test_sibling_boundary_sets_end_page(make_pdf, nested_outline):
    """End page = next-sibling-start − 1 for a sibling boundary."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23.2.1"][1] == 111


def test_ancestor_boundary_sets_end_page(make_pdf, nested_outline):
    """End page crosses subtree boundary to next non-descendant."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23.2.2"][1] == 129


def test_parent_clause_spans_subtree(make_pdf, nested_outline):
    """A parent clause's end page reaches the start of the next sibling."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["23"][1] == 129


def test_last_entry_ends_at_document_end(make_pdf, nested_outline):
    """The final outline entry ends at the last PDF page."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path)["24"][1] == 200


def test_short_subclause_clamps_end_to_start(make_pdf):
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


def test_non_clause_titles_are_skipped(make_pdf):
    """Bookmark titles without a leading clause token are ignored."""
    outline = [
        (1, "Front matter", 1),
        (1, "1 Overview", 5),
    ]
    path = make_pdf("a.pdf", 10, outline)
    assert "Front matter" not in load_toc(path)


def test_empty_outline_returns_empty_dict(blank_pdf):
    """A PDF with no outline yields an empty mapping."""
    assert load_toc(blank_pdf) == {}


def test_missing_path_returns_empty_dict(tmp_path):
    """A nonexistent file path yields an empty mapping."""
    assert load_toc(str(tmp_path / "does-not-exist.pdf")) == {}


def test_corrupt_pdf_returns_empty_dict(tmp_path):
    """A non-PDF file yields an empty mapping rather than raising."""
    path = tmp_path / "corrupt.pdf"
    path.write_bytes(b"not a pdf")
    assert load_toc(str(path)) == {}


def test_repeat_call_returns_same_object(make_pdf, nested_outline):
    """Memoization: a second call returns the identical dict object."""
    path = make_pdf("a.pdf", 200, nested_outline)
    assert load_toc(path) is load_toc(path)
