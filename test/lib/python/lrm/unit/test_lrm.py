from collections.abc import Callable, Sequence

from lib.python.lrm import build_lrm_read_instruction

PdfBuilder = Callable[[str, int, Sequence[tuple[int, str, int]]], str]


def test_lrm_read_general_subclause() -> None:
    result = build_lrm_read_instruction("6.1", "/lrm.pdf")
    assert "Also read" not in result


def test_lrm_read_non_general_adds_context() -> None:
    result = build_lrm_read_instruction("6.3", "/lrm.pdf")
    assert "General or Overview" in result


def test_lrm_read_deep_includes_ancestors() -> None:
    result = build_lrm_read_instruction("6.3.2", "/lrm.pdf")
    assert "§6.3" in result


def test_lrm_read_includes_lrm_path() -> None:
    result = build_lrm_read_instruction("4.1", "/my/lrm.pdf")
    assert "/my/lrm.pdf" in result


def test_lrm_read_includes_subclause() -> None:
    result = build_lrm_read_instruction("9.2.1", "/lrm.pdf")
    assert "§9.2.1" in result


def test_lrm_read_includes_target_page_range(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("a.pdf", 200, nested_outline)
    result = build_lrm_read_instruction("23.2.2", path)
    assert "pages 112-129" in result


def test_lrm_read_includes_ancestor_page_range(
    make_pdf: PdfBuilder, nested_outline: list[tuple[int, str, int]],
) -> None:
    path = make_pdf("a.pdf", 200, nested_outline)
    result = build_lrm_read_instruction("23.2.2", path)
    assert "pages 110-111" in result


def test_lrm_read_omits_missing_subclause_pages(make_pdf: PdfBuilder) -> None:
    outline = [
        (1, "23 Tasks and functions", 100),
        (1, "24 Classes", 130),
    ]
    path = make_pdf("a.pdf", 200, outline)
    result = build_lrm_read_instruction("23.2.2", path)
    assert "(pages" not in result


def test_lrm_read_omits_ancestor_pages_when_overlap_total(
    make_pdf: PdfBuilder,
) -> None:
    outline = [
        (1, "23 Tasks", 100),
        (2, "23.2 Tasks", 110),
        (3, "23.2.1 Decl", 110),
        (1, "24 Classes", 130),
    ]
    path = make_pdf("a.pdf", 200, outline)
    result = build_lrm_read_instruction("23.2.1", path)
    assert "§23.2)" in result


def test_lrm_read_formats_single_page_clause(make_pdf: PdfBuilder) -> None:
    outline = [
        (1, "1 Overview", 5),
        (1, "2 Body", 6),
    ]
    path = make_pdf("a.pdf", 10, outline)
    result = build_lrm_read_instruction("1", path)
    assert "page 5)" in result


def test_lrm_read_falls_back_when_outline_empty(blank_pdf: str) -> None:
    fallback = build_lrm_read_instruction("9.2.1", "/nope.pdf")
    real = build_lrm_read_instruction("9.2.1", blank_pdf)
    assert real.replace(blank_pdf, "/nope.pdf") == fallback


def test_lrm_read_intro_pairs_read_tool_with_pages_param() -> None:
    result = build_lrm_read_instruction("4.1", "/lrm.pdf")
    sentences = [s.strip() for s in result.split(". ") if s.strip()]
    assert any("Read tool" in s and "pages:" in s for s in sentences)


def test_lrm_read_cap_lives_in_separate_sentence() -> None:
    result = build_lrm_read_instruction("4.1", "/lrm.pdf")
    sentences = [s.strip() for s in result.split(". ") if s.strip()]
    intro_idx = next(
        i for i, s in enumerate(sentences)
        if "Read tool" in s and "pages:" in s
    )
    cap_idx = next(
        i for i, s in enumerate(sentences)
        if "one page per call" in s.lower()
    )
    assert intro_idx != cap_idx


def test_lrm_read_cap_names_read_20_page_limit() -> None:
    result = build_lrm_read_instruction("4.1", "/lrm.pdf")
    sentences = [s.strip() for s in result.split(". ") if s.strip()]
    cap = next(s for s in sentences if "one page per call" in s.lower())
    assert "20 pages" in cap


def test_lrm_read_cap_names_content_filter_budget() -> None:
    result = build_lrm_read_instruction("4.1", "/lrm.pdf")
    sentences = [s.strip() for s in result.split(". ") if s.strip()]
    cap = next(s for s in sentences if "one page per call" in s.lower())
    assert "content-filter" in cap


def test_lrm_read_uses_positive_phrasing() -> None:
    assert "never" not in build_lrm_read_instruction("4.1", "/lrm.pdf")
