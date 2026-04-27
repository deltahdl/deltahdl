"""Tests for lib.lrm."""

from lib.python.lrm import build_lrm_read_instruction


def test_lrm_read_general_subclause() -> None:
    """General subclause (X.1) does not add 'Also read General'."""
    result = build_lrm_read_instruction("6.1", "/lrm.pdf")
    assert "Also read" not in result


def test_lrm_read_non_general_adds_context() -> None:
    """Non-general subclause adds 'Also read General or Overview'."""
    result = build_lrm_read_instruction("6.3", "/lrm.pdf")
    assert "General or Overview" in result


def test_lrm_read_deep_includes_ancestors() -> None:
    """Deep subclause includes ancestor list."""
    result = build_lrm_read_instruction("6.3.2", "/lrm.pdf")
    assert "§6.3" in result


def test_lrm_read_includes_lrm_path() -> None:
    """Instruction includes the LRM path."""
    result = build_lrm_read_instruction("4.1", "/my/lrm.pdf")
    assert "/my/lrm.pdf" in result


def test_lrm_read_includes_subclause() -> None:
    """Instruction includes the subclause number."""
    result = build_lrm_read_instruction("9.2.1", "/lrm.pdf")
    assert "§9.2.1" in result


def test_lrm_read_includes_target_page_range(make_pdf, nested_outline) -> None:
    """Target subclause page range appears when outline is available."""
    path = make_pdf("a.pdf", 200, nested_outline)
    result = build_lrm_read_instruction("23.2.2", path)
    assert "pages 112-129" in result


def test_lrm_read_includes_ancestor_page_range(
    make_pdf, nested_outline,
) -> None:
    """Ancestor page range appears, de-overlapped against the target."""
    path = make_pdf("a.pdf", 200, nested_outline)
    result = build_lrm_read_instruction("23.2.2", path)
    assert "pages 110-111" in result


def test_lrm_read_omits_missing_clause_pages(make_pdf) -> None:
    """A clause missing from the outline gets no page range."""
    outline = [
        (1, "23 Tasks and functions", 100),
        (1, "24 Classes", 130),
    ]
    path = make_pdf("a.pdf", 200, outline)
    result = build_lrm_read_instruction("23.2.2", path)
    assert "(pages" not in result


def test_lrm_read_omits_ancestor_pages_when_overlap_total(make_pdf) -> None:
    """Ancestor that shares its start page with the target gets no range."""
    outline = [
        (1, "23 Tasks", 100),
        (2, "23.2 Tasks", 110),
        (3, "23.2.1 Decl", 110),
        (1, "24 Classes", 130),
    ]
    path = make_pdf("a.pdf", 200, outline)
    result = build_lrm_read_instruction("23.2.1", path)
    assert "§23.2)" in result


def test_lrm_read_formats_single_page_clause(make_pdf) -> None:
    """A clause spanning exactly one page renders as 'page N' (singular)."""
    outline = [
        (1, "1 Overview", 5),
        (1, "2 Body", 6),
    ]
    path = make_pdf("a.pdf", 10, outline)
    result = build_lrm_read_instruction("1", path)
    assert "page 5)" in result


def test_lrm_read_falls_back_when_outline_empty(blank_pdf) -> None:
    """Empty outline → instruction matches the no-PDF fallback."""
    fallback = build_lrm_read_instruction("9.2.1", "/nope.pdf")
    real = build_lrm_read_instruction("9.2.1", blank_pdf)
    assert real.replace(blank_pdf, "/nope.pdf") == fallback


def test_lrm_read_intro_pairs_read_tool_with_pages_param() -> None:
    """One sentence introduces both the Read tool and the `pages:` parameter."""
    result = build_lrm_read_instruction("4.1", "/lrm.pdf")
    sentences = [s.strip() for s in result.split(". ") if s.strip()]
    assert any("Read tool" in s and "pages:" in s for s in sentences)


def test_lrm_read_cap_lives_in_separate_sentence() -> None:
    """The `one page per call` cap is a separate sentence from the intro."""
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
    """The cap sentence names Read's hard 20-page-per-request cap."""
    result = build_lrm_read_instruction("4.1", "/lrm.pdf")
    sentences = [s.strip() for s in result.split(". ") if s.strip()]
    cap = next(s for s in sentences if "one page per call" in s.lower())
    assert "20 pages" in cap


def test_lrm_read_cap_names_content_filter_budget() -> None:
    """The cap sentence names the content-filter budget alongside the Read cap."""
    result = build_lrm_read_instruction("4.1", "/lrm.pdf")
    sentences = [s.strip() for s in result.split(". ") if s.strip()]
    cap = next(s for s in sentences if "one page per call" in s.lower())
    assert "content-filter" in cap


def test_lrm_read_uses_positive_phrasing() -> None:
    """Page hint avoids the word 'never' (positive scope only)."""
    assert "never" not in build_lrm_read_instruction("4.1", "/lrm.pdf")
