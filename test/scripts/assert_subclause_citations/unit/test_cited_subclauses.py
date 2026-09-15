from pathlib import Path

from assert_subclause_citations import cited_subclauses


def test_a_citation_in_code_is_reported() -> None:
    source = 'diag.Error(loc, "bad range", Subclause("11.4.14"));'
    assert cited_subclauses(source) == {"11.4.14"}


def test_a_citation_in_a_line_comment_is_not_reported() -> None:
    source = '// Write Subclause("11.4.14"), not Subclause("§11.4.14").\n'
    assert cited_subclauses(source) == set()


def test_a_citation_in_a_block_comment_is_not_reported() -> None:
    source = '/* Never write Subclause("§11.4.14") at an emission site. */'
    assert cited_subclauses(source) == set()


def test_the_diagnostic_header_cites_no_section_sign(repo_root: Path) -> None:
    header = repo_root / "src" / "common" / "diagnostic.h"
    assert "§11.4.14" not in cited_subclauses(header.read_text())
