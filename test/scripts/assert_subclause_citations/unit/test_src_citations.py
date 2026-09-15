from pathlib import Path

from assert_subclause_citations import invalid_citations


def test_every_citation_in_src_names_a_clause(repo_root: Path) -> None:
    assert not invalid_citations(repo_root / "src")
