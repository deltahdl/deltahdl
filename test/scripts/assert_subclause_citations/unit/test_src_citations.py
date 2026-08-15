"""The gate over src/: every citation there names a clause that exists."""

from pathlib import Path

from assert_subclause_citations import invalid_citations


def test_every_citation_in_src_names_a_clause(repo_root: Path) -> None:
    """A Subclause("...") in src/ naming no clause of IEEE 1800-2023 fails here.

    Two elaborator reports in src/elaborator/elaborator_items.cpp cited
    6.20.3.1 until #3068, a number the standard has no clause at, and nothing
    anywhere said so: a unit test over a report reads the string the emission
    site passes, which is the value under suspicion.
    """
    assert not invalid_citations(repo_root / "src")
