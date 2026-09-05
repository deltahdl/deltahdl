"""Tests for lib.python.test_fixtures.lrm_subclause_dependencies.

These fixtures supply the table of contents the dependency tests judge
oracle answers against, and they patch the two functions those tests must
not really call. A table that stopped holding an entry with numbered
subclauses beneath it would leave every aggregate-rejection test passing
over an input that cannot be rejected, which is the failure CLAUDE.md
calls an input that cannot fail.
"""

from lib.python.test_fixtures.lrm_subclause_dependencies import (
    AGGREGATE_TOC,
    RETRY_AGGREGATE_TOC,
    patched_oracle_sequence,
    patched_retry_toc,
    patched_toc,
)


def test_aggregate_toc_holds_a_clause_with_a_subclause_beneath_it() -> None:
    """§8 carries §8.1, so an answer naming §8 has something to be rejected for."""
    assert "8" in AGGREGATE_TOC and "8.1" in AGGREGATE_TOC


def test_aggregate_toc_holds_an_annex_with_a_subclause_beneath_it() -> None:
    """Annex A carries A.1, so the annex arm of the rejection is reachable too."""
    assert "A" in AGGREGATE_TOC and "A.1" in AGGREGATE_TOC


def test_retry_toc_holds_the_corrected_answer() -> None:
    """§33.6.1 is in the table, so a retry naming it is not turned down again."""
    assert "33.6.1" in RETRY_AGGREGATE_TOC


def test_patched_oracle_sequence_returns_each_result_in_turn() -> None:
    """Successive oracle calls answer the results in the order given.

    A helper that answered the first result twice would let a retry test
    pass while the retry it is about never happened.
    """
    with patched_oracle_sequence("first", "second") as oracle:
        answers = [oracle("prompt"), oracle("prompt")]
    assert answers == ["first", "second"]


def test_patched_toc_supplies_the_table_it_was_given() -> None:
    """The patched ``load_toc`` answers the table handed in, not a PDF."""
    table = {"1": (1, 2)}
    with patched_toc(table) as load_toc:
        loaded = load_toc("lrm.pdf")
    assert loaded == table


def test_patched_retry_toc_supplies_the_retry_table() -> None:
    """The retry helper patches in the table holding the corrected answer."""
    with patched_retry_toc() as load_toc:
        loaded = load_toc("lrm.pdf")
    assert loaded == RETRY_AGGREGATE_TOC
