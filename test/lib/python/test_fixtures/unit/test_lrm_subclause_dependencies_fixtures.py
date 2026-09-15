from lib.python.test_fixtures.lrm_subclause_dependencies import (
    AGGREGATE_TOC,
    RETRY_AGGREGATE_TOC,
    patched_oracle_sequence,
    patched_retry_toc,
    patched_toc,
)


def test_aggregate_toc_holds_a_clause_with_a_subclause_beneath_it() -> None:
    assert {"8", "8.1"} <= set(AGGREGATE_TOC)


def test_aggregate_toc_holds_an_annex_with_a_subclause_beneath_it() -> None:
    assert {"A", "A.1"} <= set(AGGREGATE_TOC)


def test_retry_toc_holds_the_corrected_answer() -> None:
    assert "33.6.1" in RETRY_AGGREGATE_TOC


def test_patched_oracle_sequence_returns_each_result_in_turn() -> None:
    with patched_oracle_sequence("first", "second") as oracle:
        answers = [oracle("prompt"), oracle("prompt")]
    assert answers == ["first", "second"]


def test_patched_toc_supplies_the_table_it_was_given() -> None:
    table = {"1": (1, 2)}
    with patched_toc(table) as load_toc:
        loaded = load_toc("lrm.pdf")
    assert loaded == table


def test_patched_retry_toc_supplies_the_retry_table() -> None:
    with patched_retry_toc() as load_toc:
        loaded = load_toc("lrm.pdf")
    assert loaded == RETRY_AGGREGATE_TOC
