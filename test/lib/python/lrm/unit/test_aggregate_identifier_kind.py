from lib.python.lrm import identifier_kind, is_top_level_aggregate

TOC = dict.fromkeys(
    ("2", "11", "11.4", "41", "A", "A.10", "B", "P", "Q"), (1, 2),
)

NO_SUBCLAUSES_OF_THEIR_OWN = ("2", "41", "B", "P", "Q")

AGGREGATES = ("11", "A")


def test_the_five_bare_targets_are_not_aggregates() -> None:
    assert not [
        identifier for identifier in NO_SUBCLAUSES_OF_THEIR_OWN
        if is_top_level_aggregate(identifier, TOC)
    ]


def test_the_five_bare_targets_are_clauses_or_annexes() -> None:
    assert [identifier_kind(i, TOC) for i in NO_SUBCLAUSES_OF_THEIR_OWN] == [
        "clause", "clause", "annex", "annex", "annex",
    ]


def test_an_aggregate_is_never_a_subclause() -> None:
    assert [identifier_kind(i, TOC) for i in AGGREGATES] == ["clause", "annex"]


def test_every_aggregate_in_the_table_is_a_clause_or_an_annex() -> None:
    assert not [
        identifier for identifier in TOC
        if is_top_level_aggregate(identifier, TOC)
        and identifier_kind(identifier, TOC) == "subclause"
    ]
