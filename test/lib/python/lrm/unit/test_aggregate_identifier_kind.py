"""``is_top_level_aggregate`` and ``identifier_kind`` read one table together.

``is_top_level_aggregate`` decides that an identifier is too coarse to
depend on, and ``identifier_kind`` decides what IEEE 1800-2023 calls it.
``lib.python.lrm_subclause_dependencies._aggregate_message`` runs the two
in that order, naming each rejected identifier by its kind, so it rests
on the two agreeing about the same table of contents.

The five entries with nothing numbered beneath them are the case worth
holding down. Clauses 2 and 41 and annexes B, P and Q can only be named
by their own identifier, so each is a satisfaction target rather than an
aggregate — and each is also the identifier shape ``identifier_kind``
answers ``clause`` or ``annex`` for. A change that made the two disagree
would either reject a target that has to be nameable or hand
``_aggregate_message`` an identifier with no kind to print.
"""

from lib.python.lrm import identifier_kind, is_top_level_aggregate

# The five entries of IEEE 1800-2023 that have nothing numbered beneath
# them, sitting beside two that do: §11 carries §11.4, and Annex A carries
# A.10. Neither function reads a page range, so every entry is given the
# same one rather than the real one — the keys are the whole subject here,
# and spelling out ranges nothing reads would only invite a reader to
# check them.
TOC = dict.fromkeys(
    ("2", "11", "11.4", "41", "A", "A.10", "B", "P", "Q"), (1, 2),
)

# The identifiers the two functions have to agree about.
NO_SUBCLAUSES_OF_THEIR_OWN = ("2", "41", "B", "P", "Q")

AGGREGATES = ("11", "A")


def test_the_five_bare_targets_are_not_aggregates() -> None:
    """None of the five holds a numbered subclause, so none is an aggregate."""
    assert not [
        identifier for identifier in NO_SUBCLAUSES_OF_THEIR_OWN
        if is_top_level_aggregate(identifier, TOC)
    ]


def test_the_five_bare_targets_are_clauses_or_annexes() -> None:
    """Each of the five is named by the word §1.5 or Annex A gives it."""
    assert [identifier_kind(i, TOC) for i in NO_SUBCLAUSES_OF_THEIR_OWN] == [
        "clause", "clause", "annex", "annex", "annex",
    ]


def test_an_aggregate_is_never_a_subclause() -> None:
    """What ``_aggregate_message`` prints is a clause or an annex, never None."""
    assert [identifier_kind(i, TOC) for i in AGGREGATES] == ["clause", "annex"]


def test_every_aggregate_in_the_table_is_a_clause_or_an_annex() -> None:
    """No entry the table holds is both an aggregate and a subclause."""
    assert not [
        identifier for identifier in TOC
        if is_top_level_aggregate(identifier, TOC)
        and identifier_kind(identifier, TOC) == "subclause"
    ]
