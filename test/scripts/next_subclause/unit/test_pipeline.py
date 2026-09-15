from collections.abc import Callable
from pathlib import Path
from typing import Any

from next_subclause.pipeline import load_order, next_subclause


def test_load_order_returns_the_recorded_groups(
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    assert load_order(write_graph([["3.1"], ["3.2", "3.3"]])) == [
        ["3.1"], ["3.2", "3.3"],
    ]


def test_next_subclause_takes_the_earliest_group_that_is_tracked(
    satisfy_issues: Callable[..., list[dict[str, Any]]],
) -> None:
    assert next_subclause(
        [["3.1"], ["3.2"]], satisfy_issues("3.2", "3.1"),
    ) == ("3.1", 101)


def test_next_subclause_passes_over_a_group_nothing_tracks(
    satisfy_issues: Callable[..., list[dict[str, Any]]],
) -> None:
    assert next_subclause(
        [["3.1"], ["3.2"]], satisfy_issues("3.2"),
    ) == ("3.2", 100)


def test_next_subclause_passes_over_an_untracked_entry_within_a_group(
    satisfy_issues: Callable[..., list[dict[str, Any]]],
) -> None:
    assert next_subclause(
        [["3.1", "3.2"]], satisfy_issues("3.2"),
    ) == ("3.2", 100)


def test_next_subclause_ignores_an_issue_that_only_mentions_a_subclause() -> None:
    assert next_subclause(
        [["3.1"]],
        [{"number": 100, "title": "Six §3.1 sv-tests fail on unknown operands"}],
    ) is None


def test_next_subclause_answers_none_when_the_order_is_exhausted(
    satisfy_issues: Callable[..., list[dict[str, Any]]],
) -> None:
    assert next_subclause([["3.1"], ["3.2"]], satisfy_issues("9.9")) is None
