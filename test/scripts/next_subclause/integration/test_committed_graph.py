"""Integration tests for next_subclause against the committed graph.

The unit tests write their own order, so they say nothing about the file
the script actually reads. These read that file: a graph that has been
regenerated into a shape the reader does not understand fails here and
nowhere else.
"""

from collections.abc import Callable
from typing import Any

import pytest

import next_subclause
from next_subclause import GRAPH_PATH, main
from next_subclause.pipeline import load_order


def test_the_committed_graph_records_a_non_empty_order() -> None:
    """The graph in the tree holds an order the reader can take groups from."""
    assert load_order(GRAPH_PATH)


def test_the_committed_order_resolves_a_tracked_subclause(
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
    satisfy_issues: Callable[..., list[dict[str, Any]]],
) -> None:
    """A subclause the real order holds is found and reported from it."""
    first = load_order(GRAPH_PATH)[0][0]
    monkeypatch.setattr(
        next_subclause, "list_open_issues", lambda **_: satisfy_issues(first),
    )
    main([])
    assert capsys.readouterr().out.endswith(" #100\n")
