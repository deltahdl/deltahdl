from collections.abc import Callable
from typing import Any

import pytest

import next_subclause
from next_subclause import GRAPH_PATH, main
from next_subclause.pipeline import load_order


def test_the_committed_graph_records_a_non_empty_order() -> None:
    assert load_order(GRAPH_PATH)


def test_the_committed_order_resolves_a_tracked_subclause(
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
    satisfy_issues: Callable[..., list[dict[str, Any]]],
) -> None:
    first = load_order(GRAPH_PATH)[0][0]
    monkeypatch.setattr(
        next_subclause, "list_open_issues", lambda **_: satisfy_issues(first),
    )
    main([])
    assert capsys.readouterr().out.endswith(" #100\n")
