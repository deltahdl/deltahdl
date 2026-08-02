"""Unit tests for the next_subclause entry point."""

from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest

import next_subclause
from next_subclause import GRAPH_PATH, main, parse_args


def _stub_issues(
    monkeypatch: pytest.MonkeyPatch, issues: list[dict[str, Any]],
) -> None:
    """Answer the repository listing with *issues* instead of calling gh."""
    monkeypatch.setattr(
        next_subclause, "list_open_issues", lambda **_: issues,
    )


def test_parse_args_defaults_to_the_committed_graph() -> None:
    """With no --graph the reader is pointed at the graph in the tree."""
    assert parse_args([]).graph == GRAPH_PATH


def test_parse_args_accepts_an_explicit_graph() -> None:
    """A --graph argument replaces the committed location."""
    assert parse_args(["--graph", "elsewhere.json"]).graph == Path(
        "elsewhere.json",
    )


def test_main_prints_the_subclause_and_the_issue_tracking_it(
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
    satisfy_issues: Callable[..., list[dict[str, Any]]],
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    """The answer is one line: the labelled subclause and its issue number."""
    _stub_issues(monkeypatch, satisfy_issues("3.2"))
    main(["--graph", str(write_graph([["3.1"], ["3.2"]]))])
    assert capsys.readouterr().out == "§3.2 #100\n"


def test_main_exits_nonzero_when_no_subclause_is_tracked(
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
    monkeypatch: pytest.MonkeyPatch,
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    """Nothing left to take is not an answer, so it is not reported as one."""
    _stub_issues(monkeypatch, [])
    graph = str(write_graph([["3.1"]]))
    assert get_exit_code(lambda: main(["--graph", graph])) == 1


def test_main_says_why_it_had_no_answer(
    capsys: pytest.CaptureFixture[str],
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
    monkeypatch: pytest.MonkeyPatch,
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    """The exit code is accompanied by a reason on stderr, not silence."""
    _stub_issues(monkeypatch, [])
    graph = str(write_graph([["3.1"]]))
    get_exit_code(lambda: main(["--graph", graph]))
    assert "no subclause" in capsys.readouterr().err.lower()
