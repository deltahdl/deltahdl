import runpy
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest

import next_subclause
from next_subclause import GRAPH_PATH, main, parse_args


def _stub_issues(
    monkeypatch: pytest.MonkeyPatch, issues: list[dict[str, Any]],
) -> None:
    monkeypatch.setattr(
        next_subclause, "list_open_issues", lambda **_: issues,
    )


def test_parse_args_defaults_to_the_committed_graph() -> None:
    assert parse_args([]).graph == GRAPH_PATH


def test_parse_args_accepts_an_explicit_graph() -> None:
    assert parse_args(["--graph", "elsewhere.json"]).graph == Path(
        "elsewhere.json",
    )


def test_main_prints_the_subclause_and_the_issue_tracking_it(
    capsys: pytest.CaptureFixture[str],
    monkeypatch: pytest.MonkeyPatch,
    satisfy_issues: Callable[..., list[dict[str, Any]]],
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    _stub_issues(monkeypatch, satisfy_issues("3.2"))
    main(["--graph", str(write_graph([["3.1"], ["3.2"]]))])
    assert capsys.readouterr().out == "§3.2 #100\n"


def test_main_exits_nonzero_when_no_subclause_is_tracked(
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
    monkeypatch: pytest.MonkeyPatch,
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    _stub_issues(monkeypatch, [])
    graph = str(write_graph([["3.1"]]))
    assert get_exit_code(lambda: main(["--graph", graph])) == 1


def test_main_says_why_it_had_no_answer(
    capsys: pytest.CaptureFixture[str],
    get_exit_code: Callable[[Callable[[], object]], int | str | None],
    monkeypatch: pytest.MonkeyPatch,
    write_graph: Callable[[list[list[str]]], Path],
) -> None:
    _stub_issues(monkeypatch, [])
    graph = str(write_graph([["3.1"]]))
    get_exit_code(lambda: main(["--graph", graph]))
    assert "no subclause" in capsys.readouterr().err.lower()


def test_running_the_package_as_a_module_calls_main(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[str] = []
    monkeypatch.setattr(next_subclause, "main", lambda: calls.append("main"))
    runpy.run_module("next_subclause", run_name="__main__")
    assert calls == ["main"]
