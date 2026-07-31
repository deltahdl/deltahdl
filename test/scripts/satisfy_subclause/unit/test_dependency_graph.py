"""Unit tests for satisfy_subclause.dependency_graph."""

import json
from pathlib import Path
from unittest.mock import patch

import pytest

from satisfy_subclause.dependency_graph import (
    GRAPH_PATH,
    load_dependency_graph,
    resolve_dependencies,
)


# A path no PDF lives at. load_toc reads it as an empty table of
# contents, which is what the aggregate check consults; every test here
# turns on the identifier itself rather than on where it sits in the
# LRM, so an empty table of contents is the honest input.
_NO_LRM = "no-such-lrm.pdf"

# What the oracle answers when a test lets the call through. It shares
# no entry with any recorded list below, so a result carrying it is
# proof the oracle was asked and a result without it is proof it was
# not.
_ORACLE_ANSWER = ["9.9.9"]


def _write_graph(path: Path, records: dict[str, list[str]]) -> Path:
    """Write a graph file holding *records* and return the path."""
    path.write_text(json.dumps({
        "records": {
            subclause: {"dependencies": deps}
            for subclause, deps in records.items()
        },
        "order": [],
    }))
    return path


def _resolve_against(graph: Path, subclause: str) -> list[str]:
    """Resolve *subclause* with *graph* installed and the oracle stubbed."""
    with patch(
        "satisfy_subclause.dependency_graph.GRAPH_PATH", graph,
    ), patch(
        "satisfy_subclause.dependency_graph.compute_subclause_dependencies",
        return_value=list(_ORACLE_ANSWER),
    ):
        return resolve_dependencies(
            subclause, _NO_LRM, model="sonnet", effort="medium",
        )


# --- the committed graph ----------------------------------------------------


def test_graph_path_names_a_file_that_exists() -> None:
    """The wired-in path resolves to the graph the generator committed."""
    assert GRAPH_PATH.is_file()


def test_graph_path_names_the_documented_graph() -> None:
    """The wired-in path is docs/dependency_graph.json, not some other file."""
    assert GRAPH_PATH.parts[-2:] == ("docs", "dependency_graph.json")


# --- load_dependency_graph --------------------------------------------------


def test_absent_graph_reads_as_no_records(tmp_path: Path) -> None:
    """A graph that was never written reads as no recorded answers at all."""
    assert not load_dependency_graph(tmp_path / "absent.json")


def test_absent_graph_says_so(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """An absent graph is announced, so a per-frame bill is not silent."""
    load_dependency_graph(tmp_path / "unannounced.json")
    assert "is absent" in capsys.readouterr().err


def test_graph_maps_a_subclause_to_its_recorded_dependencies(
    tmp_path: Path,
) -> None:
    """Each record is read back as that subclause's dependency list."""
    graph = _write_graph(tmp_path / "graph.json", {"7.9": ["7.4", "7.8"]})
    assert load_dependency_graph(graph)["7.9"] == ["7.4", "7.8"]


def test_graph_keeps_every_subclause_it_records(tmp_path: Path) -> None:
    """A graph of several records reads back as several records."""
    graph = _write_graph(
        tmp_path / "several.json", {"7.9": ["7.4"], "7.8": [], "6.5": ["6.4"]},
    )
    assert sorted(load_dependency_graph(graph)) == ["6.5", "7.8", "7.9"]


def test_unparseable_graph_raises(tmp_path: Path) -> None:
    """A graph that is not JSON is a broken file, not a reason to fall back."""
    graph = tmp_path / "garbage.json"
    graph.write_text("this is not JSON")
    with pytest.raises(ValueError):
        load_dependency_graph(graph)


def test_graph_without_records_raises(tmp_path: Path) -> None:
    """A JSON file lacking the records the generator writes is broken too."""
    graph = tmp_path / "recordless.json"
    graph.write_text(json.dumps({"order": []}))
    with pytest.raises(KeyError):
        load_dependency_graph(graph)


# --- resolve_dependencies ---------------------------------------------------


def test_recorded_answer_is_what_comes_back(tmp_path: Path) -> None:
    """A subclause the graph records resolves to the recorded list."""
    graph = _write_graph(tmp_path / "hit.json", {"7.9": ["7.4", "7.8"]})
    assert _resolve_against(graph, "7.9") == ["7.4", "7.8"]


def test_recorded_answer_is_not_the_oracle_answer(tmp_path: Path) -> None:
    """A recorded answer is used in place of the oracle's, not alongside it."""
    graph = _write_graph(tmp_path / "instead.json", {"7.9": ["7.4"]})
    assert _ORACLE_ANSWER[0] not in _resolve_against(graph, "7.9")


def test_recorded_answer_leaves_the_oracle_unasked(tmp_path: Path) -> None:
    """A hit costs no oracle call, which is the whole point of the graph."""
    graph = _write_graph(tmp_path / "unasked.json", {"7.9": ["7.4"]})
    with patch(
        "satisfy_subclause.dependency_graph.GRAPH_PATH", graph,
    ), patch(
        "satisfy_subclause.dependency_graph.compute_subclause_dependencies",
    ) as oracle:
        resolve_dependencies("7.9", _NO_LRM, model="sonnet", effort="medium")
    assert not oracle.called


def test_recorded_empty_answer_is_an_answer(tmp_path: Path) -> None:
    """A subclause recorded as depending on nothing is a hit, not a miss.

    A fifth of the committed graph records an empty list, so treating
    empty as absent would send every one of those subclauses to the
    oracle while the graph looked as though it were being read.
    """
    graph = _write_graph(tmp_path / "empty.json", {"7.9": []})
    assert not _resolve_against(graph, "7.9")


def test_unrecorded_subclause_asks_the_oracle(tmp_path: Path) -> None:
    """A subclause the graph does not mention falls through to the oracle."""
    graph = _write_graph(tmp_path / "miss.json", {"7.8": ["7.4"]})
    assert _resolve_against(graph, "7.9") == _ORACLE_ANSWER


def test_rejected_recording_asks_the_oracle(tmp_path: Path) -> None:
    """A recorded list today's checks reject is treated as a miss."""
    graph = _write_graph(tmp_path / "rejected.json", {"7.9": ["not-a-clause"]})
    assert _resolve_against(graph, "7.9") == _ORACLE_ANSWER


def test_rejected_recording_says_so(
    tmp_path: Path, capsys: pytest.CaptureFixture[str],
) -> None:
    """A rejected recording is reported, so a stale graph is visible."""
    graph = _write_graph(tmp_path / "reported.json", {"7.9": ["not-a-clause"]})
    _resolve_against(graph, "7.9")
    assert "no longer acceptable" in capsys.readouterr().err
