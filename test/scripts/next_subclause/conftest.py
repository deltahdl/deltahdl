"""Shared fixtures and helpers for next_subclause tests."""

import json
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest


@pytest.fixture()
def write_graph(tmp_path: Path) -> Callable[[list[list[str]]], Path]:
    """Return a factory writing a dependency graph holding *order*.

    Only the ``order`` key carries anything. The reader takes nothing
    else from the file, and a fixture supplying records it never reads
    would suggest the answer depended on them.
    """
    def _write(order: list[list[str]]) -> Path:
        path = tmp_path / "dependency_graph.json"
        path.write_text(json.dumps({"records": {}, "order": order}))
        return path

    return _write


@pytest.fixture()
def satisfy_issues() -> Callable[..., list[dict[str, Any]]]:
    """Return a factory building open-issue payloads from subclauses.

    Each entry gets the canonical title for its subclause, which is what
    marks an issue as tracking that subclause rather than mentioning it.
    """
    def _issues(*subclauses: str, first: int = 100) -> list[dict[str, Any]]:
        return [
            {
                "number": first + offset,
                "title": f"Satisfy IEEE 1800-2023 §{subclause}",
            }
            for offset, subclause in enumerate(subclauses)
        ]

    return _issues
