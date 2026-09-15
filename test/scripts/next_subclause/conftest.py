import json
from collections.abc import Callable
from pathlib import Path
from typing import Any

import pytest


@pytest.fixture()
def write_graph(tmp_path: Path) -> Callable[[list[list[str]]], Path]:
    def _write(order: list[list[str]]) -> Path:
        path = tmp_path / "dependency_graph.json"
        path.write_text(json.dumps({"records": {}, "order": order}))
        return path

    return _write


@pytest.fixture()
def satisfy_issues() -> Callable[..., list[dict[str, Any]]]:
    def _issues(*subclauses: str, first: int = 100) -> list[dict[str, Any]]:
        return [
            {
                "number": first + offset,
                "title": f"Satisfy IEEE 1800-2023 §{subclause}",
            }
            for offset, subclause in enumerate(subclauses)
        ]

    return _issues
