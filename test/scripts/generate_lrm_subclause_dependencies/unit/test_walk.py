"""Unit tests for generate_lrm_subclause_dependencies.walk."""

from pathlib import Path
from typing import Any
from unittest.mock import MagicMock, patch

from generate_lrm_subclause_dependencies.walk import build_subclause_record


def _run_record(
    make_lrm: Path,
    *,
    deps: list[str],
    model: str = "opus",
) -> tuple[dict[str, Any], MagicMock]:
    """Patch the dependency oracle, run build_subclause_record, return mock+record."""
    deps_patch = patch(
        "generate_lrm_subclause_dependencies.walk.compute_subclause_dependencies",
        return_value=deps,
    )
    with deps_patch as mock_deps:
        record = build_subclause_record(
            "4.4", str(make_lrm), model=model,
        )
    return record, mock_deps


def test_record_lists_dependencies(make_lrm: Path) -> None:
    """The record exposes the dependency list in oracle order."""
    record, _ = _run_record(make_lrm, deps=["3.14.3", "10.4.1"])
    assert record["dependencies"] == ["3.14.3", "10.4.1"]


def test_record_handles_empty_dependencies(make_lrm: Path) -> None:
    """A subclause with no dependencies yields a record with an empty list."""
    record, _ = _run_record(make_lrm, deps=[])
    assert record == {"dependencies": []}


def test_record_forwards_model_to_dependency_oracle(make_lrm: Path) -> None:
    """The model argument flows to compute_subclause_dependencies."""
    _, mock_deps = _run_record(make_lrm, deps=[], model="haiku")
    assert mock_deps.call_args[1]["model"] == "haiku"
