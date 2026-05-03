"""Unit tests for document_dependency_graph.walk."""

from pathlib import Path
from typing import Any
from unittest.mock import MagicMock, patch

from document_dependency_graph.walk import build_subclause_record


def _run_record(
    make_lrm: Path,
    *,
    deps: list[str],
    proof: str = "s.",
    prereq: str = "p",
    model: str = "opus",
) -> tuple[dict[str, Any], MagicMock, MagicMock, MagicMock]:
    """Patch the three oracles, run build_subclause_record, return mocks+record."""
    deps_patch = patch(
        "document_dependency_graph.walk.compute_subclause_dependencies",
        return_value=deps,
    )
    proof_patch = patch(
        "document_dependency_graph.walk.compute_proof_sentence",
        return_value=proof,
    )
    prereq_patch = patch(
        "document_dependency_graph.walk.compute_prerequisites",
        return_value=prereq,
    )
    with deps_patch as mock_deps, proof_patch as mock_proof, \
         prereq_patch as mock_prereq:
        record = build_subclause_record(
            "4.4", str(make_lrm), model=model,
        )
    return record, mock_deps, mock_proof, mock_prereq


def test_record_lists_dependencies(make_lrm: Path) -> None:
    """The record exposes the dependency list in oracle order."""
    record, _, _, _ = _run_record(make_lrm, deps=["3.14.3", "10.4.1"])
    assert record["dependencies"] == ["3.14.3", "10.4.1"]


def test_record_proofs_keyed_by_dep(make_lrm: Path) -> None:
    """The record stores one proof sentence per dependency."""
    record, _, _, _ = _run_record(make_lrm, deps=["3.14.3", "10.4.1"])
    assert set(record["proofs"]) == {"3.14.3", "10.4.1"}


def test_record_prerequisites_keyed_by_dep(make_lrm: Path) -> None:
    """The record stores one prerequisites string per dependency."""
    record, _, _, _ = _run_record(
        make_lrm, deps=["3.14.3"], prereq="needs §3.14.3 elaborated",
    )
    assert record["prerequisites"]["3.14.3"] == "needs §3.14.3 elaborated"


def test_record_handles_empty_dependencies(make_lrm: Path) -> None:
    """A subclause with no dependencies yields empty proof/prereq dicts."""
    record, _, _, _ = _run_record(make_lrm, deps=[])
    expected: dict[str, Any] = {
        "dependencies": [],
        "proofs": {},
        "prerequisites": {},
    }
    assert record == expected


def test_record_calls_proof_oracle_per_dep(make_lrm: Path) -> None:
    """compute_proof_sentence is invoked once per dependency."""
    _, _, mock_proof, _ = _run_record(make_lrm, deps=["3.14.3", "10.4.1"])
    assert mock_proof.call_count == 2


def test_record_calls_prereq_oracle_per_dep(make_lrm: Path) -> None:
    """compute_prerequisites is invoked once per dependency."""
    _, _, _, mock_prereq = _run_record(make_lrm, deps=["3.14.3", "10.4.1"])
    assert mock_prereq.call_count == 2


def test_record_forwards_model_to_dependency_oracle(make_lrm: Path) -> None:
    """The model argument flows to compute_subclause_dependencies."""
    _, mock_deps, _, _ = _run_record(make_lrm, deps=[], model="haiku")
    assert mock_deps.call_args[1]["model"] == "haiku"
