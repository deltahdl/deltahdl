"""Unit tests for the document_dependency_graph argparse wrapper."""

import json
import runpy
from unittest.mock import patch

import pytest

import document_dependency_graph


def test_parse_args_requires_lrm(make_output) -> None:
    """--lrm is required."""
    with pytest.raises(SystemExit):
        document_dependency_graph.parse_args([
            "--output", str(make_output),
        ])


def test_parse_args_validates_lrm_exists(tmp_path, make_output) -> None:
    """--lrm must point at an existing file."""
    missing = tmp_path / "missing.pdf"
    with pytest.raises(SystemExit):
        document_dependency_graph.parse_args([
            "--lrm", str(missing),
            "--output", str(make_output),
        ])


def test_parse_args_default_model(make_lrm, make_output) -> None:
    """--model defaults to 'opus'."""
    args = document_dependency_graph.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.model == "opus"


def test_parse_args_explicit_model(make_lrm, make_output) -> None:
    """--model accepts an explicit value."""
    args = document_dependency_graph.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--model", "haiku",
    ])
    assert args.model == "haiku"


def test_parse_args_requires_output(make_lrm) -> None:
    """--output is required."""
    with pytest.raises(SystemExit):
        document_dependency_graph.parse_args([
            "--lrm", str(make_lrm),
        ])


def test_parse_args_output_value(make_lrm, make_output) -> None:
    """--output is parsed and forwarded as the file path."""
    args = document_dependency_graph.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert str(args.output) == str(make_output)


def test_main_invokes_oracle_for_placeholder(make_lrm, make_output) -> None:
    """main() calls the dependency oracle once for the placeholder subclause."""
    with patch(
        "document_dependency_graph.compute_subclause_dependencies",
        return_value=[],
    ) as mock_oracle:
        document_dependency_graph.main([
            "--lrm", str(make_lrm),
            "--output", str(make_output),
        ])
    assert mock_oracle.call_count == 1


def test_main_passes_lrm_to_oracle(make_lrm, make_output) -> None:
    """main() forwards the parsed --lrm path to the oracle."""
    with patch(
        "document_dependency_graph.compute_subclause_dependencies",
        return_value=[],
    ) as mock_oracle:
        document_dependency_graph.main([
            "--lrm", str(make_lrm),
            "--output", str(make_output),
        ])
    assert mock_oracle.call_args[0][1] == str(make_lrm)


def test_main_passes_model_to_oracle(make_lrm, make_output) -> None:
    """main() forwards the parsed --model to the oracle."""
    with patch(
        "document_dependency_graph.compute_subclause_dependencies",
        return_value=[],
    ) as mock_oracle:
        document_dependency_graph.main([
            "--lrm", str(make_lrm),
            "--output", str(make_output),
            "--model", "haiku",
        ])
    assert mock_oracle.call_args[1]["model"] == "haiku"


def test_main_writes_oracle_result_to_output(make_lrm, make_output) -> None:
    """main() writes a JSON file mapping the placeholder subclause to deps."""
    with patch(
        "document_dependency_graph.compute_subclause_dependencies",
        return_value=["4.4.1", "4.4.2"],
    ):
        document_dependency_graph.main([
            "--lrm", str(make_lrm),
            "--output", str(make_output),
        ])
    payload = json.loads(make_output.read_text())
    assert payload == {"4.4": ["4.4.1", "4.4.2"]}


def test_main_writes_single_entry_file(make_lrm, make_output) -> None:
    """The graph file contains exactly one entry (the placeholder)."""
    with patch(
        "document_dependency_graph.compute_subclause_dependencies",
        return_value=[],
    ):
        document_dependency_graph.main([
            "--lrm", str(make_lrm),
            "--output", str(make_output),
        ])
    payload = json.loads(make_output.read_text())
    assert len(payload) == 1


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("document_dependency_graph", run_name="__main__")
