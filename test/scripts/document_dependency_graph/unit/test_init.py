"""Unit tests for the document_dependency_graph argparse wrapper."""

import json
import runpy

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


def test_main_walks_every_toc_entry(run_main) -> None:
    """main() invokes build_subclause_record once per load_toc entry."""
    _, mock_record = run_main(
        toc={"4.4": (10, 20), "5.6": (21, 30), "13.4": (31, 50)},
    )
    assert mock_record.call_count == 3


def test_main_writes_record_per_subclause(run_main, make_output) -> None:
    """records/ section contains one entry per load_toc subclause, keyed by id."""
    run_main(toc={"4.4": (10, 20), "5.6": (21, 30)})
    payload = json.loads(make_output.read_text())
    assert set(payload["records"]) == {"4.4", "5.6"}


def test_main_record_payload(run_main, make_output) -> None:
    """Each entry under records/ is the build_subclause_record payload."""
    record = {
        "dependencies": ["3.14.3"],
        "proofs": {"3.14.3": "Sentence."},
        "prerequisites": {"3.14.3": "elaboration"},
    }
    run_main(record=record)
    payload = json.loads(make_output.read_text())
    assert payload["records"]["4.4"] == record


def test_main_writes_order_section(run_main, make_output) -> None:
    """The output file carries an order section with one group per subclause."""
    run_main(toc={"4.4": (10, 20), "5.6": (21, 30)})
    payload = json.loads(make_output.read_text())
    assert sorted(g[0] for g in payload["order"]) == ["4.4", "5.6"]


def test_main_forwards_model_to_record_builder(run_main) -> None:
    """main() forwards the parsed --model to build_subclause_record."""
    _, mock_record = run_main(extra_argv=["--model", "haiku"])
    assert mock_record.call_args[1]["model"] == "haiku"


def test_main_forwards_lrm_to_record_builder(run_main, make_lrm) -> None:
    """main() forwards the parsed --lrm to build_subclause_record."""
    _, mock_record = run_main()
    assert mock_record.call_args[0][1] == str(make_lrm)


def test_main_passes_lrm_to_load_toc(run_main, make_lrm) -> None:
    """main() reads the table of contents from the --lrm path."""
    mock_toc, _ = run_main(toc={})
    assert mock_toc.call_args[0][0] == str(make_lrm)


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("document_dependency_graph", run_name="__main__")
