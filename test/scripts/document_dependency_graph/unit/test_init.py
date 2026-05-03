"""Unit tests for the document_dependency_graph argparse wrapper."""

import json
import runpy
from typing import Any
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


def test_parse_args_commit_defaults_off(make_lrm, make_output) -> None:
    """--commit defaults to False so a plain run never touches git."""
    args = document_dependency_graph.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.commit is False


def test_parse_args_commit_explicit(make_lrm, make_output) -> None:
    """--commit sets args.commit to True."""
    args = document_dependency_graph.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--commit",
    ])
    assert args.commit is True


def test_main_walks_every_toc_entry(run_main) -> None:
    """main() invokes build_subclause_record once per load_toc entry."""
    _, mock_record, _ = run_main(
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
    _, mock_record, _ = run_main(extra_argv=["--model", "haiku"])
    assert mock_record.call_args[1]["model"] == "haiku"


def test_main_forwards_lrm_to_record_builder(run_main, make_lrm) -> None:
    """main() forwards the parsed --lrm to build_subclause_record."""
    _, mock_record, _ = run_main()
    assert mock_record.call_args[0][1] == str(make_lrm)


def test_main_passes_lrm_to_load_toc(run_main, make_lrm) -> None:
    """main() reads the table of contents from the --lrm path."""
    mock_toc, _, _ = run_main(toc={})
    assert mock_toc.call_args[0][0] == str(make_lrm)


def test_main_skips_commit_when_flag_unset(run_main) -> None:
    """Without --commit, main() does not call commit_output."""
    _, _, mock_commit = run_main()
    assert mock_commit.call_count == 0


def test_main_calls_commit_output_when_commit_flag(run_main) -> None:
    """With --commit, main() calls commit_output exactly once."""
    _, _, mock_commit = run_main(extra_argv=["--commit"])
    assert mock_commit.call_count == 1


def test_main_passes_output_path_to_commit(run_main, make_output) -> None:
    """commit_output is called with the parsed --output path."""
    _, _, mock_commit = run_main(extra_argv=["--commit"])
    assert mock_commit.call_args[0][0] == make_output


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("document_dependency_graph", run_name="__main__")


# --- Checkpoint / resume ----------------------------------------------------


_CACHED_RECORD: dict[str, Any] = {
    "dependencies": ["3.14.3"],
    "proofs": {"3.14.3": "Cached sentence."},
    "prerequisites": {"3.14.3": "cached prereq"},
}
_FRESH_RECORD: dict[str, Any] = {
    "dependencies": [],
    "proofs": {},
    "prerequisites": {},
}


def _checkpoint_argv(make_lrm, make_output) -> list[str]:
    """Build the canonical argv for checkpoint tests."""
    return ["--lrm", str(make_lrm), "--output", str(make_output)]


def _patch_walk(toc, *, return_value=None, side_effect=None):
    """Stack patches on load_toc/build_subclause_record/commit_output."""
    record_kwargs = (
        {"side_effect": side_effect}
        if side_effect is not None
        else {"return_value": return_value}
    )
    return (
        patch("document_dependency_graph.load_toc", return_value=toc),
        patch(
            "document_dependency_graph.build_subclause_record",
            **record_kwargs,
        ),
        patch("document_dependency_graph.commit_output"),
    )


def test_main_resume_reuses_cached_record(make_lrm, make_output) -> None:
    """A pre-existing records section is reused verbatim for the cached subclause."""
    make_output.write_text(json.dumps({"records": {"4.4": _CACHED_RECORD}}))
    toc_p, rec_p, com_p = _patch_walk(
        {"4.4": (10, 20), "5.6": (21, 30)}, return_value=_FRESH_RECORD,
    )
    with toc_p, rec_p, com_p:
        document_dependency_graph.main(_checkpoint_argv(make_lrm, make_output))
    payload = json.loads(make_output.read_text())
    assert payload["records"]["4.4"] == _CACHED_RECORD


def test_main_resume_skips_oracle_for_cached_subclause(make_lrm, make_output) -> None:
    """build_subclause_record is not called for a cached subclause."""
    make_output.write_text(json.dumps({"records": {"4.4": _CACHED_RECORD}}))
    toc_p, rec_p, com_p = _patch_walk(
        {"4.4": (10, 20), "5.6": (21, 30)}, return_value=_FRESH_RECORD,
    )
    with toc_p, com_p, rec_p as mock_record:
        document_dependency_graph.main(_checkpoint_argv(make_lrm, make_output))
    assert [c.args[0] for c in mock_record.call_args_list] == ["5.6"]


def _run_main_capturing_crash(make_lrm, make_output, toc_p, rec_p, com_p) -> None:
    """Run main() and swallow the seeded crash so the file state can be inspected."""
    with toc_p, rec_p, com_p:
        try:
            document_dependency_graph.main(
                _checkpoint_argv(make_lrm, make_output),
            )
        except RuntimeError:
            pass


def test_main_crash_persists_completed_records(make_lrm, make_output) -> None:
    """A crash mid-walk leaves prior subclauses persisted in --output."""
    side = [_FRESH_RECORD, RuntimeError("oracle exploded")]
    toc_p, rec_p, com_p = _patch_walk(
        {"4.4": (10, 20), "5.6": (21, 30)}, side_effect=side,
    )
    _run_main_capturing_crash(make_lrm, make_output, toc_p, rec_p, com_p)
    payload = json.loads(make_output.read_text())
    assert payload["records"] == {"4.4": _FRESH_RECORD}


def test_main_partial_checkpoint_omits_order_section(make_lrm, make_output) -> None:
    """A crash mid-walk leaves no order section since the walk did not finish."""
    side = [_FRESH_RECORD, RuntimeError("oracle exploded")]
    toc_p, rec_p, com_p = _patch_walk(
        {"4.4": (10, 20), "5.6": (21, 30)}, side_effect=side,
    )
    _run_main_capturing_crash(make_lrm, make_output, toc_p, rec_p, com_p)
    payload = json.loads(make_output.read_text())
    assert "order" not in payload


def test_main_drops_cached_records_not_in_toc(make_lrm, make_output) -> None:
    """Cached records for subclauses no longer in TOC are dropped from output."""
    stale = {"old.1": _CACHED_RECORD}
    make_output.write_text(json.dumps({"records": stale}))
    toc_p, rec_p, com_p = _patch_walk(
        {"4.4": (10, 20)}, return_value=_FRESH_RECORD,
    )
    with toc_p, rec_p, com_p:
        document_dependency_graph.main(_checkpoint_argv(make_lrm, make_output))
    payload = json.loads(make_output.read_text())
    assert "old.1" not in payload["records"]


def test_main_no_checkpoint_runs_every_subclause(make_lrm, make_output) -> None:
    """Without a checkpoint file, build_subclause_record runs for every TOC entry."""
    toc_p, rec_p, com_p = _patch_walk(
        {"4.4": (10, 20), "5.6": (21, 30)}, return_value=_FRESH_RECORD,
    )
    with toc_p, com_p, rec_p as mock_record:
        document_dependency_graph.main(_checkpoint_argv(make_lrm, make_output))
    assert mock_record.call_count == 2
