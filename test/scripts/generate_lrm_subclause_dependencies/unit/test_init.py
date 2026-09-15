import contextlib
import json
import runpy
from collections.abc import Callable, Iterator
from pathlib import Path
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

import generate_lrm_subclause_dependencies


def test_parse_args_requires_lrm(make_output: Path) -> None:
    with pytest.raises(SystemExit):
        generate_lrm_subclause_dependencies.parse_args([
            "--output", str(make_output),
        ])


def test_parse_args_validates_lrm_exists(
    tmp_path: Path, make_output: Path,
) -> None:
    missing = tmp_path / "missing.pdf"
    with pytest.raises(SystemExit):
        generate_lrm_subclause_dependencies.parse_args([
            "--lrm", str(missing),
            "--output", str(make_output),
        ])


def test_parse_args_default_model(make_lrm: Path, make_output: Path) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.model == "sonnet"


def test_parse_args_explicit_model(make_lrm: Path, make_output: Path) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--model", "haiku",
    ])
    assert args.model == "haiku"


def test_parse_args_default_effort(make_lrm: Path, make_output: Path) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.effort == "medium"


def test_parse_args_explicit_effort(make_lrm: Path, make_output: Path) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--effort", "high",
    ])
    assert args.effort == "high"


def test_parse_args_requires_output(make_lrm: Path) -> None:
    with pytest.raises(SystemExit):
        generate_lrm_subclause_dependencies.parse_args([
            "--lrm", str(make_lrm),
        ])


def test_parse_args_output_value(make_lrm: Path, make_output: Path) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert str(args.output) == str(make_output)


def test_parse_args_default_jobs(make_lrm: Path, make_output: Path) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.jobs == 16


def test_parse_args_explicit_jobs(make_lrm: Path, make_output: Path) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--jobs", "3",
    ])
    assert args.jobs == 3


def test_parse_args_rejects_jobs_below_one(
    make_lrm: Path, make_output: Path,
) -> None:
    with pytest.raises(SystemExit):
        generate_lrm_subclause_dependencies.parse_args([
            "--lrm", str(make_lrm),
            "--output", str(make_output),
            "--jobs", "0",
        ])


def test_parse_args_commit_defaults_off(
    make_lrm: Path, make_output: Path,
) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.commit is False


def test_parse_args_commit_explicit(
    make_lrm: Path, make_output: Path,
) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--commit",
    ])
    assert args.commit is True


def test_parse_args_resume_defaults_off(
    make_lrm: Path, make_output: Path,
) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.resume is False


def test_parse_args_resume_explicit(
    make_lrm: Path, make_output: Path,
) -> None:
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--resume",
    ])
    assert args.resume is True


def test_main_walks_every_toc_entry(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, mock_record, _ = run_main(
        toc={"4.4": (10, 20), "5.6": (21, 30), "13.4": (31, 50)},
    )
    assert mock_record.call_count == 3


def test_main_writes_record_per_subclause(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    run_main(toc={"4.4": (10, 20), "5.6": (21, 30)})
    payload = json.loads(make_output.read_text())
    assert set(payload["records"]) == {"4.4", "5.6"}


def test_main_writes_pretty_printed_json(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    run_main(toc={"4.4": (10, 20)})
    assert "\n  " in make_output.read_text()


def test_main_record_payload(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    record = {"dependencies": ["3.14.3"]}
    run_main(record=record)
    payload = json.loads(make_output.read_text())
    assert payload["records"]["4.4"] == record


def test_main_writes_order_section(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    run_main(toc={"4.4": (10, 20), "5.6": (21, 30)})
    payload = json.loads(make_output.read_text())
    assert sorted(g[0] for g in payload["order"]) == ["4.4", "5.6"]


def test_main_forwards_model_to_record_builder(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, mock_record, _ = run_main(extra_argv=["--model", "haiku"])
    assert mock_record.call_args[1]["model"] == "haiku"


def test_main_forwards_effort_to_record_builder(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, mock_record, _ = run_main(extra_argv=["--effort", "high"])
    assert mock_record.call_args[1]["effort"] == "high"


def test_main_forwards_lrm_to_record_builder(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_lrm: Path,
) -> None:
    _, mock_record, _ = run_main()
    assert mock_record.call_args[0][1] == str(make_lrm)


def test_main_passes_lrm_to_load_toc(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_lrm: Path,
) -> None:
    mock_toc, _, _ = run_main(toc={})
    assert mock_toc.call_args[0][0] == str(make_lrm)


def test_main_skips_commit_when_flag_unset(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, _, mock_commit = run_main()
    assert mock_commit.call_count == 0


def test_main_commit_output_called_per_subclause(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, _, mock_commit = run_main(
        toc={"4.4": (10, 20), "5.6": (21, 30), "13.4": (31, 50)},
        extra_argv=["--commit"],
    )
    assert mock_commit.call_count == 3


def test_main_passes_output_path_to_commit(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    _, _, mock_commit = run_main(extra_argv=["--commit"])
    assert mock_commit.call_args[0][0] == make_output


_TWO_SUBCLAUSE_TOC: dict[str, tuple[int, int]] = {
    "4.4": (10, 20), "5.6": (21, 30),
}


def _commit_messages(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    toc: dict[str, tuple[int, int]],
) -> list[str]:
    _, _, mock_commit = run_main(toc=toc, extra_argv=["--commit"])
    return [call.kwargs["message"] for call in mock_commit.call_args_list]


def test_main_commit_message_includes_progress(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    assert _commit_messages(run_main, _TWO_SUBCLAUSE_TOC) == [
        "generate_lrm_subclause_dependencies: checkpoint 1/2 answered",
        "generate_lrm_subclause_dependencies: checkpoint 2/2 answered",
    ]


def test_main_guard_invokes_main() -> None:
    with pytest.raises(SystemExit):
        runpy.run_module("generate_lrm_subclause_dependencies", run_name="__main__")


_CACHED_RECORD: dict[str, Any] = {"dependencies": ["3.14.3"]}
_FRESH_RECORD: dict[str, Any] = {"dependencies": []}


def _checkpoint_argv(
    make_lrm: Path, make_output: Path, *, resume: bool = False,
    jobs: str = "1",
) -> list[str]:
    argv = [
        "--lrm", str(make_lrm), "--output", str(make_output),
        "--jobs", jobs,
    ]
    if resume:
        argv.append("--resume")
    return argv


@contextlib.contextmanager
def _stub_walk(
    toc: dict[str, tuple[int, int]],
    *,
    return_value: dict[str, Any] | None = None,
    side_effect: list[Any] | None = None,
) -> Iterator[MagicMock]:
    record_kwargs: dict[str, Any] = (
        {"side_effect": side_effect}
        if side_effect is not None
        else {"return_value": return_value}
    )
    toc_p = patch("generate_lrm_subclause_dependencies.load_toc", return_value=toc)
    rec_p = patch(
        "generate_lrm_subclause_dependencies.build_subclause_record",
        **record_kwargs,
    )
    com_p = patch("generate_lrm_subclause_dependencies.commit_output")
    cln_p = patch("generate_lrm_subclause_dependencies.assert_clean_tree")
    with toc_p, com_p, cln_p, rec_p as mock_record:
        with contextlib.suppress(RuntimeError):
            yield mock_record


def _seed_checkpoint(
    make_output: Path, records: dict[str, dict[str, Any]],
) -> None:
    make_output.write_text(json.dumps({"records": records}))


def _run_main(
    make_lrm: Path, make_output: Path, *, resume: bool = False,
) -> None:
    generate_lrm_subclause_dependencies.main(
        _checkpoint_argv(make_lrm, make_output, resume=resume),
    )


_TWO_TOC: dict[str, tuple[int, int]] = {"4.4": (10, 20), "5.6": (21, 30)}
_CRASH_SIDE_EFFECT: list[Any] = [_FRESH_RECORD, RuntimeError("oracle exploded")]


def test_main_resume_reuses_cached_record(
    make_lrm: Path, make_output: Path,
) -> None:
    _seed_checkpoint(make_output, {"4.4": _CACHED_RECORD})
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD):
        _run_main(make_lrm, make_output, resume=True)
    payload = json.loads(make_output.read_text())
    assert payload["records"]["4.4"] == _CACHED_RECORD


def test_main_resume_skips_oracle_for_cached_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    _seed_checkpoint(make_output, {"4.4": _CACHED_RECORD})
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD) as mock_record:
        _run_main(make_lrm, make_output, resume=True)
    assert [c.args[0] for c in mock_record.call_args_list] == ["5.6"]


def test_main_crash_persists_completed_records(
    make_lrm: Path, make_output: Path,
) -> None:
    with _stub_walk(_TWO_TOC, side_effect=_CRASH_SIDE_EFFECT):
        _run_main(make_lrm, make_output)
    payload = json.loads(make_output.read_text())
    assert payload["records"] == {"4.4": _FRESH_RECORD}


def test_main_partial_checkpoint_includes_order_section(
    make_lrm: Path, make_output: Path,
) -> None:
    with _stub_walk(_TWO_TOC, side_effect=_CRASH_SIDE_EFFECT):
        _run_main(make_lrm, make_output)
    payload = json.loads(make_output.read_text())
    assert payload["order"] == [["4.4"]]


def test_main_drops_cached_records_not_in_toc(
    make_lrm: Path, make_output: Path,
) -> None:
    _seed_checkpoint(make_output, {"old.1": _CACHED_RECORD})
    with _stub_walk({"4.4": (10, 20)}, return_value=_FRESH_RECORD):
        _run_main(make_lrm, make_output, resume=True)
    payload = json.loads(make_output.read_text())
    assert "old.1" not in payload["records"]


def test_main_no_checkpoint_runs_every_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD) as mock_record:
        _run_main(make_lrm, make_output)
    assert mock_record.call_count == 2


def test_main_without_resume_ignores_existing_output(
    make_lrm: Path, make_output: Path,
) -> None:
    _seed_checkpoint(make_output, {"4.4": _CACHED_RECORD})
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD) as mock_record:
        _run_main(make_lrm, make_output)
    assert mock_record.call_count == 2


def test_main_resume_with_no_existing_output_runs_fresh(
    make_lrm: Path, make_output: Path,
) -> None:
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD) as mock_record:
        _run_main(make_lrm, make_output, resume=True)
    assert mock_record.call_count == 2


@contextlib.contextmanager
def _stub_run_with_clean(
    toc: dict[str, tuple[int, int]],
) -> Iterator[MagicMock]:
    toc_p = patch("generate_lrm_subclause_dependencies.load_toc", return_value=toc)
    rec_p = patch(
        "generate_lrm_subclause_dependencies.build_subclause_record",
        return_value=_FRESH_RECORD,
    )
    com_p = patch("generate_lrm_subclause_dependencies.commit_output")
    cln_p = patch("generate_lrm_subclause_dependencies.assert_clean_tree")
    with toc_p, rec_p, com_p, cln_p as mock_clean:
        yield mock_clean


def test_main_asserts_clean_tree_when_commit(
    make_lrm: Path, make_output: Path,
) -> None:
    argv = _checkpoint_argv(make_lrm, make_output) + ["--commit"]
    with _stub_run_with_clean(_TWO_TOC) as mock_clean:
        generate_lrm_subclause_dependencies.main(argv)
    assert mock_clean.call_count == 1


def test_main_skips_assert_clean_tree_without_commit(
    make_lrm: Path, make_output: Path,
) -> None:
    argv = _checkpoint_argv(make_lrm, make_output)
    with _stub_run_with_clean(_TWO_TOC) as mock_clean:
        generate_lrm_subclause_dependencies.main(argv)
    assert mock_clean.call_count == 0


def test_main_empty_toc_writes_empty_payload(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    run_main(toc={})
    payload = json.loads(make_output.read_text())
    assert payload == {"records": {}, "order": []}


def _capture_snapshots(
    make_lrm: Path, make_output: Path, *, resume: bool = False,
) -> list[dict[str, Any]]:
    snapshots: list[dict[str, Any]] = []

    def _snapshot(path: Path, **_kwargs: Any) -> None:
        snapshots.append(json.loads(path.read_text()))

    toc_p = patch(
        "generate_lrm_subclause_dependencies.load_toc",
        return_value=_TWO_TOC,
    )
    rec_p = patch(
        "generate_lrm_subclause_dependencies.build_subclause_record",
        return_value=_FRESH_RECORD,
    )
    com_p = patch(
        "generate_lrm_subclause_dependencies.commit_output",
        side_effect=_snapshot,
    )
    cln_p = patch("generate_lrm_subclause_dependencies.assert_clean_tree")
    argv = _checkpoint_argv(make_lrm, make_output, resume=resume) + ["--commit"]
    with toc_p, rec_p, com_p, cln_p:
        generate_lrm_subclause_dependencies.main(argv)
    return snapshots


def test_main_each_checkpoint_includes_order(
    make_lrm: Path, make_output: Path,
) -> None:
    snapshots = _capture_snapshots(make_lrm, make_output)
    assert all("order" in snap for snap in snapshots)


def test_main_resume_first_checkpoint_has_full_cached_records(
    make_lrm: Path, make_output: Path,
) -> None:
    _seed_checkpoint(
        make_output,
        {"4.4": _CACHED_RECORD, "5.6": _CACHED_RECORD},
    )
    snapshots = _capture_snapshots(make_lrm, make_output, resume=True)
    assert set(snapshots[0]["records"]) == {"4.4", "5.6"}


_AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "23": (100, 129),
    "23.1": (100, 109),
}
_SINGLETON_TOC: dict[str, tuple[int, int]] = {"2": (10, 12)}
_ANNEX_AGGREGATE_TOC: dict[str, tuple[int, int]] = {
    "A": (900, 939),
    "A.1": (900, 919),
}
_ANNEX_SINGLETON_TOC: dict[str, tuple[int, int]] = {"B": (940, 949)}


def test_main_skips_aggregate_chapter(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, mock_record, _ = run_main(toc=_AGGREGATE_TOC)
    walked = [c.args[0] for c in mock_record.call_args_list]
    assert "23" not in walked


def test_main_walks_subclauses_under_aggregate(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, mock_record, _ = run_main(toc=_AGGREGATE_TOC)
    walked = [c.args[0] for c in mock_record.call_args_list]
    assert walked == ["23.1"]


def test_main_walks_singleton_chapter(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, mock_record, _ = run_main(toc=_SINGLETON_TOC)
    walked = [c.args[0] for c in mock_record.call_args_list]
    assert walked == ["2"]


def test_main_skips_aggregate_annex(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, mock_record, _ = run_main(toc=_ANNEX_AGGREGATE_TOC)
    walked = [c.args[0] for c in mock_record.call_args_list]
    assert "A" not in walked


def test_main_walks_singleton_annex(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    _, mock_record, _ = run_main(toc=_ANNEX_SINGLETON_TOC)
    walked = [c.args[0] for c in mock_record.call_args_list]
    assert walked == ["B"]


def test_main_drops_aggregate_records_from_output(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    run_main(toc=_AGGREGATE_TOC)
    payload = json.loads(make_output.read_text())
    assert "23" not in payload["records"]


def test_main_progress_total_excludes_aggregates(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    assert _commit_messages(run_main, _AGGREGATE_TOC) == [
        "generate_lrm_subclause_dependencies: checkpoint 1/1 answered",
    ]


def test_main_resume_drops_cached_aggregate_record(
    make_lrm: Path, make_output: Path,
) -> None:
    _seed_checkpoint(
        make_output,
        {"23": _CACHED_RECORD, "23.1": _CACHED_RECORD},
    )
    with _stub_walk(_AGGREGATE_TOC, return_value=_FRESH_RECORD):
        _run_main(make_lrm, make_output, resume=True)
    payload = json.loads(make_output.read_text())
    assert "23" not in payload["records"]
