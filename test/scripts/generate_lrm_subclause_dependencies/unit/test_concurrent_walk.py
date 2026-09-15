import contextlib
import json
import threading
from collections.abc import Callable
from pathlib import Path
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

import generate_lrm_subclause_dependencies
from generate_lrm_subclause_dependencies import _write_checkpoint


_RECORD: dict[str, Any] = {"dependencies": []}

_FOUR_TOC: dict[str, tuple[int, int]] = {
    "4.4": (10, 20), "5.6": (21, 30), "6.7": (31, 40), "7.8": (41, 50),
}
_PARTIAL_SUFFIX = ".partial"


def _answered(_subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
    return _RECORD


def _walk(
    lrm: Path,
    output: Path,
    jobs: str,
    builder: Callable[..., dict[str, Any]],
    *,
    resume: bool = False,
) -> MagicMock:
    argv = [
        "--lrm", str(lrm), "--output", str(output),
        "--jobs", jobs, "--commit",
    ]
    if resume:
        argv.append("--resume")
    toc_patch = patch(
        "generate_lrm_subclause_dependencies.load_toc",
        return_value=_FOUR_TOC,
    )
    builder_patch = patch(
        "generate_lrm_subclause_dependencies.build_subclause_record",
        side_effect=builder,
    )
    clean_patch = patch(
        "generate_lrm_subclause_dependencies.assert_clean_tree",
    )
    commit_patch = patch(
        "generate_lrm_subclause_dependencies.commit_output",
    )
    with toc_patch, builder_patch, clean_patch, commit_patch as mock_commit:
        generate_lrm_subclause_dependencies.main(argv)
    return mock_commit


def _written_records(output: Path) -> dict[str, Any]:
    payload: dict[str, Any] = json.loads(output.read_text())
    records: dict[str, Any] = payload["records"]
    return records


def test_two_oracle_calls_are_in_flight_at_once(
    make_lrm: Path, make_output: Path,
) -> None:
    barrier = threading.Barrier(2, timeout=30)

    def _paired(_subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
        barrier.wait()
        return _RECORD

    _walk(make_lrm, make_output, "2", _paired)
    assert not barrier.broken


def test_a_concurrent_walk_records_every_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    _walk(make_lrm, make_output, "4", _answered)
    assert set(_written_records(make_output)) == set(_FOUR_TOC)


def test_a_concurrent_walk_answers_each_subclause_once(
    make_lrm: Path, make_output: Path,
) -> None:
    calls: list[str] = []

    def _counted(subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
        calls.append(subclause)
        return _RECORD

    _walk(make_lrm, make_output, "4", _counted)
    assert sorted(calls) == sorted(_FOUR_TOC)


def test_a_concurrent_walk_checkpoints_less_often_than_once_per_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    commit = _walk(make_lrm, make_output, "4", _answered)
    assert commit.call_count < len(_FOUR_TOC)


def test_a_one_job_walk_checkpoints_once_per_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    commit = _walk(make_lrm, make_output, "1", _answered)
    assert commit.call_count == len(_FOUR_TOC)


def test_the_checkpoint_message_counts_a_whole_batch(
    make_lrm: Path, make_output: Path,
) -> None:
    commit = _walk(make_lrm, make_output, "4", _answered)
    assert commit.call_args[1]["message"] == (
        "generate_lrm_subclause_dependencies: checkpoint 4/4 answered"
    )


def test_a_pool_wider_than_the_walk_writes_once_on_the_way_out(
    make_lrm: Path, make_output: Path,
) -> None:
    commit = _walk(make_lrm, make_output, "8", _answered)
    assert commit.call_count == 1


def test_a_pool_wider_than_the_walk_writes_every_answer(
    make_lrm: Path, make_output: Path,
) -> None:
    _walk(make_lrm, make_output, "8", _answered)
    assert set(_written_records(make_output)) == set(_FOUR_TOC)


def _one_fails(subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
    if subclause == "7.8":
        raise RuntimeError("oracle exploded")
    return _RECORD


def _walk_past_the_failure(lrm: Path, output: Path) -> None:
    with contextlib.suppress(RuntimeError):
        _walk(lrm, output, "8", _one_fails)


def test_a_failed_oracle_call_raises_out_of_the_walk(
    make_lrm: Path, make_output: Path,
) -> None:
    with pytest.raises(RuntimeError):
        _walk(make_lrm, make_output, "8", _one_fails)


def test_a_failed_walk_still_leaves_a_readable_checkpoint(
    make_lrm: Path, make_output: Path,
) -> None:
    _walk_past_the_failure(make_lrm, make_output)
    assert "order" in json.loads(make_output.read_text())


def test_a_fully_cached_resume_still_writes_the_output(
    make_lrm: Path, make_output: Path,
) -> None:
    make_output.write_text(json.dumps({
        "records": {sub: _RECORD for sub in _FOUR_TOC},
    }))

    def _unused(_subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
        raise RuntimeError("a cached subclause reached the oracle")

    _walk(make_lrm, make_output, "4", _unused, resume=True)
    assert "order" in json.loads(make_output.read_text())


def test_records_are_written_in_table_of_contents_order(
    make_lrm: Path, make_output: Path,
) -> None:
    walked = list(_FOUR_TOC)
    finished = {sub: threading.Event() for sub in walked}
    completions: list[str] = []

    def _answer_in_reverse(
        subclause: str, _lrm: str, **_kwargs: Any,
    ) -> dict[str, Any]:
        index = walked.index(subclause)
        if index + 1 < len(walked):
            finished[walked[index + 1]].wait(timeout=30)
        completions.append(subclause)
        finished[subclause].set()
        return _RECORD

    _walk(make_lrm, make_output, "4", _answer_in_reverse)
    assert list(_written_records(make_output)) == walked != completions


def _partial_of(output: Path) -> Path:
    return output.with_name(output.name + _PARTIAL_SUFFIX)


def test_the_checkpoint_is_not_written_in_place(make_output: Path) -> None:
    make_output.write_text("previous")
    with patch.object(Path, "replace"):
        _write_checkpoint(make_output, {"4.4": _RECORD}, ["4.4"])
    assert make_output.read_text() == "previous"


def test_the_staged_checkpoint_carries_the_whole_payload(
    make_output: Path,
) -> None:
    with patch.object(Path, "replace"):
        _write_checkpoint(make_output, {"4.4": _RECORD}, ["4.4"])
    assert json.loads(_partial_of(make_output).read_text())["records"] == {
        "4.4": _RECORD,
    }


def test_no_staged_file_is_left_beside_the_output(make_output: Path) -> None:
    _write_checkpoint(make_output, {"4.4": _RECORD}, ["4.4"])
    assert not _partial_of(make_output).exists()
