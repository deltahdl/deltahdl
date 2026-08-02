"""Unit tests for running the walk's oracle calls several at a time.

The walk costs one oracle call per subclause, and a call spends nearly
all of its time waiting on a session that is reading the LRM. These
tests cover the pool that overlaps those calls, the checkpoint cadence
that keeps the graph write off the per-answer path, and the move that
keeps the graph readable while it is being rewritten.
"""

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

# Four subclauses, so a pool of four overlaps all of them and a pool of
# one runs them in the order they were asked.
_FOUR_TOC: dict[str, tuple[int, int]] = {
    "4.4": (10, 20), "5.6": (21, 30), "6.7": (31, 40), "7.8": (41, 50),
}
_PARTIAL_SUFFIX = ".partial"


def _answered(_subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
    """Answer any subclause with the same empty record."""
    return _RECORD


def _walk(
    lrm: Path,
    output: Path,
    jobs: str,
    builder: Callable[..., dict[str, Any]],
    *,
    resume: bool = False,
) -> MagicMock:
    """Walk the four-subclause table with *builder* answering each call.

    Runs with --commit so the checkpoint cadence is observable: the
    returned commit_output mock is called once per checkpoint written.
    """
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
    """Return the records section of the graph written to *output*."""
    payload: dict[str, Any] = json.loads(output.read_text())
    records: dict[str, Any] = payload["records"]
    return records


# --- the pool ---------------------------------------------------------------


def test_two_oracle_calls_are_in_flight_at_once(
    make_lrm: Path, make_output: Path,
) -> None:
    """A second call reaches the barrier while the first is waiting on it.

    The barrier opens only once two callers have arrived. A walk that
    ran its calls one after another would leave the first waiting alone
    until the barrier timed out, which breaks the barrier and raises
    out of the call rather than reaching the assertion.
    """
    barrier = threading.Barrier(2, timeout=30)

    def _paired(_subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
        barrier.wait()
        return _RECORD

    _walk(make_lrm, make_output, "2", _paired)
    assert not barrier.broken


def test_a_concurrent_walk_records_every_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    """Overlapping the calls drops none of them."""
    _walk(make_lrm, make_output, "4", _answered)
    assert set(_written_records(make_output)) == set(_FOUR_TOC)


def test_a_concurrent_walk_answers_each_subclause_once(
    make_lrm: Path, make_output: Path,
) -> None:
    """The pool buys one answer per subclause, not one per worker."""
    calls: list[str] = []

    def _counted(subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
        calls.append(subclause)
        return _RECORD

    _walk(make_lrm, make_output, "4", _counted)
    assert sorted(calls) == sorted(_FOUR_TOC)


# --- checkpoint cadence -----------------------------------------------------


def test_a_concurrent_walk_checkpoints_less_often_than_once_per_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    """The graph write comes off the per-answer path when calls overlap.

    Recomputing the cycle groups and the order over every answer so far
    and serialising the whole graph is the one serial section of an
    otherwise parallel walk, so four answers cost fewer than four
    writes.
    """
    commit = _walk(make_lrm, make_output, "4", _answered)
    assert commit.call_count < len(_FOUR_TOC)


def test_a_one_job_walk_checkpoints_once_per_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    """The interval is the pool size, so the narrowest pool writes per answer."""
    commit = _walk(make_lrm, make_output, "1", _answered)
    assert commit.call_count == len(_FOUR_TOC)


def test_the_checkpoint_message_counts_a_whole_batch(
    make_lrm: Path, make_output: Path,
) -> None:
    """A checkpoint covering four answers reports four of them, not one."""
    commit = _walk(make_lrm, make_output, "4", _answered)
    assert commit.call_args[1]["message"] == (
        "generate_lrm_subclause_dependencies: checkpoint 4/4 answered"
    )


# --- what survives a failure ------------------------------------------------


def test_a_pool_wider_than_the_walk_writes_once_on_the_way_out(
    make_lrm: Path, make_output: Path,
) -> None:
    """Four answers under a pool of eight never reach the interval.

    The interval is the pool size, so nothing is written until the walk
    ends. Every answer is therefore in hand and unwritten at that
    point, and the write on the way out is the only one there is.
    """
    commit = _walk(make_lrm, make_output, "8", _answered)
    assert commit.call_count == 1


def test_a_pool_wider_than_the_walk_writes_every_answer(
    make_lrm: Path, make_output: Path,
) -> None:
    """The single write on the way out carries every answer bought."""
    _walk(make_lrm, make_output, "8", _answered)
    assert set(_written_records(make_output)) == set(_FOUR_TOC)


def _one_fails(subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
    """Answer every subclause of the four-entry table except the last one.

    The last one raises instead, standing in for an oracle call that
    fails partway through a walk.
    """
    if subclause == "7.8":
        raise RuntimeError("oracle exploded")
    return _RECORD


def _walk_past_the_failure(lrm: Path, output: Path) -> None:
    """Run the walk whose last call raises and absorb the raise.

    The raise itself is pinned by its own test. What is wanted here is
    the state the walk left on disk, which is only reachable once the
    failure has been let past.
    """
    with contextlib.suppress(RuntimeError):
        _walk(lrm, output, "8", _one_fails)


def test_a_failed_oracle_call_raises_out_of_the_walk(
    make_lrm: Path, make_output: Path,
) -> None:
    """A call that fails inside the pool surfaces rather than being dropped.

    A pool reports a failure only to whoever reads the future, so a
    walk that never read one would finish quietly with a subclause
    missing from the graph.
    """
    with pytest.raises(RuntimeError):
        _walk(make_lrm, make_output, "8", _one_fails)


def test_a_failed_walk_still_leaves_a_readable_checkpoint(
    make_lrm: Path, make_output: Path,
) -> None:
    """A walk that raises leaves a checkpoint a resumed run can read.

    How many answers were in hand when the failure surfaced depends on
    which of the overlapping calls had finished by then, so this pins
    the file being written and complete rather than a particular number
    of records in it. The output does not exist before the walk, so a
    walk that wrote nothing on its way out fails to be read here at
    all.
    """
    _walk_past_the_failure(make_lrm, make_output)
    assert "order" in json.loads(make_output.read_text())


def test_a_fully_cached_resume_still_writes_the_output(
    make_lrm: Path, make_output: Path,
) -> None:
    """With nothing for the pool to run, the graph is still written.

    The seeded checkpoint carries records and no order section, so an
    order section on disk afterwards is proof a checkpoint was written
    rather than the seed being left untouched.
    """
    make_output.write_text(json.dumps({
        "records": {sub: _RECORD for sub in _FOUR_TOC},
    }))

    def _unused(_subclause: str, _lrm: str, **_kwargs: Any) -> dict[str, Any]:
        raise RuntimeError("a cached subclause reached the oracle")

    _walk(make_lrm, make_output, "4", _unused, resume=True)
    assert "order" in json.loads(make_output.read_text())


# --- the order records are written in ---------------------------------------


def test_records_are_written_in_table_of_contents_order(
    make_lrm: Path, make_output: Path,
) -> None:
    """Answers arriving out of order are written in the order they were asked.

    Each call waits for the next subclause to answer first, so the
    answers complete in exactly the reverse of the walk. Comparing the
    written order against the completion order as well as against the
    table of contents keeps the test from passing on a run where the
    two happened to coincide.
    """
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


# --- moving the checkpoint into place ---------------------------------------


def _partial_of(output: Path) -> Path:
    """Return the path a checkpoint is staged at before it is moved in."""
    return output.with_name(output.name + _PARTIAL_SUFFIX)


def test_the_checkpoint_is_not_written_in_place(make_output: Path) -> None:
    """With the move stubbed out, the output keeps the content it had.

    A payload written straight into the output would have replaced it,
    and a reader arriving mid-write would have seen half a file.
    """
    make_output.write_text("previous")
    with patch.object(Path, "replace"):
        _write_checkpoint(make_output, {"4.4": _RECORD}, ["4.4"])
    assert make_output.read_text() == "previous"


def test_the_staged_checkpoint_carries_the_whole_payload(
    make_output: Path,
) -> None:
    """The file moved into place is a complete checkpoint, not a fragment."""
    with patch.object(Path, "replace"):
        _write_checkpoint(make_output, {"4.4": _RECORD}, ["4.4"])
    assert json.loads(_partial_of(make_output).read_text())["records"] == {
        "4.4": _RECORD,
    }


def test_no_staged_file_is_left_beside_the_output(make_output: Path) -> None:
    """A completed checkpoint leaves nothing beside the output.

    A leftover would be an untracked file in the tree a committing walk
    pushes from.
    """
    _write_checkpoint(make_output, {"4.4": _RECORD}, ["4.4"])
    assert not _partial_of(make_output).exists()
