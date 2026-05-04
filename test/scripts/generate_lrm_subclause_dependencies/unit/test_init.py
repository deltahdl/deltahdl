"""Unit tests for the generate_lrm_subclause_dependencies argparse wrapper."""

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
    """--lrm is required."""
    with pytest.raises(SystemExit):
        generate_lrm_subclause_dependencies.parse_args([
            "--output", str(make_output),
        ])


def test_parse_args_validates_lrm_exists(
    tmp_path: Path, make_output: Path,
) -> None:
    """--lrm must point at an existing file."""
    missing = tmp_path / "missing.pdf"
    with pytest.raises(SystemExit):
        generate_lrm_subclause_dependencies.parse_args([
            "--lrm", str(missing),
            "--output", str(make_output),
        ])


def test_parse_args_default_model(make_lrm: Path, make_output: Path) -> None:
    """--model defaults to 'sonnet' for the dependency-graph walk."""
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.model == "sonnet"


def test_parse_args_explicit_model(make_lrm: Path, make_output: Path) -> None:
    """--model accepts an explicit value."""
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--model", "haiku",
    ])
    assert args.model == "haiku"


def test_parse_args_default_effort(make_lrm: Path, make_output: Path) -> None:
    """--effort defaults to 'medium'."""
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.effort == "medium"


def test_parse_args_explicit_effort(make_lrm: Path, make_output: Path) -> None:
    """--effort accepts an explicit value from the allowed set."""
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--effort", "high",
    ])
    assert args.effort == "high"


def test_parse_args_requires_output(make_lrm: Path) -> None:
    """--output is required."""
    with pytest.raises(SystemExit):
        generate_lrm_subclause_dependencies.parse_args([
            "--lrm", str(make_lrm),
        ])


def test_parse_args_output_value(make_lrm: Path, make_output: Path) -> None:
    """--output is parsed and forwarded as the file path."""
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert str(args.output) == str(make_output)


def test_parse_args_commit_defaults_off(
    make_lrm: Path, make_output: Path,
) -> None:
    """--commit defaults to False so a plain run never touches git."""
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.commit is False


def test_parse_args_commit_explicit(
    make_lrm: Path, make_output: Path,
) -> None:
    """--commit sets args.commit to True."""
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--commit",
    ])
    assert args.commit is True


def test_parse_args_resume_defaults_off(
    make_lrm: Path, make_output: Path,
) -> None:
    """--resume defaults to False so a plain run never reads the prior --output."""
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
    ])
    assert args.resume is False


def test_parse_args_resume_explicit(
    make_lrm: Path, make_output: Path,
) -> None:
    """--resume sets args.resume to True."""
    args = generate_lrm_subclause_dependencies.parse_args([
        "--lrm", str(make_lrm),
        "--output", str(make_output),
        "--resume",
    ])
    assert args.resume is True


def test_main_walks_every_toc_entry(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    """main() invokes build_subclause_record once per load_toc entry."""
    _, mock_record, _ = run_main(
        toc={"4.4": (10, 20), "5.6": (21, 30), "13.4": (31, 50)},
    )
    assert mock_record.call_count == 3


def test_main_writes_record_per_subclause(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    """records/ section contains one entry per load_toc subclause, keyed by id."""
    run_main(toc={"4.4": (10, 20), "5.6": (21, 30)})
    payload = json.loads(make_output.read_text())
    assert set(payload["records"]) == {"4.4", "5.6"}


def test_main_record_payload(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    """Each entry under records/ is the build_subclause_record payload."""
    record = {"dependencies": ["3.14.3"]}
    run_main(record=record)
    payload = json.loads(make_output.read_text())
    assert payload["records"]["4.4"] == record


def test_main_writes_order_section(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    """The output file carries an order section with one group per subclause."""
    run_main(toc={"4.4": (10, 20), "5.6": (21, 30)})
    payload = json.loads(make_output.read_text())
    assert sorted(g[0] for g in payload["order"]) == ["4.4", "5.6"]


def test_main_forwards_model_to_record_builder(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    """main() forwards the parsed --model to build_subclause_record."""
    _, mock_record, _ = run_main(extra_argv=["--model", "haiku"])
    assert mock_record.call_args[1]["model"] == "haiku"


def test_main_forwards_effort_to_record_builder(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    """main() forwards the parsed --effort to build_subclause_record."""
    _, mock_record, _ = run_main(extra_argv=["--effort", "high"])
    assert mock_record.call_args[1]["effort"] == "high"


def test_main_forwards_lrm_to_record_builder(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_lrm: Path,
) -> None:
    """main() forwards the parsed --lrm to build_subclause_record."""
    _, mock_record, _ = run_main()
    assert mock_record.call_args[0][1] == str(make_lrm)


def test_main_passes_lrm_to_load_toc(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_lrm: Path,
) -> None:
    """main() reads the table of contents from the --lrm path."""
    mock_toc, _, _ = run_main(toc={})
    assert mock_toc.call_args[0][0] == str(make_lrm)


def test_main_skips_commit_when_flag_unset(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    """Without --commit, main() does not call commit_output."""
    _, _, mock_commit = run_main()
    assert mock_commit.call_count == 0


def test_main_calls_commit_output_when_commit_flag(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
) -> None:
    """With --commit, main() calls commit_output exactly once."""
    _, _, mock_commit = run_main(extra_argv=["--commit"])
    assert mock_commit.call_count == 1


def test_main_passes_output_path_to_commit(
    run_main: Callable[..., tuple[MagicMock, MagicMock, MagicMock]],
    make_output: Path,
) -> None:
    """commit_output is called with the parsed --output path."""
    _, _, mock_commit = run_main(extra_argv=["--commit"])
    assert mock_commit.call_args[0][0] == make_output


def test_main_guard_invokes_main() -> None:
    """Running as __main__ calls main()."""
    with pytest.raises(SystemExit):
        runpy.run_module("generate_lrm_subclause_dependencies", run_name="__main__")


# --- Checkpoint / resume ----------------------------------------------------


_CACHED_RECORD: dict[str, Any] = {"dependencies": ["3.14.3"]}
_FRESH_RECORD: dict[str, Any] = {"dependencies": []}


def _checkpoint_argv(
    make_lrm: Path, make_output: Path, *, resume: bool = False,
) -> list[str]:
    """Build the canonical argv for checkpoint tests."""
    argv = ["--lrm", str(make_lrm), "--output", str(make_output)]
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
    """Stub load_toc/build_subclause_record/commit_output for one main() run.

    Yields the build_subclause_record mock so tests can assert on its
    call list. ``side_effect`` is a non-None list-like to seed varied
    or raising returns; otherwise ``return_value`` is the same record
    on every call. The seeded crash from a RuntimeError side_effect is
    swallowed so the test can inspect the on-disk checkpoint state.
    """
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
    with toc_p, com_p, rec_p as mock_record:
        with contextlib.suppress(RuntimeError):
            yield mock_record


def _seed_checkpoint(
    make_output: Path, records: dict[str, dict[str, Any]],
) -> None:
    """Pre-populate --output with a partial records section."""
    make_output.write_text(json.dumps({"records": records}))


def _run_main(
    make_lrm: Path, make_output: Path, *, resume: bool = False,
) -> None:
    """Invoke main() with the canonical argv for checkpoint tests."""
    generate_lrm_subclause_dependencies.main(
        _checkpoint_argv(make_lrm, make_output, resume=resume),
    )


_TWO_TOC: dict[str, tuple[int, int]] = {"4.4": (10, 20), "5.6": (21, 30)}
_CRASH_SIDE_EFFECT: list[Any] = [_FRESH_RECORD, RuntimeError("oracle exploded")]


def test_main_resume_reuses_cached_record(
    make_lrm: Path, make_output: Path,
) -> None:
    """A pre-existing records section is reused verbatim for the cached subclause."""
    _seed_checkpoint(make_output, {"4.4": _CACHED_RECORD})
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD):
        _run_main(make_lrm, make_output, resume=True)
    payload = json.loads(make_output.read_text())
    assert payload["records"]["4.4"] == _CACHED_RECORD


def test_main_resume_skips_oracle_for_cached_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    """build_subclause_record is not called for a cached subclause."""
    _seed_checkpoint(make_output, {"4.4": _CACHED_RECORD})
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD) as mock_record:
        _run_main(make_lrm, make_output, resume=True)
    assert [c.args[0] for c in mock_record.call_args_list] == ["5.6"]


def test_main_crash_persists_completed_records(
    make_lrm: Path, make_output: Path,
) -> None:
    """A crash mid-walk leaves prior subclauses persisted in --output."""
    with _stub_walk(_TWO_TOC, side_effect=_CRASH_SIDE_EFFECT):
        _run_main(make_lrm, make_output)
    payload = json.loads(make_output.read_text())
    assert payload["records"] == {"4.4": _FRESH_RECORD}


def test_main_partial_checkpoint_omits_order_section(
    make_lrm: Path, make_output: Path,
) -> None:
    """A crash mid-walk leaves no order section since the walk did not finish."""
    with _stub_walk(_TWO_TOC, side_effect=_CRASH_SIDE_EFFECT):
        _run_main(make_lrm, make_output)
    payload = json.loads(make_output.read_text())
    assert "order" not in payload


def test_main_drops_cached_records_not_in_toc(
    make_lrm: Path, make_output: Path,
) -> None:
    """Cached records for subclauses no longer in TOC are dropped from output."""
    _seed_checkpoint(make_output, {"old.1": _CACHED_RECORD})
    with _stub_walk({"4.4": (10, 20)}, return_value=_FRESH_RECORD):
        _run_main(make_lrm, make_output, resume=True)
    payload = json.loads(make_output.read_text())
    assert "old.1" not in payload["records"]


def test_main_no_checkpoint_runs_every_subclause(
    make_lrm: Path, make_output: Path,
) -> None:
    """Without a checkpoint file, build_subclause_record runs for every TOC entry."""
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD) as mock_record:
        _run_main(make_lrm, make_output)
    assert mock_record.call_count == 2


def test_main_without_resume_ignores_existing_output(
    make_lrm: Path, make_output: Path,
) -> None:
    """Without --resume, a pre-existing --output is ignored — every subclause re-walks."""
    _seed_checkpoint(make_output, {"4.4": _CACHED_RECORD})
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD) as mock_record:
        _run_main(make_lrm, make_output)
    assert mock_record.call_count == 2


def test_main_resume_with_no_existing_output_runs_fresh(
    make_lrm: Path, make_output: Path,
) -> None:
    """--resume against a missing --output starts fresh and walks every subclause."""
    with _stub_walk(_TWO_TOC, return_value=_FRESH_RECORD) as mock_record:
        _run_main(make_lrm, make_output, resume=True)
    assert mock_record.call_count == 2
