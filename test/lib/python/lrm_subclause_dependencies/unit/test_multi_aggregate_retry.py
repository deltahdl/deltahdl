from typing import Any
from unittest.mock import patch

import pytest

from lib.python.lrm_subclause_dependencies import (
    AggregateRejection,
    build_parse_retry_prompt,
    compute_subclause_dependencies,
    parse_dependencies,
)
from lib.python.test_fixtures.lrm_subclause_dependencies import (
    AGGREGATE_TOC,
    patched_oracle_sequence,
    patched_retry_toc,
)


def test_parse_dependencies_collects_all_aggregates_when_multiple_present() -> None:
    captured: list[str] | None = None
    try:
        parse_dependencies('["8", "A"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifiers
    assert captured == ["8", "A"]


def test_parse_dependencies_aggregate_rejection_preserves_payload_order() -> None:
    captured: list[str] | None = None
    try:
        parse_dependencies('["A", "8"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifiers
    assert captured == ["A", "8"]


def test_parse_dependencies_aggregate_rejection_skips_non_aggregates() -> None:
    captured: list[str] | None = None
    try:
        parse_dependencies('["8", "8.1", "A"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifiers
    assert captured == ["8", "A"]


def test_parse_dependencies_short_circuits_on_bad_shape_before_aggregates() -> None:
    captured: ValueError | None = None
    try:
        parse_dependencies('["not-a-clause", "8"]', toc=AGGREGATE_TOC)
    except ValueError as exc:
        captured = exc
    assert not isinstance(captured, AggregateRejection)


def test_aggregate_rejection_message_names_every_identifier() -> None:
    captured: str = ""
    try:
        parse_dependencies('["8", "A"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = str(exc)
    missing = [i for i in ("'8'", "'A'") if i not in captured]
    assert not missing


def test_build_parse_retry_prompt_lists_each_rejected_aggregate() -> None:
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13", "24"],
        alternatives_map={"13": ["13.1"], "24": ["24.1"]},
    )
    missing = [i for i in ("'13'", "'24'") if i not in prompt]
    assert not missing


def test_build_parse_retry_prompt_lists_first_aggregate_children() -> None:
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13", "24"],
        alternatives_map={"13": ["13.3", "13.4"], "24": ["24.6", "24.7"]},
    )
    missing = [c for c in ("13.3", "13.4") if c not in prompt]
    assert not missing


def test_build_parse_retry_prompt_lists_second_aggregate_children() -> None:
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13", "24"],
        alternatives_map={"13": ["13.3", "13.4"], "24": ["24.6", "24.7"]},
    )
    missing = [c for c in ("24.6", "24.7") if c not in prompt]
    assert not missing


def test_build_parse_retry_prompt_preserves_aggregate_order() -> None:
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["24", "13"],
        alternatives_map={"13": ["13.1"], "24": ["24.1"]},
    )
    assert prompt.index("'24'") < prompt.index("'13'")


_MULTI_AGG_TOC: dict[str, tuple[int, int]] = {
    "13": (336, 354),
    "13.1": (336, 336), "13.2": (336, 336), "13.3": (336, 340),
    "24": (775, 780),
    "24.1": (775, 775), "24.2": (775, 775), "24.3": (775, 778),
}


def _patched_multi_agg_toc() -> Any:
    return patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_MULTI_AGG_TOC,
    )


def test_compute_subclause_dependencies_retry_prompt_names_all_aggregates() -> None:
    with patched_oracle_sequence(
        '["13", "24"]', "[]",
    ) as mock_run, _patched_multi_agg_toc():
        compute_subclause_dependencies("14.12", "lrm.pdf", model="opus")
    retry_prompt = mock_run.call_args_list[1].args[0]
    missing = [i for i in ("'13'", "'24'") if i not in retry_prompt]
    assert not missing


def test_compute_subclause_dependencies_retry_prompt_enumerates_each_aggregates_children() -> None:
    with patched_oracle_sequence(
        '["13", "24"]', "[]",
    ) as mock_run, _patched_multi_agg_toc():
        compute_subclause_dependencies("14.12", "lrm.pdf", model="opus")
    retry_prompt = mock_run.call_args_list[1].args[0]
    missing = [c for c in ("13.3", "24.3") if c not in retry_prompt]
    assert not missing


def test_compute_subclause_dependencies_resolves_multi_aggregate_in_single_retry() -> None:
    with patched_oracle_sequence(
        '["13", "24"]', '["13.3", "24.3"]',
    ) as mock_run, _patched_multi_agg_toc():
        deps = compute_subclause_dependencies(
            "14.12", "lrm.pdf", model="opus",
        )
    assert (deps, mock_run.call_count) == (["13.3", "24.3"], 2)


def test_compute_subclause_dependencies_allows_four_retries_before_exit() -> None:
    mock_run = None
    with patched_oracle_sequence(
        '["8"]', '["8"]', '["8"]', '["8"]', '["8"]',
    ) as mock_run, patched_retry_toc():
        try:
            compute_subclause_dependencies(
                "33.4", "lrm.pdf", model="opus",
            )
        except SystemExit:
            pass
    assert mock_run.call_count == 5


def test_compute_subclause_dependencies_exit_message_quotes_five_attempts(
    capsys: pytest.CaptureFixture[str],
) -> None:
    with patched_oracle_sequence(
        '["8"]', '["8"]', '["8"]', '["8"]', '["8"]',
    ), patched_retry_toc():
        try:
            compute_subclause_dependencies(
                "33.4", "lrm.pdf", model="opus",
            )
        except SystemExit:
            pass
    assert "after 5 attempts" in capsys.readouterr().err


def test_compute_subclause_dependencies_succeeds_within_bumped_budget() -> None:
    with patched_oracle_sequence(
        '["8"]', '["8"]', '["8"]', '["8"]', '["33.6.1"]',
    ), patched_retry_toc():
        deps = compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus",
        )
    assert deps == ["33.6.1"]


def test_aggregate_rejection_calls_a_bare_number_a_clause() -> None:
    captured = ""
    try:
        parse_dependencies('["8"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = str(exc)
    assert "clause '8'" in captured


def test_aggregate_rejection_calls_a_bare_letter_an_annex() -> None:
    captured = ""
    try:
        parse_dependencies('["A"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = str(exc)
    assert "annex 'A'" in captured


def test_aggregate_rejection_names_every_entry_it_turns_down() -> None:
    captured = ""
    try:
        parse_dependencies('["8", "A"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = str(exc)
    assert "clause '8', annex 'A'" in captured
