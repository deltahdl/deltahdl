"""Unit tests for multi-aggregate batching and the bumped parse-retry budget.

These tests cover the recovery surface that lets a single retry turn
present every rejected aggregate's child menu to the oracle at once
(instead of peeling aggregates off one retry at a time) and the wider
``MAX_PARSE_RETRIES`` budget that accommodates unanticipated
multi-step recoveries.
"""

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


# --- parse_dependencies: multi-aggregate single-pass collection -------------


def test_parse_dependencies_collects_all_aggregates_when_multiple_present() -> None:
    """A payload with two aggregates raises with both of them in ``.identifiers``."""
    captured: list[str] | None = None
    try:
        parse_dependencies('["8", "A"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifiers
    assert captured == ["8", "A"]


def test_parse_dependencies_aggregate_rejection_preserves_payload_order() -> None:
    """``.identifiers`` preserves the order aggregates appeared in the payload."""
    captured: list[str] | None = None
    try:
        parse_dependencies('["A", "8"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifiers
    assert captured == ["A", "8"]


def test_parse_dependencies_aggregate_rejection_skips_non_aggregates() -> None:
    """Non-aggregate valid entries interleaved with aggregates are not in ``.identifiers``."""
    captured: list[str] | None = None
    try:
        parse_dependencies('["8", "8.1", "A"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = exc.identifiers
    assert captured == ["8", "A"]


def test_parse_dependencies_short_circuits_on_bad_shape_before_aggregates() -> None:
    """A bad-shape entry raises plain ValueError even when aggregates also exist."""
    captured: ValueError | None = None
    try:
        parse_dependencies('["not-a-clause", "8"]', toc=AGGREGATE_TOC)
    except ValueError as exc:
        captured = exc
    assert not isinstance(captured, AggregateRejection)


def test_aggregate_rejection_message_names_every_identifier() -> None:
    """The combined rejection message quotes every rejected aggregate identifier."""
    captured: str = ""
    try:
        parse_dependencies('["8", "A"]', toc=AGGREGATE_TOC)
    except AggregateRejection as exc:
        captured = str(exc)
    assert "'8'" in captured and "'A'" in captured


# --- build_parse_retry_prompt: multi-aggregate signature --------------------


def test_build_parse_retry_prompt_lists_each_rejected_aggregate() -> None:
    """The aggregate-branch prompt names every aggregate identifier from the list."""
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13", "24"],
        alternatives_map={"13": ["13.1"], "24": ["24.1"]},
    )
    assert "'13'" in prompt and "'24'" in prompt


def test_build_parse_retry_prompt_lists_first_aggregate_children() -> None:
    """The aggregate-branch prompt enumerates children for the first aggregate."""
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13", "24"],
        alternatives_map={"13": ["13.3", "13.4"], "24": ["24.6", "24.7"]},
    )
    assert "13.3" in prompt and "13.4" in prompt


def test_build_parse_retry_prompt_lists_second_aggregate_children() -> None:
    """The aggregate-branch prompt enumerates children for the second aggregate."""
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["13", "24"],
        alternatives_map={"13": ["13.3", "13.4"], "24": ["24.6", "24.7"]},
    )
    assert "24.6" in prompt and "24.7" in prompt


def test_build_parse_retry_prompt_preserves_aggregate_order() -> None:
    """The aggregate menu lists aggregates in the order supplied."""
    prompt = build_parse_retry_prompt(
        "reason", aggregates=["24", "13"],
        alternatives_map={"13": ["13.1"], "24": ["24.1"]},
    )
    assert prompt.index("'24'") < prompt.index("'13'")


# --- compute_subclause_dependencies: multi-aggregate end-to-end -------------


_MULTI_AGG_TOC: dict[str, tuple[int, int]] = {
    "13": (336, 354),
    "13.1": (336, 336), "13.2": (336, 336), "13.3": (336, 340),
    "24": (775, 780),
    "24.1": (775, 775), "24.2": (775, 775), "24.3": (775, 778),
}


def _patched_multi_agg_toc() -> Any:
    """Patch load_toc so the multi-aggregate retry uses _MULTI_AGG_TOC."""
    return patch(
        "lib.python.lrm_subclause_dependencies.load_toc",
        return_value=_MULTI_AGG_TOC,
    )


def test_compute_subclause_dependencies_retry_prompt_names_all_aggregates() -> None:
    """A multi-aggregate response yields a retry prompt that names every aggregate."""
    with patched_oracle_sequence(
        '["13", "24"]', "[]",
    ) as mock_run, _patched_multi_agg_toc():
        compute_subclause_dependencies("14.12", "lrm.pdf", model="opus")
    retry_prompt = mock_run.call_args_list[1].args[0]
    assert "'13'" in retry_prompt and "'24'" in retry_prompt


def test_compute_subclause_dependencies_retry_prompt_enumerates_each_aggregates_children() -> None:
    """The multi-aggregate retry prompt enumerates children for each rejected aggregate."""
    with patched_oracle_sequence(
        '["13", "24"]', "[]",
    ) as mock_run, _patched_multi_agg_toc():
        compute_subclause_dependencies("14.12", "lrm.pdf", model="opus")
    retry_prompt = mock_run.call_args_list[1].args[0]
    assert "13.3" in retry_prompt and "24.3" in retry_prompt


def test_compute_subclause_dependencies_resolves_multi_aggregate_in_single_retry() -> None:
    """A multi-aggregate first response resolves in one retry, well under the budget."""
    with patched_oracle_sequence(
        '["13", "24"]', '["13.3", "24.3"]',
    ) as mock_run, _patched_multi_agg_toc():
        deps = compute_subclause_dependencies(
            "14.12", "lrm.pdf", model="opus",
        )
    assert deps == ["13.3", "24.3"] and mock_run.call_count == 2


# --- compute_subclause_dependencies: bumped retry budget --------------------


def test_compute_subclause_dependencies_allows_four_retries_before_exit() -> None:
    """With MAX_PARSE_RETRIES=4, four failed retries (5 total) precede the exit."""
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
    """The exit message after the bumped budget is exhausted reports 5 attempts."""
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
    """A clean array on the fifth call (within the 4-retry budget) is returned."""
    with patched_oracle_sequence(
        '["8"]', '["8"]', '["8"]', '["8"]', '["33.6.1"]',
    ), patched_retry_toc():
        deps = compute_subclause_dependencies(
            "33.4", "lrm.pdf", model="opus",
        )
    assert deps == ["33.6.1"]
