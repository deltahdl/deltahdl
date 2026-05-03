"""Unit tests for the --labels thread through satisfy_subclause.pipeline.

Covers:
  - ``find_or_create_issue`` passing every label into ``gh issue create``.
  - ``find_or_create_issue`` joining labels for ``gh issue edit
    --add-label`` on existing matches.
  - ``dispatch_cycle``, ``satisfy_unsatisfied_subclause``, and
    ``satisfy_subclause`` forwarding labels into their downstream calls.
"""

import json
from collections.abc import Callable
from typing import Any, cast
from unittest.mock import MagicMock, patch

from satisfy_subclause.mutators import CycleMember
from satisfy_subclause.pipeline import (
    dispatch_cycle,
    find_or_create_issue,
    satisfy_subclause,
    satisfy_unsatisfied_subclause,
)


_NEW_CANONICAL = "Satisfy IEEE 1800-2023 §33.4.1.5"
_LABELS_THREE = ["IEEE 1800-2023", "bug", "needs-triage"]


def _patched_run_create(
    stub_completed: Callable[..., MagicMock],
) -> Any:
    """Patch subprocess.run with a (no-match list, create-success) sequence."""
    list_done = stub_completed(stdout="[]")
    create_done = stub_completed(stdout="https://github.com/o/r/issues/501")
    return patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[list_done, create_done],
    )


def _patched_run_with_match(
    stub_completed: Callable[..., MagicMock], *, number: int, title: str,
) -> Any:
    """Patch subprocess.run with a one-entry OPEN list match (no extra calls)."""
    body = json.dumps([
        {"number": number, "title": title, "state": "OPEN"},
    ])
    return patch(
        "satisfy_subclause.pipeline.subprocess.run",
        return_value=stub_completed(stdout=body),
    )


def _label_create_values(create_cmd: list[str]) -> list[str]:
    """Return every ``--label`` value in *create_cmd* in input order."""
    return [
        create_cmd[i + 1]
        for i, token in enumerate(create_cmd) if token == "--label"
    ]


def _add_label_value(mock_run: MagicMock) -> str:
    """Return the single ``--add-label`` value captured by *mock_run*."""
    for call in mock_run.call_args_list:
        cmd = call[0][0]
        if cmd[:3] == ["gh", "issue", "edit"] and "--add-label" in cmd:
            return cast(str, cmd[cmd.index("--add-label") + 1])
    raise AssertionError("no --add-label call recorded")


# --- find_or_create_issue: gh issue create label arguments -----------------


def test_create_passes_every_label_in_order(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """gh issue create includes every --labels-supplied label in order."""
    with _patched_run_create(stub_completed) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS_THREE)
    create_cmd = mock_run.call_args_list[1][0][0]
    assert _label_create_values(create_cmd) == _LABELS_THREE


# --- find_or_create_issue: --add-label on existing matches -----------------


def test_add_label_joins_labels_with_commas(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """Multiple labels collapse into a single comma-separated --add-label arg."""
    with _patched_run_with_match(
        stub_completed, number=99, title=_NEW_CANONICAL,
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS_THREE)
    assert _add_label_value(mock_run) == ",".join(_LABELS_THREE)


# --- labels threaded through orchestration ---------------------------------


def test_dispatch_cycle_forwards_labels() -> None:
    """dispatch_cycle forwards --labels into per-member find_or_create_issue."""
    with patch(
        "satisfy_subclause.pipeline.find_or_create_issue",
        side_effect=[100, 101],
    ) as mock_find:
        with patch(
            "satisfy_subclause.pipeline"
            ".satisfy_unsatisfied_subclause_set_with_satisfied_dependencies",
        ):
            dispatch_cycle(
                ["33.4.1.5", "33.6"], "~/LRM.pdf",
                model="opus", labels=_LABELS_THREE,
            )
    seen = [call.kwargs["labels"] for call in mock_find.call_args_list]
    assert seen == [_LABELS_THREE, _LABELS_THREE]


def test_inner_orchestrator_forwards_labels() -> None:
    """Inner orch forwards --labels into recursive satisfy_subclause calls."""
    target = CycleMember(subclause="33.4.1.5", issue=42)
    with patch(
        "satisfy_subclause.pipeline.compute_subclause_dependencies",
        return_value=["33.6.1"],
    ):
        with patch(
            "satisfy_subclause.pipeline.satisfy_subclause",
            side_effect=[{"status": "satisfied"}],
        ) as mock_sub:
            with patch(
                "satisfy_subclause.pipeline"
                ".satisfy_unsatisfied_subclause_with_satisfied_dependencies",
            ):
                satisfy_unsatisfied_subclause(
                    target, "~/LRM.pdf",
                    model="opus", labels=_LABELS_THREE,
                    in_progress=frozenset({"33.4.1.5"}),
                )
    assert mock_sub.call_args.kwargs["labels"] == _LABELS_THREE


def test_satisfy_forwards_labels_to_find_or_create() -> None:
    """satisfy_subclause forwards --labels into find_or_create_issue."""
    with patch(
        "satisfy_subclause.pipeline.find_or_create_issue", return_value=42,
    ) as mock_find:
        with patch(
            "satisfy_subclause.pipeline.satisfy_unsatisfied_subclause",
            return_value={"status": "satisfied"},
        ):
            with patch("satisfy_subclause.pipeline.dispatch_cycle"):
                satisfy_subclause(
                    "33.4.1.5", "~/LRM.pdf",
                    model="opus", labels=_LABELS_THREE,
                )
    assert mock_find.call_args.kwargs["labels"] == _LABELS_THREE


def test_satisfy_forwards_labels_to_inner_orchestrator() -> None:
    """satisfy_subclause forwards --labels into the inner orchestrator."""
    inner_result = {"status": "satisfied"}
    with patch(
        "satisfy_subclause.pipeline.find_or_create_issue", return_value=42,
    ):
        with patch(
            "satisfy_subclause.pipeline.satisfy_unsatisfied_subclause",
            return_value=inner_result,
        ) as mock_inner:
            with patch("satisfy_subclause.pipeline.dispatch_cycle"):
                satisfy_subclause(
                    "33.4.1.5", "~/LRM.pdf",
                    model="opus", labels=_LABELS_THREE,
                )
    assert mock_inner.call_args.kwargs["labels"] == _LABELS_THREE


def test_satisfy_forwards_labels_to_dispatch_cycle() -> None:
    """satisfy_subclause forwards --labels into the cycle dispatch."""
    cycle_result = {"status": "cycle", "members": ["33.4.1.5", "33.6"]}
    with patch(
        "satisfy_subclause.pipeline.find_or_create_issue", return_value=42,
    ):
        with patch(
            "satisfy_subclause.pipeline.satisfy_unsatisfied_subclause",
            return_value=cycle_result,
        ):
            with patch(
                "satisfy_subclause.pipeline.dispatch_cycle",
            ) as mock_dispatch:
                satisfy_subclause(
                    "33.4.1.5", "~/LRM.pdf",
                    model="opus", labels=_LABELS_THREE,
                )
    assert mock_dispatch.call_args.kwargs["labels"] == _LABELS_THREE
