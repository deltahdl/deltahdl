"""Unit tests for the --labels thread through satisfy_subclause.pipeline.

Covers ``dispatch_cycle``, ``satisfy_unsatisfied_subclause``, and
``satisfy_subclause`` forwarding labels into their downstream calls.
(The corresponding label-shape tests for ``find_or_create_issue`` itself
now live in ``test/lib/python/github/unit/test_find_or_create.py``.)
"""

from unittest.mock import patch

from satisfy_subclause.mutators import CycleMember
from satisfy_subclause.pipeline import (
    dispatch_cycle,
    satisfy_subclause,
    satisfy_unsatisfied_subclause,
)


_LABELS_THREE = ["IEEE 1800-2023", "bug", "needs-triage"]


# --- labels threaded through orchestration ---------------------------------


def test_dispatch_cycle_forwards_labels() -> None:
    """dispatch_cycle forwards --labels into per-member find_or_create_issue."""
    with patch(
        "satisfy_subclause.pipeline.find_or_create_issue",
        side_effect=[(100, "OPEN"), (101, "OPEN")],
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
        "satisfy_subclause.pipeline.find_or_create_issue", return_value=(42, "OPEN"),
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
        "satisfy_subclause.pipeline.find_or_create_issue", return_value=(42, "OPEN"),
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
        "satisfy_subclause.pipeline.find_or_create_issue", return_value=(42, "OPEN"),
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
