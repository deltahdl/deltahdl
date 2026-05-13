"""Unit tests for satisfy_subclause.pipeline orchestration."""

from typing import Any
from unittest.mock import MagicMock, patch

import pytest

from satisfy_subclause.mutators import CycleMember
from satisfy_subclause.pipeline import (
    dispatch_cycle,
    satisfy_subclause,
    satisfy_unsatisfied_subclause,
)


_LABELS = ["IEEE 1800-2023"]


def _target(subclause: str = "33.4.1.5", issue: int = 42) -> CycleMember:
    """Build a CycleMember target for inner-orchestrator tests."""
    return CycleMember(subclause=subclause, issue=issue)


# --- dispatch_cycle ---------------------------------------------------------


def _patched_for_cycle(
    issues: tuple[int, ...] = (100, 101),
) -> tuple[Any, Any]:
    """Patch find_or_create_issue and the cycle mutator."""
    return (
        patch(
            "satisfy_subclause.pipeline.find_or_create_issue",
            side_effect=list(issues),
        ),
        patch(
            "satisfy_subclause.pipeline"
            ".satisfy_unsatisfied_subclause_set_with_satisfied_dependencies",
        ),
    )


def test_dispatch_cycle_invokes_set_mutator() -> None:
    """dispatch_cycle invokes the cycle-set mutator with one CycleMember per."""
    mock_issue, mock_mut = _patched_for_cycle()
    with mock_issue:
        with mock_mut as mut:
            dispatch_cycle(
                ["33.4.1.5", "33.6"], "~/LRM.pdf",
                model="opus", labels=_LABELS,
            )
    members_arg = mut.call_args[0][0]
    assert len(members_arg) == 2


def test_dispatch_cycle_passes_issues() -> None:
    """dispatch_cycle gathers the per-member issue numbers."""
    mock_issue, mock_mut = _patched_for_cycle(issues=(200, 201))
    with mock_issue:
        with mock_mut as mut:
            dispatch_cycle(
                ["33.4.1.5", "33.6"], "~/LRM.pdf",
                model="opus", labels=_LABELS,
            )
    issues_seen = [m.issue for m in mut.call_args[0][0]]
    assert issues_seen == [200, 201]


def test_dispatch_cycle_passes_subclauses() -> None:
    """dispatch_cycle preserves the cycle-member identifiers."""
    mock_issue, mock_mut = _patched_for_cycle()
    with mock_issue:
        with mock_mut as mut:
            dispatch_cycle(
                ["33.4.1.5", "33.6"], "~/LRM.pdf",
                model="opus", labels=_LABELS,
            )
    subs_seen = [m.subclause for m in mut.call_args[0][0]]
    assert subs_seen == ["33.4.1.5", "33.6"]


# --- satisfy_unsatisfied_subclause -----------------------------------------


def _patched_inner(
    deps: list[str], *, dep_results: list[dict[str, Any]] | None = None,
) -> tuple[Any, Any]:
    """Patch compute_subclause_dependencies and satisfy_subclause."""
    return (
        patch(
            "satisfy_subclause.pipeline.compute_subclause_dependencies",
            return_value=deps,
        ),
        patch(
            "satisfy_subclause.pipeline.satisfy_subclause",
            side_effect=dep_results or [{"status": "satisfied"}] * len(deps),
        ),
    )


def _patched_dispatch() -> tuple[Any, Any]:
    """Patch the no-deps and with-deps mutator entry points."""
    return (
        patch(
            "satisfy_subclause.pipeline"
            ".satisfy_unsatisfied_subclause_without_dependencies",
        ),
        patch(
            "satisfy_subclause.pipeline"
            ".satisfy_unsatisfied_subclause_with_satisfied_dependencies",
        ),
    )


def _run_inner_for_deps(deps: list[str]) -> tuple[bool, bool]:
    """Run the inner orchestrator and report (no_deps_called, with_deps_called)."""
    mock_deps, mock_satisfy = _patched_inner(deps)
    no_p, with_p = _patched_dispatch()
    with mock_deps, mock_satisfy, no_p as mock_no, with_p as mock_with:
        satisfy_unsatisfied_subclause(
            _target("33.4.1.5"), "~/LRM.pdf",
            model="opus", labels=_LABELS,
            in_progress=frozenset({"33.4.1.5"}),
        )
    return mock_no.called, mock_with.called


def test_inner_no_deps_invokes_no_deps_mutator() -> None:
    """Inner orch with no deps dispatches to the no-deps mutator."""
    no_called, with_called = _run_inner_for_deps([])
    assert no_called and not with_called


def test_inner_with_deps_invokes_with_deps_mutator() -> None:
    """Inner orch with deps dispatches to the with-deps mutator."""
    no_called, with_called = _run_inner_for_deps(["33.6.1"])
    assert with_called and not no_called


def test_inner_returns_satisfied_after_dispatch() -> None:
    """Inner orch returns the satisfied marker after the mutator returns."""
    mock_deps, mock_satisfy = _patched_inner([])
    with mock_deps:
        with mock_satisfy:
            with patch(
                "satisfy_subclause.pipeline"
                ".satisfy_unsatisfied_subclause_without_dependencies",
            ):
                result = satisfy_unsatisfied_subclause(
                    _target("33.4.1.5"), "~/LRM.pdf",
                    model="opus", labels=_LABELS,
                    in_progress=frozenset({"33.4.1.5"}),
                )
    assert result == {"status": "satisfied"}


def test_inner_detects_cycle_in_own_deps() -> None:
    """Inner orch returns a cycle marker when a dep is in in_progress."""
    mock_deps, mock_satisfy = _patched_inner(["33.4"])
    with mock_deps:
        with mock_satisfy:
            result = satisfy_unsatisfied_subclause(
                _target("33.4.1.5"), "~/LRM.pdf",
                model="opus", labels=_LABELS,
                in_progress=frozenset({"33.4.1.5", "33.4"}),
            )
    assert result["status"] == "cycle" and "33.4" in result["members"]


def test_inner_includes_self_in_cycle_members() -> None:
    """The cycle marker includes the inner orchestrator's own subclause."""
    mock_deps, mock_satisfy = _patched_inner(["33.4"])
    with mock_deps:
        with mock_satisfy:
            result = satisfy_unsatisfied_subclause(
                _target("33.4.1.5"), "~/LRM.pdf",
                model="opus", labels=_LABELS,
                in_progress=frozenset({"33.4.1.5", "33.4"}),
            )
    assert "33.4.1.5" in result["members"]


def _run_inner_cycle_propagation(
    *, in_progress: frozenset[str],
) -> dict[str, Any]:
    """Run the inner orch where its single dep returns a fixed cycle marker."""
    mock_deps, mock_satisfy = _patched_inner(
        ["33.6.1"],
        dep_results=[{"status": "cycle", "members": ["33.4", "33.6.1"]}],
    )
    with mock_deps:
        with mock_satisfy:
            return satisfy_unsatisfied_subclause(
                _target("33.4.1.5"), "~/LRM.pdf",
                model="opus", labels=_LABELS,
                in_progress=in_progress,
            )


def test_inner_propagates_cycle_from_dep() -> None:
    """Inner orch propagates a cycle marker emitted by a recursive dep call."""
    result = _run_inner_cycle_propagation(in_progress=frozenset({"33.4.1.5"}))
    assert result["status"] == "cycle"


def test_inner_does_not_add_self_above_cycle_entry() -> None:
    """A frame above the cycle entry must not pollute the members set."""
    result = _run_inner_cycle_propagation(in_progress=frozenset({"33.4.1.5"}))
    assert "33.4.1.5" not in result["members"]


def test_inner_adds_self_when_below_cycle_entry() -> None:
    """A frame between the cycle entry and the detection point includes itself."""
    result = _run_inner_cycle_propagation(
        in_progress=frozenset({"33.4", "33.4.1.5"}),
    )
    assert "33.4.1.5" in result["members"]


def test_inner_logs_subclause_to_stderr(capsys: pytest.CaptureFixture[str]) -> None:
    """Inner orch prints a one-line banner to stderr."""
    mock_deps, mock_satisfy = _patched_inner([])
    with mock_deps:
        with mock_satisfy:
            with patch(
                "satisfy_subclause.pipeline"
                ".satisfy_unsatisfied_subclause_without_dependencies",
            ):
                satisfy_unsatisfied_subclause(
                    _target("33.4.1.5"), "~/LRM.pdf",
                    model="opus", labels=_LABELS,
                    in_progress=frozenset({"33.4.1.5"}),
                )
    assert "§33.4.1.5" in capsys.readouterr().err


def _run_inner_capturing_dep_oracle(mutator_model: str) -> Any:
    """Run the inner orchestrator and return the dep-oracle mock."""
    mock_deps, mock_satisfy = _patched_inner([])
    with mock_deps as mock_dep:
        with mock_satisfy:
            with patch(
                "satisfy_subclause.pipeline"
                ".satisfy_unsatisfied_subclause_without_dependencies",
            ):
                satisfy_unsatisfied_subclause(
                    _target("33.4.1.5"), "~/LRM.pdf",
                    model=mutator_model, labels=_LABELS,
                    in_progress=frozenset({"33.4.1.5"}),
                )
    return mock_dep


def test_inner_calls_dep_oracle_with_sonnet_when_mutator_opus() -> None:
    """Dep oracle runs on sonnet even when the mutator runs on opus."""
    mock_dep = _run_inner_capturing_dep_oracle("opus")
    assert mock_dep.call_args.kwargs["model"] == "sonnet"


def test_inner_calls_dep_oracle_with_sonnet_when_mutator_haiku() -> None:
    """Dep-oracle model is independent of the mutator model — sonnet either way."""
    mock_dep = _run_inner_capturing_dep_oracle("haiku")
    assert mock_dep.call_args.kwargs["model"] == "sonnet"


def test_inner_calls_dep_oracle_with_medium_effort() -> None:
    """Dep oracle runs at medium thinking effort — focused read-and-list judgment."""
    mock_dep = _run_inner_capturing_dep_oracle("opus")
    assert mock_dep.call_args.kwargs["effort"] == "medium"


# --- satisfy_subclause -----------------------------------------------------


def _patched_pipeline(
    *, inner_results: list[dict[str, Any]] | None = None,
) -> tuple[Any, Any, Any]:
    """Patch the pipeline integration points (no oracle, no retry loop)."""
    return (
        patch(
            "satisfy_subclause.pipeline.find_or_create_issue",
            return_value=42,
        ),
        patch(
            "satisfy_subclause.pipeline.satisfy_unsatisfied_subclause",
            side_effect=inner_results or [{"status": "satisfied"}],
        ),
        patch("satisfy_subclause.pipeline.dispatch_cycle"),
    )


def test_satisfy_runs_inner_pipeline_unconditionally() -> None:
    """satisfy_subclause always runs the inner pipeline (no entry-time skip)."""
    issue, inner, cycle = _patched_pipeline()
    with issue:
        with inner as mock_inner:
            with cycle:
                satisfy_subclause(
                    "33.4.1.5", "~/LRM.pdf",
                    model="opus", labels=_LABELS,
                )
    assert mock_inner.called


def test_satisfy_returns_satisfied_after_inner_pipeline() -> None:
    """satisfy_subclause returns satisfied after the inner pipeline returns."""
    issue, inner, cycle = _patched_pipeline()
    with issue:
        with inner:
            with cycle:
                result = satisfy_subclause(
                    "33.4.1.5", "~/LRM.pdf",
                    model="opus", labels=_LABELS,
                )
    assert result == {"status": "satisfied"}


def test_satisfy_runs_pipeline_only_once() -> None:
    """One pass: there is no retry loop and no post-mutator re-check."""
    issue, inner, cycle = _patched_pipeline()
    with issue:
        with inner as mock_inner:
            with cycle:
                satisfy_subclause(
                    "33.4.1.5", "~/LRM.pdf",
                    model="opus", labels=_LABELS,
                )
    assert mock_inner.call_count == 1


def _run_satisfy_with_cycle(
    subclause: str, members: list[str],
    *, in_progress: frozenset[str] = frozenset(),
) -> tuple[dict[str, Any], MagicMock]:
    """Run satisfy_subclause whose inner returns the given cycle marker."""
    cycle_payload = {"status": "cycle", "members": members}
    issue, inner, cycle = _patched_pipeline(inner_results=[cycle_payload])
    with issue:
        with inner:
            with cycle as mock_dispatch:
                result = satisfy_subclause(
                    subclause, "~/LRM.pdf",
                    model="opus", labels=_LABELS,
                    in_progress=in_progress,
                )
    return result, mock_dispatch


def test_satisfy_propagates_cycle_when_nested() -> None:
    """satisfy_subclause propagates a cycle when nested under another frame."""
    result, mock_dispatch = _run_satisfy_with_cycle(
        "33.4.1.5", ["33.4", "33.4.1.5"], in_progress=frozenset({"33.4"}),
    )
    assert result["status"] == "cycle" and not mock_dispatch.called


def test_satisfy_dispatches_cycle_at_outermost_frame() -> None:
    """satisfy_subclause dispatches when the cycle frame is outermost."""
    _, mock_dispatch = _run_satisfy_with_cycle(
        "33.4.1.5", ["33.4.1.5", "33.6"],
    )
    assert mock_dispatch.called


def test_satisfy_dispatches_at_cycle_entry_under_ancestors() -> None:
    """The cycle-entry frame dispatches even when ancestors sit above it."""
    _, mock_dispatch = _run_satisfy_with_cycle(
        "33.4", ["33.4", "33.6"], in_progress=frozenset({"7.2"}),
    )
    assert mock_dispatch.called


def test_satisfy_propagates_cycle_when_self_not_in_members() -> None:
    """A frame whose subclause is not on the cycle propagates without dispatching."""
    result, mock_dispatch = _run_satisfy_with_cycle(
        "7.2", ["33.4", "33.6"], in_progress=frozenset({"R"}),
    )
    assert result["status"] == "cycle" and not mock_dispatch.called


def test_satisfy_logs_subclause_to_stderr(capsys: pytest.CaptureFixture[str]) -> None:
    """satisfy_subclause prints a one-line outer-orchestrator banner."""
    issue, inner, cycle = _patched_pipeline()
    with issue:
        with inner:
            with cycle:
                satisfy_subclause(
                    "33.4.1.5", "~/LRM.pdf",
                    model="opus", labels=_LABELS,
                )
    assert "§33.4.1.5" in capsys.readouterr().err


# --- CycleMember dataclass --------------------------------------------------


def test_cycle_member_holds_subclause() -> None:
    """CycleMember stores the subclause identifier."""
    member = CycleMember(subclause="33.4.1.5", issue=42)
    assert member.subclause == "33.4.1.5"
