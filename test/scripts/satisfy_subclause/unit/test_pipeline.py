"""Unit tests for satisfy_subclause.pipeline."""

import json
from unittest.mock import patch

import pytest

from satisfy_subclause.mutators import CycleMember
from satisfy_subclause.oracles import (
    SATISFACTION_CONDITIONS,
    SATISFIED,
    ConditionStatus,
    SubclauseDiagnostic,
)
from satisfy_subclause.pipeline import (
    dispatch_cycle,
    find_or_create_issue,
    issue_title_for,
    label_issue_pipeline_stuck,
    legacy_issue_title_for,
    parse_issue_number_from_create_output,
    satisfy_subclause,
    satisfy_unsatisfied_subclause,
)


_LEGACY_TITLE = (
    "Ensure IEEE 1800-2023 §33.4.1.5 functionalities and tests are"
    " implemented and properly named"
)


def _legacy_payload(state: str, *, number: int = 88) -> str:
    """Return a gh-issue-list JSON payload with one legacy-titled entry."""
    return json.dumps([
        {"number": number, "title": _LEGACY_TITLE, "state": state},
    ])


# --- helpers ----------------------------------------------------------------


def _diag(failing: bool = False) -> SubclauseDiagnostic:
    """Return a satisfied or one-failure diagnostic."""
    fields: dict[str, ConditionStatus] = {
        c: SATISFIED for c in SATISFACTION_CONDITIONS
    }
    if failing:
        fields["rule_coverage"] = ["rule 7 has no production code"]
    return SubclauseDiagnostic(**fields)


def _target(subclause: str, *, issue: int = 42,
            failing: bool = True) -> CycleMember:
    """Build a CycleMember target for inner-orchestrator tests."""
    return CycleMember(
        subclause=subclause, diagnostic=_diag(failing=failing), issue=issue,
    )


# --- issue helpers ----------------------------------------------------------


def test_issue_title_for() -> None:
    """issue_title_for produces the canonical 'Satisfy §X' title."""
    assert issue_title_for("33.4.1.5") == "Satisfy §33.4.1.5"


def test_parse_issue_number_from_create_output() -> None:
    """The number is extracted from a gh issue create URL."""
    output = "Creating issue\nhttps://github.com/o/r/issues/123\n"
    assert parse_issue_number_from_create_output(output) == 123


# --- find_or_create_issue ---------------------------------------------------


def _patched_gh(stub_completed, list_payload="[]", list_rc=0,
                create_url="", create_rc=0):
    """Patch subprocess.run with a sequence of gh responses."""
    list_completed = stub_completed(stdout=list_payload, returncode=list_rc)
    create_completed = stub_completed(stdout=create_url, returncode=create_rc)
    return patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[list_completed, create_completed],
    )


def test_find_or_create_issue_creates_new(stub_completed) -> None:
    """find_or_create_issue creates a new issue when none exists."""
    url = "https://github.com/o/r/issues/777"
    with _patched_gh(stub_completed, create_url=url):
        assert find_or_create_issue("33.4.1.5") == 777


def test_find_or_create_issue_reuses_open(stub_completed) -> None:
    """find_or_create_issue returns an existing open issue's number."""
    body = json.dumps([
        {"number": 99, "title": "Satisfy §33.4.1.5", "state": "OPEN"},
    ])
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        return_value=stub_completed(stdout=body),
    ):
        assert find_or_create_issue("33.4.1.5") == 99


def test_find_or_create_issue_reopens_closed(stub_completed) -> None:
    """find_or_create_issue reopens a closed match before returning it."""
    body = json.dumps([
        {"number": 55, "title": "Satisfy §33.4.1.5", "state": "CLOSED"},
    ])
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body), stub_completed()],
    ) as mock_run:
        find_or_create_issue("33.4.1.5")
    cmd = mock_run.call_args_list[1][0][0]
    assert cmd[:3] == ["gh", "issue", "reopen"]


def test_find_or_create_issue_exits_on_list_failure(stub_completed) -> None:
    """A non-zero gh issue list exit is loud-fatal."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        return_value=stub_completed(returncode=1),
    ):
        with pytest.raises(SystemExit):
            find_or_create_issue("33.4.1.5")


def test_find_or_create_issue_exits_on_create_failure(stub_completed) -> None:
    """A non-zero gh issue create exit is loud-fatal."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout="[]"), stub_completed(returncode=1)],
    ):
        with pytest.raises(SystemExit):
            find_or_create_issue("33.4.1.5")


def test_find_or_create_issue_creates_when_no_title_matches(
    stub_completed,
) -> None:
    """A list with mismatched-title entries falls through to create."""
    body = json.dumps([
        {"number": 1, "title": "Different title", "state": "OPEN"},
    ])
    create_url = "https://github.com/o/r/issues/333"
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=body), stub_completed(stdout=create_url),
        ],
    ):
        assert find_or_create_issue("33.4.1.5") == 333


# --- legacy-title migration -------------------------------------------------


def test_legacy_issue_title_for() -> None:
    """legacy_issue_title_for produces the historical 'Ensure …' title."""
    assert legacy_issue_title_for("33.4.1.5") == _LEGACY_TITLE


def test_find_or_create_issue_returns_legacy_open_number(stub_completed) -> None:
    """find_or_create_issue returns the legacy-titled open issue's number."""
    body = _legacy_payload("OPEN")
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body), stub_completed()],
    ):
        assert find_or_create_issue("33.4.1.5") == 88


def test_find_or_create_issue_renames_legacy_open(stub_completed) -> None:
    """find_or_create_issue renames a legacy-titled open issue in place."""
    body = _legacy_payload("OPEN")
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body), stub_completed()],
    ) as mock_run:
        find_or_create_issue("33.4.1.5")
    edit_cmd = mock_run.call_args_list[1][0][0]
    assert edit_cmd == [
        "gh", "issue", "edit", "88", "--title", "Satisfy §33.4.1.5",
    ]


def test_find_or_create_issue_renames_legacy_closed(stub_completed) -> None:
    """A legacy-titled closed issue is renamed before being reopened."""
    body = _legacy_payload("CLOSED")
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=body),
            stub_completed(),
            stub_completed(),
        ],
    ) as mock_run:
        find_or_create_issue("33.4.1.5")
    edit_cmd = mock_run.call_args_list[1][0][0]
    assert edit_cmd[:3] == ["gh", "issue", "edit"]


def test_find_or_create_issue_reopens_legacy_closed(stub_completed) -> None:
    """A legacy-titled closed issue is reopened after the rename."""
    body = _legacy_payload("CLOSED")
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=body),
            stub_completed(),
            stub_completed(),
        ],
    ) as mock_run:
        find_or_create_issue("33.4.1.5")
    reopen_cmd = mock_run.call_args_list[2][0][0]
    assert reopen_cmd[:3] == ["gh", "issue", "reopen"]


# --- label_issue_pipeline_stuck --------------------------------------------


def test_label_issue_adds_label(stub_completed) -> None:
    """label_issue_pipeline_stuck adds the pipeline-stuck label."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        return_value=stub_completed(),
    ) as mock_run:
        label_issue_pipeline_stuck(42, _diag(failing=True))
    label_cmd = mock_run.call_args_list[0][0][0]
    assert "pipeline-stuck" in label_cmd


def test_label_issue_posts_comment(stub_completed) -> None:
    """label_issue_pipeline_stuck posts a diagnostic comment."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        return_value=stub_completed(),
    ) as mock_run:
        label_issue_pipeline_stuck(42, _diag(failing=True))
    comment_cmd = mock_run.call_args_list[1][0][0]
    assert "comment" in comment_cmd


# --- dispatch_cycle ---------------------------------------------------------


def _patched_for_cycle(diagnostic_factory=None, issues=(100, 101)):
    """Patch is_subclause_satisfied, find_or_create_issue, and the cycle mutator."""
    diag_factory = diagnostic_factory or (lambda: _diag(failing=True))
    return (
        patch(
            "satisfy_subclause.pipeline.is_subclause_satisfied",
            side_effect=lambda *_a, **_k: diag_factory(),
        ),
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
    mock_oracle, mock_issue, mock_mut = _patched_for_cycle()
    with mock_oracle:
        with mock_issue:
            with mock_mut as mut:
                dispatch_cycle(["33.4.1.5", "33.6"], "~/LRM.pdf", model="opus")
    members_arg = mut.call_args[0][0]
    assert len(members_arg) == 2


def test_dispatch_cycle_passes_issues() -> None:
    """dispatch_cycle gathers the per-member issue numbers."""
    mock_oracle, mock_issue, mock_mut = _patched_for_cycle(issues=(200, 201))
    with mock_oracle:
        with mock_issue:
            with mock_mut as mut:
                dispatch_cycle(["33.4.1.5", "33.6"], "~/LRM.pdf", model="opus")
    issues_seen = [m.issue for m in mut.call_args[0][0]]
    assert issues_seen == [200, 201]


def test_dispatch_cycle_passes_subclauses() -> None:
    """dispatch_cycle preserves the cycle-member identifiers."""
    mock_oracle, mock_issue, mock_mut = _patched_for_cycle()
    with mock_oracle:
        with mock_issue:
            with mock_mut as mut:
                dispatch_cycle(["33.4.1.5", "33.6"], "~/LRM.pdf", model="opus")
    subs_seen = [m.subclause for m in mut.call_args[0][0]]
    assert subs_seen == ["33.4.1.5", "33.6"]


def test_dispatch_cycle_passes_diagnostics() -> None:
    """dispatch_cycle attaches a diagnostic per member."""
    mock_oracle, mock_issue, mock_mut = _patched_for_cycle()
    with mock_oracle:
        with mock_issue:
            with mock_mut as mut:
                dispatch_cycle(["33.4.1.5", "33.6"], "~/LRM.pdf", model="opus")
    diagnostics_seen = [m.diagnostic for m in mut.call_args[0][0]]
    assert all(isinstance(d, SubclauseDiagnostic) for d in diagnostics_seen)


# --- satisfy_unsatisfied_subclause -----------------------------------------


def _patched_inner(deps, *, dep_results=None):
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


def _patched_dispatch():
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


def test_inner_no_deps_invokes_no_deps_mutator() -> None:
    """Inner orch with no deps dispatches to the no-deps mutator."""
    mock_deps, mock_satisfy = _patched_inner([])
    no_p, with_p = _patched_dispatch()
    with mock_deps:
        with mock_satisfy:
            with no_p as mock_no:
                with with_p as mock_with:
                    satisfy_unsatisfied_subclause(
                        _target("33.4.1.5"), "~/LRM.pdf",
                        model="opus", in_progress=frozenset({"33.4.1.5"}),
                    )
    assert mock_no.called and not mock_with.called


def test_inner_with_deps_invokes_with_deps_mutator() -> None:
    """Inner orch with deps dispatches to the with-deps mutator."""
    mock_deps, mock_satisfy = _patched_inner(["33.6.1"])
    no_p, with_p = _patched_dispatch()
    with mock_deps:
        with mock_satisfy:
            with no_p as mock_no:
                with with_p as mock_with:
                    satisfy_unsatisfied_subclause(
                        _target("33.4.1.5"), "~/LRM.pdf",
                        model="opus", in_progress=frozenset({"33.4.1.5"}),
                    )
    assert mock_with.called and not mock_no.called


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
                    model="opus", in_progress=frozenset({"33.4.1.5"}),
                )
    assert result == {"status": "satisfied"}


def test_inner_detects_cycle_in_own_deps() -> None:
    """Inner orch returns a cycle marker when a dep is in in_progress."""
    mock_deps, mock_satisfy = _patched_inner(["33.4"])
    with mock_deps:
        with mock_satisfy:
            result = satisfy_unsatisfied_subclause(
                _target("33.4.1.5"), "~/LRM.pdf",
                model="opus", in_progress=frozenset({"33.4.1.5", "33.4"}),
            )
    assert result["status"] == "cycle" and "33.4" in result["members"]


def test_inner_includes_self_in_cycle_members() -> None:
    """The cycle marker includes the inner orchestrator's own subclause."""
    mock_deps, mock_satisfy = _patched_inner(["33.4"])
    with mock_deps:
        with mock_satisfy:
            result = satisfy_unsatisfied_subclause(
                _target("33.4.1.5"), "~/LRM.pdf",
                model="opus", in_progress=frozenset({"33.4.1.5", "33.4"}),
            )
    assert "33.4.1.5" in result["members"]


def test_inner_propagates_cycle_from_dep() -> None:
    """Inner orch propagates a cycle marker emitted by a recursive dep call."""
    mock_deps, mock_satisfy = _patched_inner(
        ["33.6.1"],
        dep_results=[{"status": "cycle", "members": ["33.4", "33.6.1"]}],
    )
    with mock_deps:
        with mock_satisfy:
            result = satisfy_unsatisfied_subclause(
                _target("33.4.1.5"), "~/LRM.pdf",
                model="opus", in_progress=frozenset({"33.4.1.5"}),
            )
    assert result["status"] == "cycle"


def test_inner_logs_subclause_to_stderr(capsys) -> None:
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
                    model="opus", in_progress=frozenset({"33.4.1.5"}),
                )
    assert "§33.4.1.5" in capsys.readouterr().err


# --- satisfy_subclause -----------------------------------------------------


def _patched_pipeline(diagnostics, *, inner_results=None):
    """Patch the pipeline integration points."""
    return (
        patch(
            "satisfy_subclause.pipeline.is_subclause_satisfied",
            side_effect=diagnostics,
        ),
        patch(
            "satisfy_subclause.pipeline.find_or_create_issue",
            return_value=42,
        ),
        patch(
            "satisfy_subclause.pipeline.satisfy_unsatisfied_subclause",
            side_effect=inner_results or [],
        ),
        patch("satisfy_subclause.pipeline.label_issue_pipeline_stuck"),
        patch("satisfy_subclause.pipeline.dispatch_cycle"),
    )


def _patched_stuck_pipeline():
    """Build a pipeline patch set that exhausts the retry budget."""
    failing = _diag(failing=True)
    return _patched_pipeline(
        [failing, failing, failing],
        inner_results=[{"status": "satisfied"}, {"status": "satisfied"}],
    )


def test_satisfy_skips_when_already_satisfied() -> None:
    """satisfy_subclause does not run the pipeline when the oracle says yes."""
    oracle, issue, inner, label, cycle = _patched_pipeline([_diag()])
    with oracle:
        with issue:
            with inner as mock_inner:
                with label:
                    with cycle:
                        satisfy_subclause(
                            "33.4.1.5", "~/LRM.pdf", model="opus",
                        )
    assert not mock_inner.called


def test_satisfy_returns_satisfied_when_already_satisfied() -> None:
    """satisfy_subclause returns the satisfied marker on early-yes."""
    oracle, issue, inner, label, cycle = _patched_pipeline([_diag()])
    with oracle:
        with issue:
            with inner:
                with label:
                    with cycle:
                        result = satisfy_subclause(
                            "33.4.1.5", "~/LRM.pdf", model="opus",
                        )
    assert result == {"status": "satisfied"}


def test_satisfy_runs_pipeline_when_unsatisfied() -> None:
    """satisfy_subclause runs the inner pipeline when the oracle returns no."""
    oracle, issue, inner, label, cycle = _patched_pipeline(
        [_diag(failing=True), _diag()],
        inner_results=[{"status": "satisfied"}],
    )
    with oracle:
        with issue:
            with inner as mock_inner:
                with label:
                    with cycle:
                        satisfy_subclause(
                            "33.4.1.5", "~/LRM.pdf", model="opus",
                        )
    assert mock_inner.called


def test_satisfy_returns_satisfied_after_convergence() -> None:
    """satisfy_subclause returns satisfied after the inner pipeline converges."""
    oracle, issue, inner, label, cycle = _patched_pipeline(
        [_diag(failing=True), _diag()],
        inner_results=[{"status": "satisfied"}],
    )
    with oracle:
        with issue:
            with inner:
                with label:
                    with cycle:
                        result = satisfy_subclause(
                            "33.4.1.5", "~/LRM.pdf", model="opus",
                        )
    assert result == {"status": "satisfied"}


def test_satisfy_propagates_cycle_when_nested() -> None:
    """satisfy_subclause propagates a cycle when nested under another frame."""
    cycle_payload = {"status": "cycle", "members": ["33.4", "33.4.1.5"]}
    oracle, issue, inner, label, cycle = _patched_pipeline(
        [_diag(failing=True)],
        inner_results=[cycle_payload],
    )
    with oracle:
        with issue:
            with inner:
                with label:
                    with cycle as mock_dispatch:
                        result = satisfy_subclause(
                            "33.4.1.5", "~/LRM.pdf", model="opus",
                            in_progress=frozenset({"33.4"}),
                        )
    assert result["status"] == "cycle" and not mock_dispatch.called


def test_satisfy_dispatches_cycle_at_outermost_frame() -> None:
    """satisfy_subclause dispatches when the cycle frame is outermost."""
    cycle_payload = {"status": "cycle", "members": ["33.4.1.5", "33.6"]}
    oracle, issue, inner, label, cycle = _patched_pipeline(
        [_diag(failing=True), _diag()],
        inner_results=[cycle_payload],
    )
    with oracle:
        with issue:
            with inner:
                with label:
                    with cycle as mock_dispatch:
                        satisfy_subclause(
                            "33.4.1.5", "~/LRM.pdf", model="opus",
                        )
    assert mock_dispatch.called


def test_satisfy_retries_once_then_labels_stuck() -> None:
    """satisfy_subclause retries once then labels the issue pipeline-stuck."""
    oracle, issue, inner, label, cycle = _patched_stuck_pipeline()
    with oracle:
        with issue:
            with inner:
                with label as mock_label:
                    with cycle:
                        try:
                            satisfy_subclause(
                                "33.4.1.5", "~/LRM.pdf", model="opus",
                            )
                        except SystemExit:
                            pass
    assert mock_label.called


def test_satisfy_exits_nonzero_when_stuck() -> None:
    """satisfy_subclause exits non-zero when the pipeline gets stuck."""
    oracle, issue, inner, label, cycle = _patched_stuck_pipeline()
    captured_code = None
    with oracle:
        with issue:
            with inner:
                with label:
                    with cycle:
                        try:
                            satisfy_subclause(
                                "33.4.1.5", "~/LRM.pdf", model="opus",
                            )
                        except SystemExit as exc:
                            captured_code = exc.code
    assert captured_code != 0


def test_satisfy_logs_subclause_to_stderr(capsys) -> None:
    """satisfy_subclause prints a one-line outer-orchestrator banner."""
    oracle, issue, inner, label, cycle = _patched_pipeline([_diag()])
    with oracle:
        with issue:
            with inner:
                with label:
                    with cycle:
                        satisfy_subclause(
                            "33.4.1.5", "~/LRM.pdf", model="opus",
                        )
    assert "§33.4.1.5" in capsys.readouterr().err


def test_satisfy_logs_retry_to_stderr(capsys) -> None:
    """satisfy_subclause logs the retry message between passes."""
    oracle, issue, inner, label, cycle = _patched_stuck_pipeline()
    with oracle:
        with issue:
            with inner:
                with label:
                    with cycle:
                        try:
                            satisfy_subclause(
                                "33.4.1.5", "~/LRM.pdf", model="opus",
                            )
                        except SystemExit:
                            pass
    assert "retrying" in capsys.readouterr().err


# --- CycleMember dataclass --------------------------------------------------


def test_cycle_member_holds_subclause() -> None:
    """CycleMember stores the subclause identifier."""
    member = CycleMember(
        subclause="33.4.1.5", diagnostic=_diag(), issue=42,
    )
    assert member.subclause == "33.4.1.5"
