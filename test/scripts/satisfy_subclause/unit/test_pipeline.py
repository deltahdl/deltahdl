"""Unit tests for satisfy_subclause.pipeline."""

import json
from collections.abc import Callable
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

from satisfy_subclause import oracles
from satisfy_subclause.mutators import CycleMember
from satisfy_subclause.pipeline import (
    dispatch_cycle,
    find_or_create_issue,
    issue_title_for,
    legacy_issue_title_for,
    parse_issue_number_from_create_output,
    satisfy_subclause,
    satisfy_unsatisfied_subclause,
)


_NEW_CANONICAL = "Satisfy IEEE 1800-2023 §33.4.1.5"
_LEGACY_SHORT = "Satisfy §33.4.1.5"
_LEGACY_AUDIT_NUMERIC = (
    "Ensure IEEE 1800-2023 §33.4.1.5 functionalities and tests are"
    " implemented and properly named"
)
_LEGACY_AUDIT_ANNEX = (
    "Ensure IEEE 1800-2023 A.9.3 functionalities and tests are"
    " implemented and properly named"
)
_MASTER_LIST = "Implement IEEE 1800-2023 §33 Configuring the contents of a design"
_LABELS = ["IEEE 1800-2023"]


def _payload(*entries: tuple[int, str, str]) -> str:
    """Return a gh-issue-list JSON payload for the given (number, title, state) tuples."""
    return json.dumps([
        {"number": n, "title": t, "state": s} for n, t, s in entries
    ])


# --- helpers ----------------------------------------------------------------


def _target(subclause: str = "33.4.1.5", issue: int = 42) -> CycleMember:
    """Build a CycleMember target for inner-orchestrator tests."""
    return CycleMember(subclause=subclause, issue=issue)


# --- issue helpers ----------------------------------------------------------


def test_issue_title_for() -> None:
    """issue_title_for produces the new canonical 'Satisfy IEEE 1800-2023 §X' title."""
    assert issue_title_for("33.4.1.5") == _NEW_CANONICAL


def test_parse_issue_number_from_create_output() -> None:
    """The number is extracted from a gh issue create URL."""
    output = "Creating issue\nhttps://github.com/o/r/issues/123\n"
    assert parse_issue_number_from_create_output(output) == 123


# --- find_or_create_issue: create / search-failure paths --------------------


def _patched_gh(
    stub_completed: Callable[..., MagicMock],
    list_payload: str = "[]", list_rc: int = 0,
    create_url: str = "", create_rc: int = 0,
) -> Any:
    """Patch subprocess.run with a sequence of gh responses (list, create)."""
    list_completed = stub_completed(stdout=list_payload, returncode=list_rc)
    create_completed = stub_completed(stdout=create_url, returncode=create_rc)
    return patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[list_completed, create_completed],
    )


def test_find_or_create_issue_creates_new(stub_completed: Callable[..., MagicMock]) -> None:
    """find_or_create_issue creates a new issue when none exists."""
    url = "https://github.com/o/r/issues/777"
    with _patched_gh(stub_completed, create_url=url):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS) == 777


def test_find_or_create_issue_creates_with_new_canonical_title(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """gh issue create receives the new canonical title."""
    url = "https://github.com/o/r/issues/777"
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout="[]"), stub_completed(stdout=url)],
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS)
    cmd = mock_run.call_args_list[1][0][0]
    assert cmd[cmd.index("--title") + 1] == _NEW_CANONICAL


def test_find_or_create_issue_handles_empty_list_stdout(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """find_or_create_issue treats an empty list stdout as no matches."""
    url = "https://github.com/o/r/issues/333"
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=""), stub_completed(stdout=url)],
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS) == 333


def test_find_or_create_issue_exits_on_list_failure(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A non-zero gh issue list exit is loud-fatal."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        return_value=stub_completed(returncode=1),
    ):
        with pytest.raises(SystemExit):
            find_or_create_issue("33.4.1.5", labels=_LABELS)


def test_find_or_create_issue_exits_on_create_failure(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A non-zero gh issue create exit is loud-fatal."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout="[]"), stub_completed(returncode=1)],
    ):
        with pytest.raises(SystemExit):
            find_or_create_issue("33.4.1.5", labels=_LABELS)


def test_find_or_create_issue_creates_when_no_title_matches(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A list with mismatched-title entries falls through to create."""
    body = _payload((1, "Different title", "OPEN"))
    create_url = "https://github.com/o/r/issues/333"
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=body), stub_completed(stdout=create_url),
        ],
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS) == 333


# --- find_or_create_issue: new-canonical match ------------------------------


def test_find_or_create_issue_returns_new_canonical_open(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A new-canonical-titled open issue is returned without rename or reopen."""
    body = _payload((99, _NEW_CANONICAL, "OPEN"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        return_value=stub_completed(stdout=body),
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS) == 99


def test_find_or_create_issue_does_not_rename_new_canonical(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A new-canonical-titled match does not trigger a title-rename edit."""
    body = _payload((99, _NEW_CANONICAL, "OPEN"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        return_value=stub_completed(stdout=body),
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS)
    rename_calls = [
        call for call in mock_run.call_args_list
        if call[0][0][:3] == ["gh", "issue", "edit"] and "--title" in call[0][0]
    ]
    assert rename_calls == []


def test_find_or_create_issue_reopens_new_canonical_closed(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A new-canonical-titled closed match is reopened."""
    body = _payload((55, _NEW_CANONICAL, "CLOSED"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS)
    reopen_cmd = mock_run.call_args_list[1][0][0]
    assert reopen_cmd[:3] == ["gh", "issue", "reopen"]


# --- find_or_create_issue: legacy-short ('Satisfy §X') ----------------------


def _run_rename_open_legacy(
    stub_completed: Callable[..., MagicMock], title: str, number: int,
) -> MagicMock:
    """Run find_or_create_issue against a single open legacy-titled match."""
    body = _payload((number, title, "OPEN"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS)
    return mock_run


def _run_reopen_closed_legacy(
    stub_completed: Callable[..., MagicMock], title: str, number: int,
) -> MagicMock:
    """Run find_or_create_issue against a single closed legacy-titled match."""
    body = _payload((number, title, "CLOSED"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 3,
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS)
    return mock_run


def test_find_or_create_issue_returns_legacy_short_number(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A 'Satisfy §X' open issue is recognised as legacy and returns its number."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=_payload((99, _LEGACY_SHORT, "OPEN"))),
        ] + [stub_completed()] * 2,
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS) == 99


def test_find_or_create_issue_renames_legacy_short_to_new_canonical(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A 'Satisfy §X' match is renamed to the new canonical title."""
    mock_run = _run_rename_open_legacy(stub_completed, _LEGACY_SHORT, 99)
    edit_cmd = mock_run.call_args_list[1][0][0]
    assert edit_cmd == ["gh", "issue", "edit", "99", "--title", _NEW_CANONICAL]


def test_find_or_create_issue_reopens_legacy_short_closed(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A closed 'Satisfy §X' match is reopened after the rename."""
    mock_run = _run_reopen_closed_legacy(stub_completed, _LEGACY_SHORT, 55)
    reopen_cmd = mock_run.call_args_list[2][0][0]
    assert reopen_cmd[:3] == ["gh", "issue", "reopen"]


# --- find_or_create_issue: legacy-audit-numeric -----------------------------


def test_legacy_issue_title_for() -> None:
    """legacy_issue_title_for produces the historical numeric 'Ensure …' title."""
    assert legacy_issue_title_for("33.4.1.5") == _LEGACY_AUDIT_NUMERIC


def test_find_or_create_issue_returns_legacy_audit_numeric_open_number(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-numeric titled open issue's number is returned."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=_payload((88, _LEGACY_AUDIT_NUMERIC, "OPEN"))),
        ] + [stub_completed()] * 2,
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS) == 88


def test_find_or_create_issue_renames_legacy_audit_numeric_open(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-numeric titled open issue is renamed to the new canonical."""
    mock_run = _run_rename_open_legacy(stub_completed, _LEGACY_AUDIT_NUMERIC, 88)
    edit_cmd = mock_run.call_args_list[1][0][0]
    assert edit_cmd == ["gh", "issue", "edit", "88", "--title", _NEW_CANONICAL]


def test_find_or_create_issue_reopens_legacy_audit_numeric_closed(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-numeric titled closed issue is reopened after the rename."""
    mock_run = _run_reopen_closed_legacy(
        stub_completed, _LEGACY_AUDIT_NUMERIC, 88,
    )
    reopen_cmd = mock_run.call_args_list[2][0][0]
    assert reopen_cmd[:3] == ["gh", "issue", "reopen"]


# --- find_or_create_issue: legacy-audit-annex (no §) ------------------------


def test_find_or_create_issue_returns_legacy_audit_annex_number(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-annex titled (no §) closed issue is recognised and returned."""
    body = _payload((609, _LEGACY_AUDIT_ANNEX, "CLOSED"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 3,
    ):
        assert find_or_create_issue("A.9.3", labels=_LABELS) == 609


def test_find_or_create_issue_renames_legacy_audit_annex(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-annex titled issue is renamed to 'Satisfy IEEE 1800-2023 §A.9.3'."""
    body = _payload((609, _LEGACY_AUDIT_ANNEX, "OPEN"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ) as mock_run:
        find_or_create_issue("A.9.3", labels=_LABELS)
    edit_cmd = mock_run.call_args_list[1][0][0]
    assert edit_cmd == [
        "gh", "issue", "edit", "609", "--title",
        "Satisfy IEEE 1800-2023 §A.9.3",
    ]


# --- find_or_create_issue: master-list --------------------------------------


def test_find_or_create_issue_returns_master_list_number(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A master-list-titled issue is returned by number."""
    body = _payload((35, _MASTER_LIST, "OPEN"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ):
        assert find_or_create_issue("33", labels=_LABELS) == 35


def test_find_or_create_issue_renames_master_list_to_new_canonical(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A master-list-titled match is renamed to bare 'Satisfy IEEE 1800-2023 §X'."""
    body = _payload((35, _MASTER_LIST, "OPEN"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ) as mock_run:
        find_or_create_issue("33", labels=_LABELS)
    edit_cmd = mock_run.call_args_list[1][0][0]
    assert edit_cmd == [
        "gh", "issue", "edit", "35", "--title",
        "Satisfy IEEE 1800-2023 §33",
    ]


def test_find_or_create_issue_reopens_master_list_closed(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A closed master-list issue is reopened after the rename."""
    body = _payload((35, _MASTER_LIST, "CLOSED"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 3,
    ) as mock_run:
        find_or_create_issue("33", labels=_LABELS)
    reopen_cmd = mock_run.call_args_list[2][0][0]
    assert reopen_cmd[:3] == ["gh", "issue", "reopen"]


def test_find_or_create_issue_master_list_exact_prefix_match(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A master-list title equal to the bare prefix (no descriptive text) matches."""
    body = _payload((35, "Implement IEEE 1800-2023 §33", "OPEN"))
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ):
        assert find_or_create_issue("33", labels=_LABELS) == 35


def test_find_or_create_issue_master_list_does_not_match_subclause_subprefix(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """An §33 master-list title must not match a §33.4 lookup."""
    body = _payload((35, _MASTER_LIST, "OPEN"))
    create_url = "https://github.com/o/r/issues/700"
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=body), stub_completed(stdout=create_url),
        ],
    ):
        assert find_or_create_issue("33.4", labels=_LABELS) == 700


# --- find_or_create_issue: duplicate-deletion path --------------------------


def _master_list_with_duplicate_payload() -> str:
    """Build a body with master-list #35 + a 'Satisfy §33' duplicate #1276."""
    return _payload(
        (35, _MASTER_LIST, "OPEN"),
        (1276, "Satisfy §33", "OPEN"),
    )


def test_find_or_create_issue_deletes_newer_duplicate(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """When two matches exist, the newer is hard-deleted via gh issue delete."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=_master_list_with_duplicate_payload()),
        ] + [stub_completed()] * 3,
    ) as mock_run:
        find_or_create_issue("33", labels=_LABELS)
    delete_cmd = mock_run.call_args_list[1][0][0]
    assert delete_cmd == ["gh", "issue", "delete", "1276", "--yes"]


def test_find_or_create_issue_keeps_older_when_duplicates(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """When two matches exist, the older issue's number is returned."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=_master_list_with_duplicate_payload()),
        ] + [stub_completed()] * 3,
    ):
        assert find_or_create_issue("33", labels=_LABELS) == 35


def test_find_or_create_issue_renames_older_master_list_with_duplicates(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """When the older match is master-list, it is also renamed (no special case)."""
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[
            stub_completed(stdout=_master_list_with_duplicate_payload()),
        ] + [stub_completed()] * 3,
    ) as mock_run:
        find_or_create_issue("33", labels=_LABELS)
    edit_cmd = mock_run.call_args_list[2][0][0]
    assert edit_cmd == [
        "gh", "issue", "edit", "35", "--title",
        "Satisfy IEEE 1800-2023 §33",
    ]


def _older_legacy_with_duplicate_payload() -> str:
    """Build a body with a closed older legacy-audit-annex + a newer 'Satisfy §X'."""
    older_title = (
        "Ensure IEEE 1800-2023 A.2.1.3 functionalities and tests are"
        " implemented and properly named"
    )
    return _payload(
        (542, older_title, "CLOSED"),
        (1279, "Satisfy §A.2.1.3", "OPEN"),
    )


def test_find_or_create_issue_renames_older_legacy_with_duplicates(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """When the older match is non-master-list legacy, it is renamed."""
    body = _older_legacy_with_duplicate_payload()
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 4,
    ) as mock_run:
        find_or_create_issue("A.2.1.3", labels=_LABELS)
    edit_cmd = mock_run.call_args_list[2][0][0]
    assert edit_cmd == [
        "gh", "issue", "edit", "542", "--title",
        "Satisfy IEEE 1800-2023 §A.2.1.3",
    ]


def test_find_or_create_issue_reopens_older_legacy_closed_with_duplicates(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A closed older legacy match is reopened after delete + rename."""
    body = _older_legacy_with_duplicate_payload()
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 4,
    ) as mock_run:
        find_or_create_issue("A.2.1.3", labels=_LABELS)
    reopen_cmd = mock_run.call_args_list[3][0][0]
    assert reopen_cmd[:3] == ["gh", "issue", "reopen"]


def test_find_or_create_issue_deletes_all_newer_duplicates(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """Every newer match is deleted, not just the most-recent one."""
    body = _payload(
        (35, _MASTER_LIST, "OPEN"),
        (1276, "Satisfy §33", "OPEN"),
        (2000, "Satisfy §33", "OPEN"),
    )
    with patch(
        "satisfy_subclause.pipeline.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 4,
    ) as mock_run:
        find_or_create_issue("33", labels=_LABELS)
    delete_targets = [
        call[0][0][3] for call in mock_run.call_args_list[1:3]
        if call[0][0][:3] == ["gh", "issue", "delete"]
    ]
    assert delete_targets == ["1276", "2000"]


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


def test_dispatch_cycle_does_not_call_oracle() -> None:
    """dispatch_cycle no longer invokes the satisfaction oracle."""
    mock_issue, mock_mut = _patched_for_cycle()
    with mock_issue:
        with mock_mut:
            dispatch_cycle(
                ["33.4.1.5", "33.6"], "~/LRM.pdf",
                model="opus", labels=_LABELS,
            )
    assert not hasattr(oracles, "is_subclause_satisfied")


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


def test_satisfy_does_not_call_satisfaction_oracle() -> None:
    """satisfy_subclause never invokes is_subclause_satisfied (it's removed)."""
    assert not hasattr(oracles, "is_subclause_satisfied")


# --- CycleMember dataclass --------------------------------------------------


def test_cycle_member_holds_subclause() -> None:
    """CycleMember stores the subclause identifier."""
    member = CycleMember(subclause="33.4.1.5", issue=42)
    assert member.subclause == "33.4.1.5"
