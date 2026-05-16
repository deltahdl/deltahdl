"""Unit tests for the find-or-create surface in lib.python.github."""

import json
from collections.abc import Callable
from typing import Any
from unittest.mock import MagicMock, patch

import pytest

from lib.python.github import (
    find_or_create_issue,
    issue_title_for,
    legacy_issue_title_for,
    parse_issue_number_from_create_output,
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


# --- issue helpers ----------------------------------------------------------


def test_issue_title_for() -> None:
    """issue_title_for produces the new canonical 'Satisfy IEEE 1800-2023 §X' title."""
    assert issue_title_for("33.4.1.5") == _NEW_CANONICAL


def test_parse_issue_number_from_create_output() -> None:
    """The number is extracted from a gh issue create URL."""
    output = "Creating issue\nhttps://github.com/o/r/issues/123\n"
    assert parse_issue_number_from_create_output(output) == 123


def test_legacy_issue_title_for() -> None:
    """legacy_issue_title_for produces the historical numeric 'Ensure …' title."""
    assert legacy_issue_title_for("33.4.1.5") == _LEGACY_AUDIT_NUMERIC


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
        "lib.python.github.subprocess.run",
        side_effect=[list_completed, create_completed],
    )


def test_find_or_create_issue_creates_new(stub_completed: Callable[..., MagicMock]) -> None:
    """find_or_create_issue creates a new issue when none exists."""
    url = "https://github.com/o/r/issues/777"
    with _patched_gh(stub_completed, create_url=url):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS)[0] == 777


def test_find_or_create_issue_creates_with_new_canonical_title(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """gh issue create receives the new canonical title."""
    url = "https://github.com/o/r/issues/777"
    with patch(
        "lib.python.github.subprocess.run",
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
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=""), stub_completed(stdout=url)],
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS)[0] == 333


def test_find_or_create_issue_exits_on_list_failure(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A non-zero gh issue list exit is loud-fatal."""
    with patch(
        "lib.python.github.subprocess.run",
        return_value=stub_completed(returncode=1),
    ):
        with pytest.raises(SystemExit):
            find_or_create_issue("33.4.1.5", labels=_LABELS)


def test_find_or_create_issue_exits_on_create_failure(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A non-zero gh issue create exit is loud-fatal."""
    with patch(
        "lib.python.github.subprocess.run",
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
        "lib.python.github.subprocess.run",
        side_effect=[
            stub_completed(stdout=body), stub_completed(stdout=create_url),
        ],
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS)[0] == 333


# --- find_or_create_issue: new-canonical match ------------------------------


def test_find_or_create_issue_returns_new_canonical_open(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A new-canonical-titled open issue is returned without rename or reopen."""
    body = _payload((99, _NEW_CANONICAL, "OPEN"))
    with patch(
        "lib.python.github.subprocess.run",
        return_value=stub_completed(stdout=body),
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS)[0] == 99


def test_find_or_create_issue_does_not_rename_new_canonical(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A new-canonical-titled match does not trigger a title-rename edit."""
    body = _payload((99, _NEW_CANONICAL, "OPEN"))
    with patch(
        "lib.python.github.subprocess.run",
        return_value=stub_completed(stdout=body),
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS)
    rename_calls = [
        call for call in mock_run.call_args_list
        if call[0][0][:3] == ["gh", "issue", "edit"] and "--title" in call[0][0]
    ]
    assert rename_calls == []


def _reopen_calls(mock_run: MagicMock) -> list[list[str]]:
    """Return every ``gh issue reopen`` invocation captured by *mock_run*."""
    return [
        call[0][0] for call in mock_run.call_args_list
        if call[0][0][:3] == ["gh", "issue", "reopen"]
    ]


def test_find_or_create_issue_does_not_reopen_new_canonical_closed(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A closed new-canonical match is NOT silently reopened — caller's choice."""
    body = _payload((55, _NEW_CANONICAL, "CLOSED"))
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS)
    assert _reopen_calls(mock_run) == []


def test_find_or_create_issue_returns_closed_state_for_new_canonical_closed(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A closed new-canonical match reports its CLOSED state back to the caller."""
    body = _payload((55, _NEW_CANONICAL, "CLOSED"))
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ):
        _number, state = find_or_create_issue("33.4.1.5", labels=_LABELS)
    assert state == "CLOSED"


def test_find_or_create_issue_returns_open_state_for_open_match(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """An open match reports its OPEN state back to the caller."""
    body = _payload((99, _NEW_CANONICAL, "OPEN"))
    with patch(
        "lib.python.github.subprocess.run",
        return_value=stub_completed(stdout=body),
    ):
        _number, state = find_or_create_issue("33.4.1.5", labels=_LABELS)
    assert state == "OPEN"


def test_find_or_create_issue_returns_open_state_for_newly_created(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A freshly-created issue is reported as OPEN."""
    url = "https://github.com/o/r/issues/777"
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout="[]"), stub_completed(stdout=url)],
    ):
        _number, state = find_or_create_issue("33.4.1.5", labels=_LABELS)
    assert state == "OPEN"


# --- find_or_create_issue: legacy-short ('Satisfy §X') ----------------------


def _run_rename_open_legacy(
    stub_completed: Callable[..., MagicMock], title: str, number: int,
) -> MagicMock:
    """Run find_or_create_issue against a single open legacy-titled match."""
    body = _payload((number, title, "OPEN"))
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS)
    return mock_run


def _run_closed_legacy(
    stub_completed: Callable[..., MagicMock], title: str, number: int,
) -> MagicMock:
    """Run find_or_create_issue against a single closed legacy-titled match."""
    body = _payload((number, title, "CLOSED"))
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 3,
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS)
    return mock_run


def test_find_or_create_issue_returns_legacy_short_number(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A 'Satisfy §X' open issue is recognised as legacy and returns its number."""
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[
            stub_completed(stdout=_payload((99, _LEGACY_SHORT, "OPEN"))),
        ] + [stub_completed()] * 2,
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS)[0] == 99


def test_find_or_create_issue_renames_legacy_short_to_new_canonical(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A 'Satisfy §X' match is renamed to the new canonical title."""
    mock_run = _run_rename_open_legacy(stub_completed, _LEGACY_SHORT, 99)
    edit_cmd = mock_run.call_args_list[1][0][0]
    assert edit_cmd == ["gh", "issue", "edit", "99", "--title", _NEW_CANONICAL]


def test_find_or_create_issue_does_not_reopen_legacy_short_closed(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A closed 'Satisfy §X' match is NOT silently reopened after the rename."""
    mock_run = _run_closed_legacy(stub_completed, _LEGACY_SHORT, 55)
    assert _reopen_calls(mock_run) == []


# --- find_or_create_issue: legacy-audit-numeric -----------------------------


def test_find_or_create_issue_returns_legacy_audit_numeric_open_number(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-numeric titled open issue's number is returned."""
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[
            stub_completed(stdout=_payload((88, _LEGACY_AUDIT_NUMERIC, "OPEN"))),
        ] + [stub_completed()] * 2,
    ):
        assert find_or_create_issue("33.4.1.5", labels=_LABELS)[0] == 88


def test_find_or_create_issue_renames_legacy_audit_numeric_open(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-numeric titled open issue is renamed to the new canonical."""
    mock_run = _run_rename_open_legacy(stub_completed, _LEGACY_AUDIT_NUMERIC, 88)
    edit_cmd = mock_run.call_args_list[1][0][0]
    assert edit_cmd == ["gh", "issue", "edit", "88", "--title", _NEW_CANONICAL]


def test_find_or_create_issue_does_not_reopen_legacy_audit_numeric_closed(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-numeric closed issue is NOT silently reopened after the rename."""
    mock_run = _run_closed_legacy(
        stub_completed, _LEGACY_AUDIT_NUMERIC, 88,
    )
    assert _reopen_calls(mock_run) == []


# --- find_or_create_issue: legacy-audit-annex (no §) ------------------------


def test_find_or_create_issue_returns_legacy_audit_annex_number(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-annex titled (no §) closed issue is recognised and returned."""
    body = _payload((609, _LEGACY_AUDIT_ANNEX, "CLOSED"))
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 3,
    ):
        assert find_or_create_issue("A.9.3", labels=_LABELS)[0] == 609


def test_find_or_create_issue_renames_legacy_audit_annex(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A legacy-audit-annex titled issue is renamed to 'Satisfy IEEE 1800-2023 §A.9.3'."""
    body = _payload((609, _LEGACY_AUDIT_ANNEX, "OPEN"))
    with patch(
        "lib.python.github.subprocess.run",
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
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ):
        assert find_or_create_issue("33", labels=_LABELS)[0] == 35


def test_find_or_create_issue_renames_master_list_to_new_canonical(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A master-list-titled match is renamed to bare 'Satisfy IEEE 1800-2023 §X'."""
    body = _payload((35, _MASTER_LIST, "OPEN"))
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ) as mock_run:
        find_or_create_issue("33", labels=_LABELS)
    edit_cmd = mock_run.call_args_list[1][0][0]
    assert edit_cmd == [
        "gh", "issue", "edit", "35", "--title",
        "Satisfy IEEE 1800-2023 §33",
    ]


def test_find_or_create_issue_does_not_reopen_master_list_closed(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A closed master-list issue is NOT silently reopened after the rename."""
    body = _payload((35, _MASTER_LIST, "CLOSED"))
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 3,
    ) as mock_run:
        find_or_create_issue("33", labels=_LABELS)
    assert _reopen_calls(mock_run) == []


def test_find_or_create_issue_master_list_exact_prefix_match(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A master-list title equal to the bare prefix (no descriptive text) matches."""
    body = _payload((35, "Implement IEEE 1800-2023 §33", "OPEN"))
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 2,
    ):
        assert find_or_create_issue("33", labels=_LABELS)[0] == 35


def test_find_or_create_issue_master_list_does_not_match_subclause_subprefix(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """An §33 master-list title must not match a §33.4 lookup."""
    body = _payload((35, _MASTER_LIST, "OPEN"))
    create_url = "https://github.com/o/r/issues/700"
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[
            stub_completed(stdout=body), stub_completed(stdout=create_url),
        ],
    ):
        assert find_or_create_issue("33.4", labels=_LABELS)[0] == 700


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
        "lib.python.github.subprocess.run",
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
        "lib.python.github.subprocess.run",
        side_effect=[
            stub_completed(stdout=_master_list_with_duplicate_payload()),
        ] + [stub_completed()] * 3,
    ):
        assert find_or_create_issue("33", labels=_LABELS)[0] == 35


def test_find_or_create_issue_renames_older_master_list_with_duplicates(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """When the older match is master-list, it is also renamed (no special case)."""
    with patch(
        "lib.python.github.subprocess.run",
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
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 4,
    ) as mock_run:
        find_or_create_issue("A.2.1.3", labels=_LABELS)
    edit_cmd = mock_run.call_args_list[2][0][0]
    assert edit_cmd == [
        "gh", "issue", "edit", "542", "--title",
        "Satisfy IEEE 1800-2023 §A.2.1.3",
    ]


def test_find_or_create_issue_does_not_reopen_older_legacy_closed_with_duplicates(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """A closed older legacy match is NOT silently reopened after delete + rename."""
    body = _older_legacy_with_duplicate_payload()
    with patch(
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 4,
    ) as mock_run:
        find_or_create_issue("A.2.1.3", labels=_LABELS)
    assert _reopen_calls(mock_run) == []


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
        "lib.python.github.subprocess.run",
        side_effect=[stub_completed(stdout=body)] + [stub_completed()] * 4,
    ) as mock_run:
        find_or_create_issue("33", labels=_LABELS)
    delete_targets = [
        call[0][0][3] for call in mock_run.call_args_list[1:3]
        if call[0][0][:3] == ["gh", "issue", "delete"]
    ]
    assert delete_targets == ["1276", "2000"]


# --- label argument shape ---------------------------------------------------


_LABELS_THREE = ["IEEE 1800-2023", "bug", "needs-triage"]


def _patched_run_create(
    stub_completed: Callable[..., MagicMock],
) -> Any:
    """Patch subprocess.run with a (no-match list, create-success) sequence."""
    list_done = stub_completed(stdout="[]")
    create_done = stub_completed(stdout="https://github.com/o/r/issues/501")
    return patch(
        "lib.python.github.subprocess.run",
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
        "lib.python.github.subprocess.run",
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
            value: str = cmd[cmd.index("--add-label") + 1]
            return value
    raise AssertionError("no --add-label call recorded")


def test_create_passes_every_label_in_order(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """gh issue create includes every --labels-supplied label in order."""
    with _patched_run_create(stub_completed) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS_THREE)
    create_cmd = mock_run.call_args_list[1][0][0]
    assert _label_create_values(create_cmd) == _LABELS_THREE


def test_add_label_joins_labels_with_commas(
    stub_completed: Callable[..., MagicMock],
) -> None:
    """Multiple labels collapse into a single comma-separated --add-label arg."""
    with _patched_run_with_match(
        stub_completed, number=99, title=_NEW_CANONICAL,
    ) as mock_run:
        find_or_create_issue("33.4.1.5", labels=_LABELS_THREE)
    assert _add_label_value(mock_run) == ",".join(_LABELS_THREE)
