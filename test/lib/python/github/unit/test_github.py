"""Tests for lib.github."""

import json
import subprocess
from unittest.mock import patch

import pytest

from lib.python.github import (
    build_synced_body,
    close_issue,
    fetch_issue_body,
    fetch_issue_title,
    mark_master_complete,
    mark_subclause_complete,
    next_unchecked,
    remove_test_row,
    sync_checklist,
    update_issue_body,
)


# --- fetch_issue_body ---


def test_fetch_issue_body_success() -> None:
    """Body text is returned on successful fetch."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="hello\n")
    with patch("lib.python.github.subprocess.run", return_value=cp):
        assert fetch_issue_body("org", "repo", 1) == "hello\n"


def test_fetch_issue_body_prints_action(capsys) -> None:
    """Prints that it is fetching the issue."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="body\n")
    with patch("lib.python.github.subprocess.run", return_value=cp):
        fetch_issue_body("org", "repo", 42)
    assert "Fetching issue #42" in capsys.readouterr().out


def test_fetch_issue_body_failure() -> None:
    """SystemExit raised on fetch failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            fetch_issue_body("org", "repo", 1)


# --- fetch_issue_title ---


def test_fetch_issue_title_success() -> None:
    """Title text is returned on successful fetch."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="Title\n")
    with patch("lib.python.github.subprocess.run", return_value=cp):
        assert fetch_issue_title("org", "repo", 1) == "Title"


def test_fetch_issue_title_prints_action(capsys) -> None:
    """Prints that it is fetching the issue title."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="T\n")
    with patch("lib.python.github.subprocess.run", return_value=cp):
        fetch_issue_title("org", "repo", 42)
    assert "Fetching title" in capsys.readouterr().out


def test_fetch_issue_title_failure() -> None:
    """SystemExit raised on fetch failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            fetch_issue_title("org", "repo", 1)


# --- update_issue_body ---


def test_update_issue_body_success() -> None:
    """Correct payload is sent on update."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp) as mock_run:
        update_issue_body("org", "repo", 1, "new body")
    assert mock_run.call_args.kwargs["input"] == json.dumps(
        {"body": "new body"},
    )


def test_update_issue_body_prints_action(capsys) -> None:
    """Prints that it is updating the issue."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp):
        update_issue_body("org", "repo", 42, "body")
    assert "Updating issue #42" in capsys.readouterr().out


def test_update_issue_body_failure() -> None:
    """SystemExit raised on update failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            update_issue_body("org", "repo", 1, "body")


# --- close_issue ---


def test_close_issue_calls_correct_endpoint() -> None:
    """Calls gh api with the correct issue endpoint."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp) as mock_run:
        close_issue("org", "repo", 42, "all done")
    assert "repos/org/repo/issues/42" in mock_run.call_args[0][0]


def test_close_issue_sets_state_closed() -> None:
    """Passes state=closed to gh api."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp) as mock_run:
        close_issue("org", "repo", 42, "all done")
    assert "state=closed" in mock_run.call_args[0][0]


def test_close_issue_prints_reason(capsys) -> None:
    """Prints the reason for closing."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp):
        close_issue("org", "repo", 42, "all done")
    assert "all done" in capsys.readouterr().out


def test_close_issue_prints_confirmation(capsys) -> None:
    """Prints confirmation after closing."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp):
        close_issue("org", "repo", 42, "all done")
    assert "Closed issue #42" in capsys.readouterr().out


def test_close_issue_failure() -> None:
    """SystemExit raised on close failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            close_issue("org", "repo", 1, "reason")


# --- build_synced_body ---


def test_build_synced_body_fresh() -> None:
    """Checklist is created when body has no subclauses section."""
    assert build_synced_body("", {"4.1": "General", "4.2": "Exec"}) == (
        "## Subclauses\n\n"
        "- [ ] 4.1 General\n"
        "- [ ] 4.2 Exec\n"
    )


def test_build_synced_body_preserves_checked() -> None:
    """Checked items remain checked after sync."""
    body = (
        "## Subclauses\n\n"
        "- [x] 4.1 General\n"
        "- [ ] 4.2 Exec\n"
    )
    assert build_synced_body(body, {"4.1": "General", "4.2": "Exec"}) == body


def test_build_synced_body_adds_missing() -> None:
    """New items are added as unchecked."""
    body = "## Subclauses\n\n- [x] 4.1 General\n"
    assert build_synced_body(body, {"4.1": "General", "4.2": "Exec"}) == (
        "## Subclauses\n\n"
        "- [x] 4.1 General\n"
        "- [ ] 4.2 Exec\n"
    )


def test_build_synced_body_removes_stale() -> None:
    """Items not in the list are removed."""
    body = (
        "## Subclauses\n\n"
        "- [x] 4.1 General\n"
        "- [ ] 4.2 Exec\n"
    )
    assert build_synced_body(body, {"4.1": "General"}) == (
        "## Subclauses\n\n"
        "- [x] 4.1 General\n"
    )


def test_build_synced_body_indents_by_depth() -> None:
    """Deeper subclauses are indented relative to the shallowest."""
    items = {
        "6.3": "Value set",
        "6.3.1": "Logic values",
        "6.3.2": "Strengths",
        "6.3.2.1": "Charge strength",
    }
    assert build_synced_body("", items) == (
        "## Subclauses\n\n"
        "- [ ] 6.3 Value set\n"
        "  - [ ] 6.3.1 Logic values\n"
        "  - [ ] 6.3.2 Strengths\n"
        "    - [ ] 6.3.2.1 Charge strength\n"
    )


def test_build_synced_body_preserves_checked_indented() -> None:
    """Checked items remain checked in indented checklists."""
    body = (
        "## Subclauses\n\n"
        "- [x] 6.3 Value set\n"
        "  - [ ] 6.3.1 Logic values\n"
    )
    result = build_synced_body(body, {"6.3": "Value set", "6.3.1": "Logic values"})
    assert result == body


# --- sync_checklist ---


def test_sync_checklist_calls_update() -> None:
    """Fetches body, transforms, and updates with correct args."""
    with (
        patch("lib.python.github.fetch_issue_body", return_value=""),
        patch("lib.python.github.update_issue_body") as mock_update,
    ):
        sync_checklist("org", "repo", 1, {"4.1": "General"})
    assert mock_update.call_args[0] == (
        "org", "repo", 1, "## Subclauses\n\n- [ ] 4.1 General\n",
    )


# --- next_unchecked ---


def test_next_unchecked_returns_first() -> None:
    """First unchecked item number is returned."""
    body = (
        "## Subclauses\n\n"
        "- [x] 4.1 General\n"
        "- [ ] 4.2 Exec\n"
        "- [ ] 4.3 Sim\n"
    )
    assert next_unchecked(body) == "4.2"


def test_next_unchecked_all_checked() -> None:
    """None when all items are checked."""
    body = "## Subclauses\n\n- [x] 4.1 General\n- [x] 4.2 Exec\n"
    assert next_unchecked(body) is None


def test_next_unchecked_no_checkboxes() -> None:
    """None when body has no checkboxes."""
    assert next_unchecked("Some text without checkboxes") is None


def test_next_unchecked_indented() -> None:
    """First unchecked item is found even when indented."""
    body = (
        "## Subclauses\n\n"
        "- [x] 6.3 Value set\n"
        "  - [ ] 6.3.1 Logic values\n"
        "  - [ ] 6.3.2 Strengths\n"
    )
    assert next_unchecked(body) == "6.3.1"


# --- mark_master_complete ---


_MASTER_BODY = """\
## Phase 1

| Section | Title | Issue | Status |
|---------|-------|-------|--------|
| §3 | Building blocks | #5 | :white_check_mark: |
| §4 | Scheduling semantics | #6 | |
"""


def _mark_master_and_capture(monkeypatch, sub_issue=6) -> str:
    """Call mark_master_complete and return the updated body."""
    monkeypatch.setattr(
        "lib.python.github.fetch_issue_body", lambda *_a: _MASTER_BODY,
    )
    updated: list[str] = []
    monkeypatch.setattr(
        "lib.python.github.update_issue_body",
        lambda _o, _r, _i, body: updated.append(body),
    )
    mark_master_complete("o", "r", 1, sub_issue)
    assert updated, "update_issue_body was not called"
    return updated[0]


def test_mark_master_complete_ticks_status(monkeypatch) -> None:
    """Row matching the sub-issue gets :white_check_mark: in Status."""
    body = _mark_master_and_capture(monkeypatch)
    assert "| #6 | :white_check_mark: |" in body


def test_mark_master_complete_preserves_other_rows(monkeypatch) -> None:
    """Other rows are unchanged after marking."""
    body = _mark_master_and_capture(monkeypatch)
    assert "| #5 | :white_check_mark: |" in body


def test_mark_master_complete_warns_when_not_found(
    monkeypatch, capsys,
) -> None:
    """Prints warning when no matching row found."""
    monkeypatch.setattr(
        "lib.python.github.fetch_issue_body", lambda *_a: _MASTER_BODY,
    )
    monkeypatch.setattr(
        "lib.python.github.update_issue_body", lambda *_a: None,
    )
    mark_master_complete("o", "r", 1, 999)
    assert "WARNING" in capsys.readouterr().err


# --- mark_subclause_complete ---


_SUBCLAUSE_BODY = (
    "## Subclauses\n\n"
    "- [x] 15.4.7 Peek()\n"
    "- [ ] 15.4.8 Try_peek()\n"
    "- [ ] 15.4.9 Parameterized mailboxes\n"
)

_SHA = "abc1234def5678901234567890abcdef12345678"


def _mark_and_capture(monkeypatch, body=_SUBCLAUSE_BODY, subclause="15.4.8"):
    """Call mark_subclause_complete and return the updated body."""
    monkeypatch.setattr(
        "lib.python.github.fetch_issue_body", lambda *_a: body,
    )
    updated: list[str] = []
    monkeypatch.setattr(
        "lib.python.github.update_issue_body",
        lambda _o, _r, _i, b: updated.append(b),
    )
    mark_subclause_complete("org", "repo", 17, subclause, _SHA)
    assert updated, "update_issue_body was not called"
    return updated[0]


def test_mark_subclause_complete_checks_box(monkeypatch) -> None:
    """The checkbox is checked."""
    assert "- [x] [15.4.8 Try_peek()](" in _mark_and_capture(monkeypatch)


def test_mark_subclause_complete_links_label(monkeypatch) -> None:
    """The label links to the commit URL."""
    body = _mark_and_capture(monkeypatch)
    assert f"org/repo/commit/{_SHA})" in body


def test_mark_subclause_complete_preserves_other(monkeypatch) -> None:
    """Other lines are unchanged."""
    body = _mark_and_capture(monkeypatch)
    assert "- [x] 15.4.7 Peek()\n" in body


def test_mark_subclause_complete_preserves_unchecked(monkeypatch) -> None:
    """Other unchecked lines are unchanged."""
    body = _mark_and_capture(monkeypatch)
    assert "- [ ] 15.4.9 Parameterized mailboxes\n" in body


def test_mark_subclause_complete_indented(monkeypatch) -> None:
    """Works with indented subclauses."""
    body = (
        "## Subclauses\n\n"
        "- [x] 15.4 Mailboxes\n"
        "  - [ ] 15.4.1 New()\n"
    )
    result = _mark_and_capture(monkeypatch, body=body, subclause="15.4.1")
    assert "  - [x] [15.4.1 New()](" in result


def test_mark_subclause_complete_warns_not_found(
    monkeypatch, capsys,
) -> None:
    """Prints warning when subclause is not found."""
    monkeypatch.setattr(
        "lib.python.github.fetch_issue_body",
        lambda *_a: "- [x] 15.4.8 Try_peek()\n",
    )
    monkeypatch.setattr(
        "lib.python.github.update_issue_body", lambda *_a: None,
    )
    mark_subclause_complete("org", "repo", 17, "99.99", _SHA)
    assert "WARNING" in capsys.readouterr().err


# --- remove_test_row ---


_TABLE_BODY = (
    "| Suite | Test | Status | Action |\n"
    "|-------|------|--------|--------|\n"
    "| S | FooTest | Reviewed | Kept |\n"
    "| S | BarTest | Unreviewed | |\n"
)


def test_remove_test_row_removes_matching() -> None:
    """Removes the row matching the test name."""
    assert "FooTest" not in remove_test_row(_TABLE_BODY, "FooTest")


def test_remove_test_row_preserves_other_rows() -> None:
    """Other rows are preserved after removal."""
    assert "BarTest" in remove_test_row(_TABLE_BODY, "FooTest")


def test_remove_test_row_not_found() -> None:
    """Raises ValueError when test name not in body."""
    with pytest.raises(ValueError, match="NoSuchTest"):
        remove_test_row(_TABLE_BODY, "NoSuchTest")
