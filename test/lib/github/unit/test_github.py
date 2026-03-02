"""Tests for lib.github."""

import json
import subprocess
from unittest.mock import patch

import pytest

from lib.github import (
    build_synced_body,
    fetch_issue_body,
    next_unchecked,
    sync_checklist,
    update_issue_body,
)


# --- fetch_issue_body ---


def test_fetch_issue_body_success() -> None:
    """Body text is returned on successful fetch."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="hello\n")
    with patch("lib.github.subprocess.run", return_value=cp):
        assert fetch_issue_body("org", "repo", 1) == "hello\n"


def test_fetch_issue_body_prints_action(capsys) -> None:
    """Prints that it is fetching the issue."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="body\n")
    with patch("lib.github.subprocess.run", return_value=cp):
        fetch_issue_body("org", "repo", 42)
    assert "Fetching issue #42" in capsys.readouterr().out


def test_fetch_issue_body_failure() -> None:
    """SystemExit raised on fetch failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.github.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            fetch_issue_body("org", "repo", 1)


# --- update_issue_body ---


def test_update_issue_body_success() -> None:
    """Correct payload is sent on update."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.github.subprocess.run", return_value=cp) as mock_run:
        update_issue_body("org", "repo", 1, "new body")
    assert mock_run.call_args.kwargs["input"] == json.dumps(
        {"body": "new body"},
    )


def test_update_issue_body_prints_action(capsys) -> None:
    """Prints that it is updating the issue."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.github.subprocess.run", return_value=cp):
        update_issue_body("org", "repo", 42, "body")
    assert "Updating issue #42" in capsys.readouterr().out


def test_update_issue_body_failure() -> None:
    """SystemExit raised on update failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.github.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            update_issue_body("org", "repo", 1, "body")


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


# --- sync_checklist ---


def test_sync_checklist_calls_update() -> None:
    """Fetches body, transforms, and updates with correct args."""
    with (
        patch("lib.github.fetch_issue_body", return_value=""),
        patch("lib.github.update_issue_body") as mock_update,
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
