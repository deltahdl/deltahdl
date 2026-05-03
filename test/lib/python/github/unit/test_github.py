"""Tests for lib.github."""

import json
import subprocess
from typing import Any
from unittest.mock import patch

import pytest

from lib.python.github import (
    add_labels,
    build_subclause_table,
    build_synced_body,
    create_issue,
    parse_subclause_rows,
    sync_subclause_table,
    update_subclause_status,
    close_issue,
    delete_issue,
    extract_subclause_from_title,
    fetch_issue_body,
    fetch_issue_state,
    fetch_issue_title,
    find_issue_by_title,
    format_subclause_label,
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


def test_fetch_issue_body_prints_action(
    capsys: pytest.CaptureFixture[str],
) -> None:
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


def test_fetch_issue_title_prints_action(
    capsys: pytest.CaptureFixture[str],
) -> None:
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


# --- fetch_issue_state ---


def test_fetch_issue_state_returns_state() -> None:
    """Returns the issue state string."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="open\n")
    with patch("lib.python.github.subprocess.run", return_value=cp):
        assert fetch_issue_state("org", "repo", 42) == "open"


def test_fetch_issue_state_failure() -> None:
    """SystemExit raised on fetch failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            fetch_issue_state("org", "repo", 1)


# --- update_issue_body ---


def test_update_issue_body_success() -> None:
    """Correct payload is sent on update."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp) as mock_run:
        update_issue_body("org", "repo", 1, "new body")
    assert mock_run.call_args.kwargs["input"] == json.dumps(
        {"body": "new body"},
    )


def test_update_issue_body_prints_action(
    capsys: pytest.CaptureFixture[str],
) -> None:
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


def test_close_issue_prints_reason(
    capsys: pytest.CaptureFixture[str],
) -> None:
    """Prints the reason for closing."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp):
        close_issue("org", "repo", 42, "all done")
    assert "all done" in capsys.readouterr().out


def test_close_issue_prints_confirmation(
    capsys: pytest.CaptureFixture[str],
) -> None:
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


# --- extract_subclause_from_title ---


def test_extract_subclause_numeric() -> None:
    """Extracts numeric subclause from title."""
    assert extract_subclause_from_title("... §3.12.1 ...") == "3.12.1"


def test_extract_subclause_annex() -> None:
    """Extracts annex subclause from title."""
    assert extract_subclause_from_title("... A.1.1 ...") == "A.1.1"


def test_extract_subclause_not_found() -> None:
    """Returns empty string when no subclause found."""
    assert extract_subclause_from_title("Random title") == ""


# --- delete_issue ---


def test_delete_issue_calls_gh_delete() -> None:
    """Calls gh issue delete with correct issue number."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp) as mock_run:
        delete_issue(42)
    cmd = mock_run.call_args[0][0]
    assert "delete" in cmd


def test_delete_issue_passes_yes_flag() -> None:
    """Passes --yes to skip confirmation."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp) as mock_run:
        delete_issue(42)
    cmd = mock_run.call_args[0][0]
    assert "--yes" in cmd


def test_delete_issue_passes_issue_number() -> None:
    """Passes the issue number as a string argument."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp) as mock_run:
        delete_issue(99)
    cmd = mock_run.call_args[0][0]
    assert "99" in cmd


def test_delete_issue_failure() -> None:
    """SystemExit raised on delete failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            delete_issue(1)


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


# ---- format_subclause_label ------------------------------------------------


def test_format_subclause_label_numeric() -> None:
    """Numeric subclauses get the section sign prefix."""
    assert format_subclause_label("3.14.1") == "§3.14.1"


def test_format_subclause_label_annex() -> None:
    """Annex subclauses use bare identifiers without section sign."""
    assert format_subclause_label("A.1.1") == "A.1.1"


# ---- build_subclause_table -------------------------------------------------


def test_build_subclause_table_basic() -> None:
    """Builds a markdown table with Unreviewed status."""
    result = build_subclause_table({"3.1": "General", "3.2": "Design"})
    assert "| §3.1 | General | Unreviewed | |" in result


def test_build_subclause_table_annex_label() -> None:
    """Annex subclauses use bare identifiers in the label column."""
    result = build_subclause_table({"A.1": "Syntax"})
    assert "| A.1 | Syntax | Unreviewed | |" in result


def test_build_subclause_table_has_header() -> None:
    """Table starts with a header row."""
    result = build_subclause_table({"3.1": "General"})
    assert result.startswith("| Label | Title | Status | Action |")


# ---- update_subclause_status -----------------------------------------------

_SUBCLAUSE_TABLE = (
    "| Label | Title | Status | Action |\n"
    "|-------|-------|--------|--------|\n"
    "| §3.1 | General | Unreviewed | |\n"
    "| §3.2 | Design | Unreviewed | |\n"
)


def test_update_subclause_status_sets_reviewed() -> None:
    """Updates status column to Reviewed."""
    result = update_subclause_status(_SUBCLAUSE_TABLE, "§3.1", "Reviewed")
    assert "| §3.1 | General | Reviewed |" in result


def test_update_subclause_status_sets_action() -> None:
    """Updates action column."""
    result = update_subclause_status(
        _SUBCLAUSE_TABLE, "§3.1", "Reviewed",
        action="Deemed not implementable",
    )
    assert "Deemed not implementable" in result


def test_update_subclause_status_exits_on_missing_label() -> None:
    """Exits when label is not found in table."""
    with pytest.raises(SystemExit):
        update_subclause_status(_SUBCLAUSE_TABLE, "§99.1", "Reviewed")


def test_update_subclause_status_preserves_other_rows() -> None:
    """Other rows are not modified."""
    result = update_subclause_status(_SUBCLAUSE_TABLE, "§3.1", "Reviewed")
    assert "| §3.2 | Design | Unreviewed | |" in result


def test_update_subclause_status_links_action_to_commit() -> None:
    """Wraps action in a markdown link when commit_url is provided."""
    result = update_subclause_status(
        _SUBCLAUSE_TABLE, "§3.1", "Reviewed",
        action="Deemed not implementable",
        commit_url="https://github.com/org/repo/commit/abc123",
    )
    assert "[Deemed not implementable](https://github.com/org/repo/commit/abc123)" in result


def test_update_subclause_status_no_link_without_url() -> None:
    """Action is plain text when commit_url is empty."""
    result = update_subclause_status(
        _SUBCLAUSE_TABLE, "§3.1", "Reviewed",
        action="Deemed not implementable",
    )
    assert "| Deemed not implementable |" in result


# ---- parse_subclause_rows --------------------------------------------------

_REVIEWED_TABLE = (
    "| Label | Title | Status | Action |\n"
    "|-------|-------|--------|--------|\n"
    "| §3.1 | General | Reviewed | Deemed not implementable |\n"
    "| §3.2 | Design | Unreviewed | |\n"
)


def test_parse_subclause_rows_extracts_status() -> None:
    """Parses the status column from a reviewed row."""
    rows = parse_subclause_rows(_REVIEWED_TABLE)
    assert rows["§3.1"][1] == "Reviewed"


def test_parse_subclause_rows_extracts_action() -> None:
    """Parses the action column from a reviewed row."""
    rows = parse_subclause_rows(_REVIEWED_TABLE)
    assert rows["§3.1"][2] == "Deemed not implementable"


def test_parse_subclause_rows_extracts_title() -> None:
    """Parses the title column."""
    rows = parse_subclause_rows(_REVIEWED_TABLE)
    assert rows["§3.1"][0] == "General"


def test_parse_subclause_rows_empty_action() -> None:
    """Empty action is parsed as empty string."""
    rows = parse_subclause_rows(_REVIEWED_TABLE)
    assert rows["§3.2"][2] == ""


# ---- sync_subclause_table --------------------------------------------------


def test_sync_subclause_table_preserves_status() -> None:
    """Existing reviewed rows keep their status and action."""
    result = sync_subclause_table(
        _REVIEWED_TABLE, {"3.1": "General", "3.2": "Design"},
    )
    assert "| §3.1 | General | Reviewed | Deemed not implementable |" in result


def test_sync_subclause_table_adds_new() -> None:
    """New subclauses are added as Unreviewed."""
    result = sync_subclause_table(
        _REVIEWED_TABLE, {"3.1": "General", "3.2": "Design", "3.3": "Modules"},
    )
    assert "| §3.3 | Modules | Unreviewed | |" in result


# ---- create_issue -----------------------------------------------------------


def test_find_issue_by_title_found() -> None:
    """Returns issue number when title matches."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='[{"number": 42, "title": "My Issue"}]',
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        assert find_issue_by_title("org", "repo", "My Issue") == 42


def test_find_issue_by_title_not_found() -> None:
    """Returns None when no title matches."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout='[]',
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        assert find_issue_by_title("org", "repo", "Missing") is None


def test_find_issue_by_title_failure() -> None:
    """Returns None on API failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        assert find_issue_by_title("org", "repo", "X") is None


def test_find_issue_by_title_partial_match() -> None:
    """Returns None when title only partially matches."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='[{"number": 42, "title": "My Issue Extended"}]',
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        assert find_issue_by_title("org", "repo", "My Issue") is None


def test_create_issue_returns_number(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """create_issue returns the issue number from the API response."""
    mock_result = subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout='{"number": 42}', stderr="",
    )
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    assert create_issue("org", "repo", "title", "body") == 42


def test_create_issue_exits_on_failure(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """create_issue exits when the API call fails."""
    mock_result = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    monkeypatch.setattr(subprocess, "run", lambda *_a, **_kw: mock_result)
    with pytest.raises(SystemExit):
        create_issue("org", "repo", "title", "body")


def _create_issue_payload(
    monkeypatch: pytest.MonkeyPatch, **kwargs: Any,
) -> dict[str, Any]:
    """Call create_issue with stubbed subprocess and return the parsed payload."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=0, stdout='{"number": 7}', stderr="",
    )
    captured: list[str] = []

    def stub_run(*_a: Any, **kw: Any) -> subprocess.CompletedProcess[str]:
        captured.append(kw.get("input", ""))
        return cp

    monkeypatch.setattr(subprocess, "run", stub_run)
    create_issue("org", "repo", "title", "body", **kwargs)
    parsed: dict[str, Any] = json.loads(captured[0])
    return parsed


def test_create_issue_includes_labels(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """create_issue includes labels in the payload when provided."""
    assert _create_issue_payload(
        monkeypatch, labels=["IEEE 1800-2023"],
    )["labels"] == ["IEEE 1800-2023"]


def test_create_issue_omits_labels_when_none(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    """create_issue omits labels key from payload when None."""
    assert "labels" not in _create_issue_payload(monkeypatch)


# --- add_labels ---


def test_add_labels_calls_correct_endpoint() -> None:
    """Calls gh api with the correct labels endpoint."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp) as mock_run:
        add_labels("org", "repo", 42, ["IEEE 1800-2023"])
    assert "repos/org/repo/issues/42/labels" in mock_run.call_args[0][0]


def test_add_labels_sends_labels_payload() -> None:
    """Sends the labels list as a JSON payload."""
    cp = subprocess.CompletedProcess(args=[], returncode=0, stdout="")
    with patch("lib.python.github.subprocess.run", return_value=cp) as mock_run:
        add_labels("org", "repo", 42, ["IEEE 1800-2023", "bug"])
    payload = json.loads(mock_run.call_args.kwargs["input"])
    assert payload == {"labels": ["IEEE 1800-2023", "bug"]}


def test_add_labels_failure() -> None:
    """SystemExit raised on add_labels failure."""
    cp = subprocess.CompletedProcess(
        args=[], returncode=1, stdout="", stderr="err",
    )
    with patch("lib.python.github.subprocess.run", return_value=cp):
        with pytest.raises(SystemExit):
            add_labels("org", "repo", 1, ["label"])
