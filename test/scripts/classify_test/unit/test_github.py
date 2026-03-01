"""Unit tests for GitHub integration functions in classify_test."""

import subprocess
import sys
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

import classify_test
from classify_test._github import (
    _validate_issue_args,
    fetch_issue_body,
    maybe_tick_issue_checkbox,
    tick_checkbox,
    update_issue_body,
)
from helpers import (
    make_test_block as _tb,
    stub_subprocess_failure,
    stub_subprocess_success,
)

_parse_args = getattr(classify_test, "_parse_args")


# ---- _parse_args (issue/organization/repo) ---------------------------------


_ALL_FLAGS = ["prog", "--file", "f.cpp", "--output-dir", "/out",
              "--lrm", "/lrm.txt", "--test", "T",
              "--issue", "42", "--organization", "myorg",
              "--repo", "myrepo"]


def test_parse_args_issue(monkeypatch):
    """Parses --issue flag as integer."""
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().issue == 42


def test_parse_args_issue_required(monkeypatch):
    """Exits when --issue is missing."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T",
         "--organization", "myorg", "--repo", "myrepo"],
    )
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_organization(monkeypatch):
    """Parses --organization flag."""
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().organization == "myorg"


def test_parse_args_organization_required(monkeypatch):
    """Exits when --organization is missing."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T",
         "--issue", "42", "--repo", "myrepo"],
    )
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_repo(monkeypatch):
    """Parses --repo flag."""
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().repo == "myrepo"


def test_parse_args_repo_required(monkeypatch):
    """Exits when --repo is missing."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T",
         "--issue", "42", "--organization", "myorg"],
    )
    with pytest.raises(SystemExit):
        _parse_args()


# ---- tick_checkbox ---------------------------------------------------------


def test_tick_checkbox_ticks_unchecked():
    """Replaces '- [ ] Name' with '- [x] Name'."""
    body = "- [ ] Alpha\n- [ ] Beta\n"
    assert "- [x] Alpha" in tick_checkbox(body, "Alpha")


def test_tick_checkbox_leaves_others_unchecked():
    """Does not tick other checkboxes."""
    body = "- [ ] Alpha\n- [ ] Beta\n"
    result = tick_checkbox(body, "Alpha")
    assert "- [ ] Beta" in result


def test_tick_checkbox_already_checked():
    """No change when checkbox is already checked."""
    body = "- [x] Alpha\n- [ ] Beta\n"
    assert tick_checkbox(body, "Alpha") == body


def test_tick_checkbox_link_ticks_unchecked():
    """Ticks a checkbox when the name is a markdown link."""
    body = "- [ ] [Alpha](https://example.com/1)\n- [ ] Beta\n"
    assert "- [x] [Alpha]" in tick_checkbox(body, "Alpha")


def test_tick_checkbox_link_leaves_others_unchecked():
    """Does not tick other checkboxes when ticking a link."""
    body = "- [ ] [Alpha](https://example.com/1)\n- [ ] Beta\n"
    assert "- [ ] Beta" in tick_checkbox(body, "Alpha")


def test_tick_checkbox_link_preserves_url():
    """Preserves the markdown link URL after ticking."""
    body = "- [ ] [Alpha](https://example.com/1)\n"
    assert "(https://example.com/1)" in tick_checkbox(body, "Alpha")


def test_tick_checkbox_link_already_checked():
    """No change when a linked checkbox is already checked."""
    body = "- [x] [Alpha](https://example.com/1)\n"
    assert tick_checkbox(body, "Alpha") == body


def test_tick_checkbox_not_found_exits():
    """Exits when test name is not found in any checkbox."""
    with pytest.raises(SystemExit):
        tick_checkbox("- [ ] Other\n", "Missing")


# ---- fetch_issue_body ------------------------------------------------------


def test_fetch_issue_body_returns_body(monkeypatch):
    """Returns the issue body from gh api."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "- [ ] T\n"
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert fetch_issue_body("org", "repo", 42) == "- [ ] T\n"


def test_fetch_issue_body_failure_exits(monkeypatch):
    """Exits on non-zero return code."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "not found"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    with pytest.raises(SystemExit):
        fetch_issue_body("org", "repo", 42)


# ---- update_issue_body -----------------------------------------------------


def _capture_update_cmd(monkeypatch):
    """Run update_issue_body and return captured subprocess command."""
    captured = stub_subprocess_success(monkeypatch)
    update_issue_body("myorg", "myrepo", 42, "new body")
    # Flatten: stub_subprocess_success stores [list, ...]; return flat.
    return [arg for cmd in captured for arg in cmd]


def test_update_issue_body_calls_gh(monkeypatch):
    """Calls gh api for issue update."""
    cmd = _capture_update_cmd(monkeypatch)
    assert cmd[0] == "gh"


def test_update_issue_body_uses_patch(monkeypatch):
    """Uses PATCH method."""
    cmd = _capture_update_cmd(monkeypatch)
    idx = cmd.index("-X")
    assert cmd[idx + 1] == "PATCH"


def test_update_issue_body_targets_correct_endpoint(monkeypatch):
    """Targets repos/org/repo/issues/N endpoint."""
    cmd = _capture_update_cmd(monkeypatch)
    assert "repos/myorg/myrepo/issues/42" in " ".join(cmd)


def test_update_issue_body_failure_exits(monkeypatch):
    """Exits on non-zero return code."""
    stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        update_issue_body("org", "repo", 42, "body")


# ---- _validate_issue_args --------------------------------------------------


def _issue_args(**overrides):
    """Build a SimpleNamespace with issue-related args."""
    defaults = {"issue": None, "organization": None, "repo": None}
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


def test_validate_issue_args_no_issue():
    """No error when --issue is not provided."""
    assert _validate_issue_args(_issue_args()) is None


def test_validate_issue_args_all_present():
    """No error when all three args are present."""
    args = _issue_args(issue=42, organization="org", repo="repo")
    assert _validate_issue_args(args) is None


def test_validate_issue_args_missing_organization():
    """Exits when --issue is set but --organization is missing."""
    with pytest.raises(SystemExit):
        _validate_issue_args(_issue_args(issue=42, repo="repo"))


def test_validate_issue_args_missing_repo():
    """Exits when --issue is set but --repo is missing."""
    with pytest.raises(SystemExit):
        _validate_issue_args(_issue_args(issue=42, organization="org"))


# ---- maybe_tick_issue_checkbox ---------------------------------------------


def test_maybe_tick_does_fetch_and_update(monkeypatch):
    """Fetches body, ticks checkbox, and updates."""
    updated = []
    monkeypatch.setattr(
        "classify_test._github.fetch_issue_body",
        lambda org, repo, issue: "- [ ] T\n",
    )
    monkeypatch.setattr(
        "classify_test._github.update_issue_body",
        lambda org, repo, issue, body: updated.append(body),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=42, organization="org", repo="repo")
    maybe_tick_issue_checkbox(args, [t])
    assert "- [x] T" in updated[0]


def test_maybe_tick_passes_correct_org(monkeypatch):
    """Passes organization to fetch and update."""
    orgs = []
    monkeypatch.setattr(
        "classify_test._github.fetch_issue_body",
        lambda org, repo, issue: (orgs.append(org), "- [ ] T\n")[1],
    )
    monkeypatch.setattr(
        "classify_test._github.update_issue_body",
        lambda org, repo, issue, body: orgs.append(org),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=42, organization="myorg", repo="repo")
    maybe_tick_issue_checkbox(args, [t])
    assert all(o == "myorg" for o in orgs)


def test_maybe_tick_passes_correct_issue(monkeypatch):
    """Passes issue number to fetch and update."""
    issues = []
    monkeypatch.setattr(
        "classify_test._github.fetch_issue_body",
        lambda org, repo, issue: (issues.append(issue), "- [ ] T\n")[1],
    )
    monkeypatch.setattr(
        "classify_test._github.update_issue_body",
        lambda org, repo, issue, body: issues.append(issue),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=99, organization="org", repo="repo")
    maybe_tick_issue_checkbox(args, [t])
    assert all(i == 99 for i in issues)
