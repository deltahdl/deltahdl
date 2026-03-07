"""Unit tests for GitHub integration functions in classify_test."""

import subprocess
import sys
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest


# ---- _parse_args (issue/organization/repo) ---------------------------------


_ALL_FLAGS = ["prog", "--file", "f.cpp", "--output-dir", "/out",
              "--lrm", "/lrm.txt", "--test", "T",
              "--issue", "42", "--organization", "myorg",
              "--repo", "myrepo", "--max-lines", "1000"]


def test_parse_args_issue(monkeypatch, ct):
    """Parses --issue flag as integer."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().issue == 42


def test_parse_args_issue_required(monkeypatch, ct):
    """Exits when --issue is missing."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T",
         "--organization", "myorg", "--repo", "myrepo",
         "--max-lines", "1000"],
    )
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_organization(monkeypatch, ct):
    """Parses --organization flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().organization == "myorg"


def test_parse_args_organization_required(monkeypatch, ct):
    """Exits when --organization is missing."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T",
         "--issue", "42", "--repo", "myrepo",
         "--max-lines", "1000"],
    )
    with pytest.raises(SystemExit):
        _parse_args()


def test_parse_args_repo(monkeypatch, ct):
    """Parses --repo flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().repo == "myrepo"


def test_parse_args_repo_required(monkeypatch, ct):
    """Exits when --repo is missing."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T",
         "--issue", "42", "--organization", "myorg",
         "--max-lines", "1000"],
    )
    with pytest.raises(SystemExit):
        _parse_args()


# ---- tick_checkbox ---------------------------------------------------------


def test_tick_checkbox_ticks_unchecked(ct_github):
    """Replaces '- [ ] Name' with '- [x] Name'."""
    body = "- [ ] Alpha\n- [ ] Beta\n"
    assert "- [x] Alpha" in ct_github.tick_checkbox(body, "Alpha")


def test_tick_checkbox_leaves_others_unchecked(ct_github):
    """Does not tick other checkboxes."""
    body = "- [ ] Alpha\n- [ ] Beta\n"
    result = ct_github.tick_checkbox(body, "Alpha")
    assert "- [ ] Beta" in result


def test_tick_checkbox_already_checked(ct_github):
    """No change when checkbox is already checked."""
    body = "- [x] Alpha\n- [ ] Beta\n"
    assert ct_github.tick_checkbox(body, "Alpha") == body


def test_tick_checkbox_link_ticks_unchecked(ct_github):
    """Ticks a checkbox when the name is a markdown link."""
    body = "- [ ] [Alpha](https://example.com/1)\n- [ ] Beta\n"
    assert "- [x] [Alpha]" in ct_github.tick_checkbox(body, "Alpha")


def test_tick_checkbox_link_leaves_others_unchecked(ct_github):
    """Does not tick other checkboxes when ticking a link."""
    body = "- [ ] [Alpha](https://example.com/1)\n- [ ] Beta\n"
    assert "- [ ] Beta" in ct_github.tick_checkbox(body, "Alpha")


def test_tick_checkbox_link_preserves_url(ct_github):
    """Preserves the markdown link URL after ticking."""
    body = "- [ ] [Alpha](https://example.com/1)\n"
    assert "(https://example.com/1)" in ct_github.tick_checkbox(body, "Alpha")


def test_tick_checkbox_link_already_checked(ct_github):
    """No change when a linked checkbox is already checked."""
    body = "- [x] [Alpha](https://example.com/1)\n"
    assert ct_github.tick_checkbox(body, "Alpha") == body


def test_tick_checkbox_not_found_exits(ct_github):
    """Exits when test name is not found in any checkbox."""
    with pytest.raises(SystemExit):
        ct_github.tick_checkbox("- [ ] Other\n", "Missing")


# ---- remove_checkbox -------------------------------------------------------


def test_remove_checkbox_removes_unchecked(ct_github):
    """Removes an unchecked checkbox line."""
    body = "- [ ] Alpha\n- [ ] Beta\n"
    assert ct_github.remove_checkbox(body, "Alpha") == "- [ ] Beta\n"


def test_remove_checkbox_removes_checked(ct_github):
    """Removes a checked checkbox line."""
    body = "- [x] Alpha\n- [ ] Beta\n"
    assert ct_github.remove_checkbox(body, "Alpha") == "- [ ] Beta\n"


def test_remove_checkbox_removes_linked_unchecked(ct_github):
    """Removes a linked unchecked checkbox line."""
    body = "- [ ] [Alpha](https://example.com/1)\n- [ ] Beta\n"
    assert ct_github.remove_checkbox(body, "Alpha") == "- [ ] Beta\n"


def test_remove_checkbox_removes_linked_checked(ct_github):
    """Removes a linked checked checkbox line."""
    body = "- [x] [Alpha](https://example.com/1)\n- [ ] Beta\n"
    assert ct_github.remove_checkbox(body, "Alpha") == "- [ ] Beta\n"


def test_remove_checkbox_preserves_others(ct_github):
    """Other checkboxes are untouched after removal."""
    body = "- [ ] Alpha\n- [ ] Beta\n- [ ] Gamma\n"
    assert "- [ ] Beta\n- [ ] Gamma\n" in ct_github.remove_checkbox(body, "Alpha")


def test_remove_checkbox_not_found_raises(ct_github):
    """Raises ValueError when test name is not found in any checkbox."""
    with pytest.raises(ValueError, match="not found"):
        ct_github.remove_checkbox("- [ ] Other\n", "Missing")


# ---- fetch_issue_body ------------------------------------------------------


def test_fetch_issue_body_returns_body(monkeypatch, ct_github):
    """Returns the issue body from gh api."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "- [ ] T\n"
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert ct_github.fetch_issue_body("org", "repo", 42) == "- [ ] T\n"


def test_fetch_issue_body_failure_exits(monkeypatch, ct_github):
    """Exits on non-zero return code."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "not found"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    with pytest.raises(SystemExit):
        ct_github.fetch_issue_body("org", "repo", 42)


# ---- update_issue_body -----------------------------------------------------


def _capture_update_cmd(monkeypatch, ct_helpers, ct_github):
    """Run update_issue_body and return captured subprocess command."""
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    ct_github.update_issue_body("myorg", "myrepo", 42, "new body")
    # Flatten: stub_subprocess_success stores [list, ...]; return flat.
    return [arg for cmd in captured for arg in cmd]


def test_update_issue_body_calls_gh(monkeypatch, ct_helpers, ct_github):
    """Calls gh api for issue update."""
    cmd = _capture_update_cmd(monkeypatch, ct_helpers, ct_github)
    assert cmd[0] == "gh"


def test_update_issue_body_uses_patch(monkeypatch, ct_helpers, ct_github):
    """Uses PATCH method."""
    cmd = _capture_update_cmd(monkeypatch, ct_helpers, ct_github)
    idx = cmd.index("-X")
    assert cmd[idx + 1] == "PATCH"


def test_update_issue_body_targets_correct_endpoint(monkeypatch, ct_helpers, ct_github):
    """Targets repos/org/repo/issues/N endpoint."""
    cmd = _capture_update_cmd(monkeypatch, ct_helpers, ct_github)
    assert "repos/myorg/myrepo/issues/42" in " ".join(cmd)


def test_update_issue_body_failure_exits(monkeypatch, ct_helpers, ct_github):
    """Exits on non-zero return code."""
    ct_helpers.stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        ct_github.update_issue_body("org", "repo", 42, "body")


# ---- _validate_issue_args --------------------------------------------------


def _issue_args(**overrides):
    """Build a SimpleNamespace with issue-related args."""
    defaults = {"issue": None, "organization": None, "repo": None}
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


def test_validate_issue_args_no_issue(ct_github):
    """No error when --issue is not provided."""
    assert getattr(ct_github, "_validate_issue_args")(_issue_args()) is None


def test_validate_issue_args_all_present(ct_github):
    """No error when all three args are present."""
    args = _issue_args(issue=42, organization="org", repo="repo")
    assert getattr(ct_github, "_validate_issue_args")(args) is None


def test_validate_issue_args_missing_organization(ct_github):
    """Exits when --issue is set but --organization is missing."""
    with pytest.raises(SystemExit):
        getattr(ct_github, "_validate_issue_args")(_issue_args(issue=42, repo="repo"))


def test_validate_issue_args_missing_repo(ct_github):
    """Exits when --issue is set but --repo is missing."""
    with pytest.raises(SystemExit):
        getattr(ct_github, "_validate_issue_args")(_issue_args(issue=42, organization="org"))


# ---- maybe_tick_issue_checkbox ---------------------------------------------


def test_maybe_tick_does_fetch_and_update(monkeypatch, ct_github, ct_helpers):
    """Fetches body, ticks checkbox, and updates."""
    _tb = ct_helpers.make_test_block
    updated = []
    monkeypatch.setattr(
        ct_github, "fetch_issue_body",
        lambda org, repo, issue: "- [ ] T\n",
    )
    monkeypatch.setattr(
        ct_github, "update_issue_body",
        lambda org, repo, issue, body: updated.append(body),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=42, organization="org", repo="repo")
    ct_github.maybe_tick_issue_checkbox(args, [t])
    assert "- [x] T" in updated[0]


def test_maybe_tick_passes_correct_org(monkeypatch, ct_github, ct_helpers):
    """Passes organization to fetch and update."""
    _tb = ct_helpers.make_test_block
    orgs = []
    monkeypatch.setattr(
        ct_github, "fetch_issue_body",
        lambda org, repo, issue: (orgs.append(org), "- [ ] T\n")[1],
    )
    monkeypatch.setattr(
        ct_github, "update_issue_body",
        lambda org, repo, issue, body: orgs.append(org),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=42, organization="myorg", repo="repo")
    ct_github.maybe_tick_issue_checkbox(args, [t])
    assert all(o == "myorg" for o in orgs)


def test_maybe_tick_passes_correct_issue(monkeypatch, ct_github, ct_helpers):
    """Passes issue number to fetch and update."""
    _tb = ct_helpers.make_test_block
    issues = []
    monkeypatch.setattr(
        ct_github, "fetch_issue_body",
        lambda org, repo, issue: (issues.append(issue), "- [ ] T\n")[1],
    )
    monkeypatch.setattr(
        ct_github, "update_issue_body",
        lambda org, repo, issue, body: issues.append(issue),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=99, organization="org", repo="repo")
    ct_github.maybe_tick_issue_checkbox(args, [t])
    assert all(i == 99 for i in issues)
