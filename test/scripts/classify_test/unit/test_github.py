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


def test_parse_args_issue_defaults_to_none(monkeypatch, ct):
    """--issue defaults to None when omitted."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T",
         "--organization", "myorg", "--repo", "myrepo",
         "--max-lines", "1000"],
    )
    assert _parse_args().issue is None


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


# ---- update_test_status ----------------------------------------------------


def test_update_test_status_sets_status(ct_github):
    """Updates status from Unreviewed to reviewed."""
    body = "| Alpha | Unreviewed | |\n| Beta | Unreviewed | |\n"
    result = ct_github.update_test_status(
        body, "Alpha", "Reviewed",
    )
    assert "| Alpha | Reviewed | |" in result


def test_update_test_status_leaves_others(ct_github):
    """Does not change other rows."""
    body = "| Alpha | Unreviewed | |\n| Beta | Unreviewed | |\n"
    result = ct_github.update_test_status(
        body, "Alpha", "Reviewed",
    )
    assert "| Beta | Unreviewed | |" in result


def test_update_test_status_already_set(ct_github):
    """Idempotent when same status is set again."""
    body = "| Alpha | Reviewed | Kept in the same file |\n"
    result = ct_github.update_test_status(
        body, "Alpha", "Reviewed",
    )
    assert "| Alpha | Reviewed | |" in result


def test_update_test_status_not_found_exits(ct_github):
    """Exits when test name is not found in any row."""
    with pytest.raises(SystemExit):
        ct_github.update_test_status(
            "| Other | Unreviewed | |\n", "Missing",
            "Reviewed",
        )


def test_update_test_status_with_remark(ct_github):
    """Sets remark in the Action column."""
    body = "| Alpha | Unreviewed | |\n"
    result = ct_github.update_test_status(
        body, "Alpha", "Reviewed",
        remark="Moved to target.cpp",
    )
    assert (
        "| Alpha | Reviewed"
        " | Moved to target.cpp |"
    ) in result


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


# ---- maybe_update_issue_status ---------------------------------------------


def _setup_maybe_update(
    monkeypatch, ct_github, ct_helpers, *,
    source_is_target, target_filenames=None,
):
    """Run maybe_update_issue_status and return captured body updates."""
    _tb = ct_helpers.make_test_block
    updated = []
    monkeypatch.setattr(
        ct_github, "fetch_issue_body",
        lambda org, repo, issue: "| T | Unreviewed | |\n",
    )
    monkeypatch.setattr(
        ct_github, "update_issue_body",
        lambda org, repo, issue, body: updated.append(body),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=42, organization="org", repo="repo")
    ct_github.maybe_update_issue_status(
        args, [t],
        source_is_target=source_is_target,
        target_filenames=target_filenames,
    )
    return updated


def test_maybe_update_skips_when_no_issue(ct_github):
    """Skips update entirely when args.issue is None."""
    args = _issue_args(issue=None, organization=None, repo=None)
    # Should return without calling fetch_issue_body or update_issue_body.
    # If it tried, it would fail because those functions are not stubbed.
    ct_github.maybe_update_issue_status(
        args, [], source_is_target=False,
    )


def test_maybe_update_kept(monkeypatch, ct_github, ct_helpers):
    """Sets status to 'Reviewed' and action to 'Kept in the same file'."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=True,
        target_filenames={"T": "test_parser_clause_06_01.cpp"},
    )
    assert "| T | Reviewed | Kept in the same file |" in updated[0]


def test_maybe_update_moved(monkeypatch, ct_github, ct_helpers):
    """Sets status and action with target filename when moved."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=False,
        target_filenames={"T": "test_parser_clause_06_01.cpp"},
    )
    assert (
        "| T | Reviewed"
        " | Moved to test_parser_clause_06_01.cpp |"
    ) in updated[0]


def test_maybe_update_moved_no_filenames(monkeypatch, ct_github, ct_helpers):
    """Sets empty action when moved but target_filenames is None."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers,
        source_is_target=False, target_filenames=None,
    )
    assert "| T | Reviewed | |" in updated[0]


def test_maybe_update_moved_empty_fname(monkeypatch, ct_github, ct_helpers):
    """Sets empty action when target_filenames maps to empty string."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers,
        source_is_target=False, target_filenames={"T": ""},
    )
    assert "| T | Reviewed | |" in updated[0]


def test_maybe_update_passes_correct_org(monkeypatch, ct_github, ct_helpers):
    """Passes organization to fetch and update."""
    _tb = ct_helpers.make_test_block
    orgs = []
    monkeypatch.setattr(
        ct_github, "fetch_issue_body",
        lambda org, repo, issue: (orgs.append(org), "| T | Unreviewed | |\n")[1],
    )
    monkeypatch.setattr(
        ct_github, "update_issue_body",
        lambda org, repo, issue, body: orgs.append(org),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=42, organization="myorg", repo="repo")
    ct_github.maybe_update_issue_status(args, [t], source_is_target=True)
    assert all(o == "myorg" for o in orgs)


def test_maybe_update_passes_correct_issue(monkeypatch, ct_github, ct_helpers):
    """Passes issue number to fetch and update."""
    _tb = ct_helpers.make_test_block
    issues = []
    monkeypatch.setattr(
        ct_github, "fetch_issue_body",
        lambda org, repo, issue: (issues.append(issue), "| T | Unreviewed | |\n")[1],
    )
    monkeypatch.setattr(
        ct_github, "update_issue_body",
        lambda org, repo, issue, body: issues.append(issue),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=99, organization="org", repo="repo")
    ct_github.maybe_update_issue_status(args, [t], source_is_target=True)
    assert all(i == 99 for i in issues)


# ---- maybe_update_issue_status: renamed tests ------------------------------


def _setup_renamed_update(
    monkeypatch, ct_github, ct_helpers, *,
    source_is_target, target_filenames=None,
):
    """Run maybe_update with a renamed test and return captured body."""
    _tb = ct_helpers.make_test_block
    updated = []
    monkeypatch.setattr(
        ct_github, "fetch_issue_body",
        lambda org, repo, issue: "| OldName | Unreviewed | |\n",
    )
    monkeypatch.setattr(
        ct_github, "update_issue_body",
        lambda org, repo, issue, body: updated.append(body),
    )
    t = _tb("NewName", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    t.original_test_name = "OldName"
    args = _issue_args(issue=42, organization="org", repo="repo")
    ct_github.maybe_update_issue_status(
        args, [t],
        source_is_target=source_is_target,
        target_filenames=target_filenames,
    )
    return updated


def test_maybe_update_renamed_uses_original_name(
    monkeypatch, ct_github, ct_helpers,
):
    """Looks up the row by original_test_name, not the renamed name."""
    updated = _setup_renamed_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=True,
    )
    assert "| OldName |" in updated[0]


def test_maybe_update_renamed_kept_uses_but(
    monkeypatch, ct_github, ct_helpers,
):
    """Remark uses 'but' when kept and renamed."""
    updated = _setup_renamed_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=True,
    )
    assert "Kept in the same file but renamed to NewName" in updated[0]


def test_maybe_update_renamed_and_moved_uses_and(
    monkeypatch, ct_github, ct_helpers,
):
    """Remark uses 'and' when moved and renamed."""
    updated = _setup_renamed_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=False,
        target_filenames={"NewName": "test_parser_clause_06_01.cpp"},
    )
    expected = ("Moved to test_parser_clause_06_01.cpp"
                " and renamed to NewName")
    assert expected in updated[0]


def test_maybe_update_same_name_no_rename_remark(
    monkeypatch, ct_github, ct_helpers,
):
    """No rename remark when original_test_name equals test_name."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=True,
    )
    assert "renamed" not in updated[0]
