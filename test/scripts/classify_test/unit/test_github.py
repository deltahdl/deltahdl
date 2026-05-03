"""Unit tests for GitHub integration functions in classify_test."""

import subprocess
import sys
from types import ModuleType, SimpleNamespace
from typing import Any
from unittest.mock import MagicMock

import pytest


# ---- _parse_args (issue/organization/repo) ---------------------------------


_ALL_FLAGS = ["prog", "--file", "f.cpp", "--output-dir", "/out",
              "--lrm", "/lrm.txt", "--suite", "S", "--test", "T",
              "--issue", "42", "--organization", "myorg",
              "--repo", "myrepo", "--max-lines", "1000"]


def test_parse_args_issue(
    monkeypatch: pytest.MonkeyPatch, ct: ModuleType,
) -> None:
    """Parses --issue flag as integer."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().issue == 42


def test_parse_args_issue_defaults_to_none(
    monkeypatch: pytest.MonkeyPatch, ct: ModuleType,
) -> None:
    """--issue defaults to None when omitted."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--suite", "S", "--test", "T",
         "--organization", "myorg", "--repo", "myrepo",
         "--max-lines", "1000"],
    )
    assert _parse_args().issue is None


def test_parse_args_organization(
    monkeypatch: pytest.MonkeyPatch, ct: ModuleType,
) -> None:
    """Parses --organization flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().organization == "myorg"


def test_parse_args_organization_required(
    monkeypatch: pytest.MonkeyPatch, ct: ModuleType,
) -> None:
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


def test_parse_args_repo(
    monkeypatch: pytest.MonkeyPatch, ct: ModuleType,
) -> None:
    """Parses --repo flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().repo == "myrepo"


def test_parse_args_repo_required(
    monkeypatch: pytest.MonkeyPatch, ct: ModuleType,
) -> None:
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


def test_parse_args_against(
    monkeypatch: pytest.MonkeyPatch, ct: ModuleType,
) -> None:
    """Parses --against flag."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(
        sys, "argv", [*_ALL_FLAGS, "--against", "23.2.1"],
    )
    assert _parse_args().against == "23.2.1"


def test_parse_args_against_default(
    monkeypatch: pytest.MonkeyPatch, ct: ModuleType,
) -> None:
    """--against defaults to empty string."""
    _parse_args = getattr(ct, "_parse_args")
    monkeypatch.setattr(sys, "argv", _ALL_FLAGS)
    assert _parse_args().against == ""


# ---- update_test_status ----------------------------------------------------


def test_update_test_status_sets_status(ct_github: ModuleType) -> None:
    """Updates status from Unreviewed to reviewed."""
    body = "| S | Alpha | Unreviewed | |\n| S | Beta | Unreviewed | |\n"
    result = ct_github.update_test_status(
        body, "Alpha", "Reviewed",
    )
    assert "| S | Alpha | Reviewed | |" in result


def test_update_test_status_leaves_others(ct_github: ModuleType) -> None:
    """Does not change other rows."""
    body = "| S | Alpha | Unreviewed | |\n| S | Beta | Unreviewed | |\n"
    result = ct_github.update_test_status(
        body, "Alpha", "Reviewed",
    )
    assert "| S | Beta | Unreviewed | |" in result


def test_update_test_status_already_set(ct_github: ModuleType) -> None:
    """Idempotent when same status is set again."""
    body = "| S | Alpha | Reviewed | Kept |\n"
    result = ct_github.update_test_status(
        body, "Alpha", "Reviewed",
    )
    assert "| S | Alpha | Reviewed | |" in result


def test_update_test_status_not_found_exits(ct_github: ModuleType) -> None:
    """Exits when test name is not found in any row."""
    with pytest.raises(SystemExit):
        ct_github.update_test_status(
            "| S | Other | Unreviewed | |\n", "Missing",
            "Reviewed",
        )


def test_update_test_status_with_remark(ct_github: ModuleType) -> None:
    """Sets remark in the Action column."""
    body = "| S | Alpha | Unreviewed | |\n"
    result = ct_github.update_test_status(
        body, "Alpha", "Reviewed",
        remark="Moved to target.cpp",
    )
    assert (
        "| S | Alpha | Reviewed"
        " | Moved to target.cpp |"
    ) in result


# ---- fetch_issue_body ------------------------------------------------------


def test_fetch_issue_body_returns_body(
    monkeypatch: pytest.MonkeyPatch, ct_github: ModuleType,
) -> None:
    """Returns the issue body from gh api."""
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = "- [ ] T\n"
    mock_result.stderr = ""
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    assert ct_github.fetch_issue_body("org", "repo", 42) == "- [ ] T\n"


def test_fetch_issue_body_failure_exits(
    monkeypatch: pytest.MonkeyPatch, ct_github: ModuleType,
) -> None:
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


def _capture_update_cmd(
    monkeypatch: pytest.MonkeyPatch,
    ct_helpers: ModuleType,
    ct_github: ModuleType,
) -> list[str]:
    """Run update_issue_body and return captured subprocess command."""
    captured = ct_helpers.stub_subprocess_success(monkeypatch)
    ct_github.update_issue_body("myorg", "myrepo", 42, "new body")
    # Flatten: stub_subprocess_success stores [list, ...]; return flat.
    return [arg for cmd in captured for arg in cmd]


def test_update_issue_body_calls_gh(
    monkeypatch: pytest.MonkeyPatch,
    ct_helpers: ModuleType,
    ct_github: ModuleType,
) -> None:
    """Calls gh api for issue update."""
    cmd = _capture_update_cmd(monkeypatch, ct_helpers, ct_github)
    assert cmd[0] == "gh"


def test_update_issue_body_uses_patch(
    monkeypatch: pytest.MonkeyPatch,
    ct_helpers: ModuleType,
    ct_github: ModuleType,
) -> None:
    """Uses PATCH method."""
    cmd = _capture_update_cmd(monkeypatch, ct_helpers, ct_github)
    idx = cmd.index("-X")
    assert cmd[idx + 1] == "PATCH"


def test_update_issue_body_targets_correct_endpoint(
    monkeypatch: pytest.MonkeyPatch,
    ct_helpers: ModuleType,
    ct_github: ModuleType,
) -> None:
    """Targets repos/org/repo/issues/N endpoint."""
    cmd = _capture_update_cmd(monkeypatch, ct_helpers, ct_github)
    assert "repos/myorg/myrepo/issues/42" in " ".join(cmd)


def test_update_issue_body_failure_exits(
    monkeypatch: pytest.MonkeyPatch,
    ct_helpers: ModuleType,
    ct_github: ModuleType,
) -> None:
    """Exits on non-zero return code."""
    ct_helpers.stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        ct_github.update_issue_body("org", "repo", 42, "body")


# ---- _validate_issue_args --------------------------------------------------


def _issue_args(**overrides: Any) -> SimpleNamespace:
    """Build a SimpleNamespace with issue-related args."""
    defaults: dict[str, Any] = {
        "issue": None, "organization": None, "repo": None,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


def test_validate_issue_args_no_issue(ct_github: ModuleType) -> None:
    """No error when --issue is not provided."""
    assert getattr(ct_github, "_validate_issue_args")(_issue_args()) is None


def test_validate_issue_args_all_present(ct_github: ModuleType) -> None:
    """No error when all three args are present."""
    args = _issue_args(issue=42, organization="org", repo="repo")
    assert getattr(ct_github, "_validate_issue_args")(args) is None


def test_validate_issue_args_missing_organization(
    ct_github: ModuleType,
) -> None:
    """Exits when --issue is set but --organization is missing."""
    with pytest.raises(SystemExit):
        getattr(ct_github, "_validate_issue_args")(
            _issue_args(issue=42, repo="repo"),
        )


def test_validate_issue_args_missing_repo(ct_github: ModuleType) -> None:
    """Exits when --issue is set but --repo is missing."""
    with pytest.raises(SystemExit):
        getattr(ct_github, "_validate_issue_args")(
            _issue_args(issue=42, organization="org"),
        )


# ---- maybe_update_issue_status ---------------------------------------------


def _setup_maybe_update(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
    *,
    source_is_target: bool,
    **kw: Any,
) -> list[str]:
    """Run maybe_update_issue_status and return captured body updates."""
    _tb = ct_helpers.make_test_block
    updated: list[str] = []
    monkeypatch.setattr(
        ct_github, "fetch_issue_body",
        lambda org, repo, issue: "| S | T | Unreviewed | |\n",
    )
    monkeypatch.setattr(
        ct_github, "update_issue_body",
        lambda org, repo, issue, body: updated.append(body),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.classification.rationale = "r"
    args = _issue_args(issue=42, organization="org", repo="repo")
    ct_github.maybe_update_issue_status(
        args, [t],
        source_is_target=source_is_target,
        **kw,
    )
    return updated


def test_maybe_update_skips_when_no_issue(
    monkeypatch: pytest.MonkeyPatch, ct_github: ModuleType,
) -> None:
    """Skips update entirely when args.issue is None."""
    called: list[bool] = []

    def _fetch(_org: str, _repo: str, _issue: int) -> str:
        called.append(True)
        return ""

    monkeypatch.setattr(ct_github, "fetch_issue_body", _fetch)
    args = _issue_args(issue=None, organization=None, repo=None)
    ct_github.maybe_update_issue_status(
        args, [], source_is_target=False,
    )
    assert not called


def test_maybe_update_kept(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Sets status to 'Reviewed' and action to 'Kept in the same file without any changes'."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=True,
        target_filenames={"T": "test_parser_clause_06_01.cpp"},
    )
    assert "| S | T | Reviewed | Kept in the same file without any changes |" in updated[0]


def test_maybe_update_moved(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Sets status and action with target filename when moved."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=False,
        target_filenames={"T": "test_parser_clause_06_01.cpp"},
    )
    assert (
        "| S | T | Reviewed"
        " | Moved to test_parser_clause_06_01.cpp |"
    ) in updated[0]


def test_maybe_update_moved_no_filenames(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Sets empty action when moved but target_filenames is None."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers,
        source_is_target=False, target_filenames=None,
    )
    assert "| S | T | Reviewed | |" in updated[0]


def test_maybe_update_moved_empty_fname(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Sets empty action when target_filenames maps to empty string."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers,
        source_is_target=False, target_filenames={"T": ""},
    )
    assert "| S | T | Reviewed | |" in updated[0]


def test_maybe_update_passes_correct_org(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Passes organization to fetch and update."""
    _tb = ct_helpers.make_test_block
    orgs: list[str] = []

    def _fetch(org: str, _repo: str, _issue: int) -> str:
        orgs.append(org)
        return "| S | T | Unreviewed | |\n"

    def _update(org: str, _repo: str, _issue: int, _body: str) -> None:
        orgs.append(org)

    monkeypatch.setattr(ct_github, "fetch_issue_body", _fetch)
    monkeypatch.setattr(ct_github, "update_issue_body", _update)
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.classification.rationale = "r"
    args = _issue_args(issue=42, organization="myorg", repo="repo")
    ct_github.maybe_update_issue_status(args, [t], source_is_target=True)
    assert all(o == "myorg" for o in orgs)


def test_maybe_update_passes_correct_issue(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Passes issue number to fetch and update."""
    _tb = ct_helpers.make_test_block
    issues: list[int] = []

    def _fetch(_org: str, _repo: str, issue: int) -> str:
        issues.append(issue)
        return "| S | T | Unreviewed | |\n"

    def _update(_org: str, _repo: str, issue: int, _body: str) -> None:
        issues.append(issue)

    monkeypatch.setattr(ct_github, "fetch_issue_body", _fetch)
    monkeypatch.setattr(ct_github, "update_issue_body", _update)
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.classification.rationale = "r"
    args = _issue_args(issue=99, organization="org", repo="repo")
    ct_github.maybe_update_issue_status(args, [t], source_is_target=True)
    assert all(i == 99 for i in issues)


# ---- maybe_update_issue_status: renamed tests ------------------------------


def _setup_renamed_update(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
    *,
    source_is_target: bool,
    target_filenames: dict[str, str] | None = None,
) -> list[str]:
    """Run maybe_update with a renamed test and return captured body."""
    _tb = ct_helpers.make_test_block
    updated: list[str] = []
    monkeypatch.setattr(
        ct_github, "fetch_issue_body",
        lambda org, repo, issue: "| S | OldName | Unreviewed | |\n",
    )
    monkeypatch.setattr(
        ct_github, "update_issue_body",
        lambda org, repo, issue, body: updated.append(body),
    )
    t = _tb("NewName", prefix="test_parser_", clause="6.1")
    t.classification.rationale = "r"
    t.classification.original_test_name = "OldName"
    args = _issue_args(issue=42, organization="org", repo="repo")
    ct_github.maybe_update_issue_status(
        args, [t],
        source_is_target=source_is_target,
        target_filenames=target_filenames,
    )
    return updated


def test_maybe_update_renamed_uses_original_name(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Looks up the row by original_test_name, not the renamed name."""
    updated = _setup_renamed_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=True,
    )
    assert "| S | OldName |" in updated[0]


def test_maybe_update_renamed_kept_uses_but(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Remark uses 'but' when kept and renamed."""
    updated = _setup_renamed_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=True,
    )
    assert "Kept in the same file but renamed test to NewName" in updated[0]


def test_maybe_update_renamed_and_moved_uses_and(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Remark uses 'and' when moved and renamed."""
    updated = _setup_renamed_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=False,
        target_filenames={"NewName": "test_parser_clause_06_01.cpp"},
    )
    expected = ("Moved to test_parser_clause_06_01.cpp"
                " and renamed test to NewName")
    assert expected in updated[0]


def test_maybe_update_same_name_no_rename_remark(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """No rename remark when original_test_name equals test_name."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=True,
    )
    assert "renamed" not in updated[0]


# ---- build_action_remark ---------------------------------------------------


def test_build_action_remark_kept(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'Kept in the same file without any changes' when source_is_target."""
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    result = ct_github.build_action_remark(
        t, source_is_target=True,
    )
    assert result == "Kept in the same file without any changes"


def test_build_action_remark_moved(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'Moved to ...' when target_filename is set."""
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    result = ct_github.build_action_remark(
        t, source_is_target=False, target_filename="foo.cpp",
    )
    assert result == "Moved to foo.cpp"


def test_build_action_remark_kept_and_renamed(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'Kept ... but renamed ...' when kept and renamed."""
    t = ct_helpers.make_test_block(
        "NewName", prefix="test_parser_", clause="6.1",
    )
    t.classification.original_test_name = "OldName"
    result = ct_github.build_action_remark(
        t, source_is_target=True,
    )
    assert result == "Kept in the same file but renamed test to NewName"


def test_build_action_remark_moved_and_renamed(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'Moved ... and renamed ...' when moved and renamed."""
    t = ct_helpers.make_test_block(
        "NewName", prefix="test_parser_", clause="6.1",
    )
    t.classification.original_test_name = "OldName"
    result = ct_github.build_action_remark(
        t, source_is_target=False, target_filename="foo.cpp",
    )
    assert result == "Moved to foo.cpp and renamed test to NewName"


def test_build_action_remark_no_action(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns empty string when not kept and no target filename."""
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    result = ct_github.build_action_remark(
        t, source_is_target=False,
    )
    assert result == ""


def test_build_action_remark_renamed_only(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'renamed to ...' when only renamed with no location info."""
    t = ct_helpers.make_test_block(
        "NewName", prefix="test_parser_", clause="6.1",
    )
    t.classification.original_test_name = "OldName"
    result = ct_github.build_action_remark(
        t, source_is_target=False,
    )
    assert result == "renamed test to NewName"


def test_build_action_remark_kept_suite_renamed(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'Kept ... but suite renamed ...' when suite changed."""
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    t.classification.original_suite_name = "OldSuite"
    t.suite_name = "NewSuite"
    result = ct_github.build_action_remark(
        t, source_is_target=True,
    )
    assert result == "Kept in the same file but renamed suite to NewSuite"


def test_build_action_remark_kept_both_renamed(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'Kept ... but suite renamed ..., renamed ...' for both."""
    t = ct_helpers.make_test_block(
        "NewName", prefix="test_parser_", clause="6.1",
    )
    t.classification.original_test_name = "OldName"
    t.classification.original_suite_name = "OldSuite"
    t.suite_name = "NewSuite"
    result = ct_github.build_action_remark(
        t, source_is_target=True,
    )
    assert result == (
        "Kept in the same file but renamed suite to NewSuite"
        " and test to NewName"
    )


def test_build_action_remark_moved_suite_renamed(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'Moved ... and suite renamed ...' when moved + suite change."""
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    t.classification.original_suite_name = "OldSuite"
    t.suite_name = "NewSuite"
    result = ct_github.build_action_remark(
        t, source_is_target=False, target_filename="foo.cpp",
    )
    assert result == "Moved to foo.cpp and renamed suite to NewSuite"


def test_build_action_remark_moved_both_renamed(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'Moved ... and suite renamed ..., renamed ...' for both."""
    t = ct_helpers.make_test_block(
        "NewName", prefix="test_parser_", clause="6.1",
    )
    t.classification.original_test_name = "OldName"
    t.classification.original_suite_name = "OldSuite"
    t.suite_name = "NewSuite"
    result = ct_github.build_action_remark(
        t, source_is_target=False, target_filename="foo.cpp",
    )
    assert result == (
        "Moved to foo.cpp and renamed suite to NewSuite"
        " and test to NewName"
    )


def test_build_action_remark_suite_renamed_only(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns 'suite renamed ...' when only suite changed, no location."""
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    t.classification.original_suite_name = "OldSuite"
    t.suite_name = "NewSuite"
    result = ct_github.build_action_remark(
        t, source_is_target=False,
    )
    assert result == "renamed suite to NewSuite"


def test_maybe_update_with_commit_url(
    monkeypatch: pytest.MonkeyPatch,
    ct_github: ModuleType,
    ct_helpers: ModuleType,
) -> None:
    """Action remark is a markdown link when commit_url is provided."""
    updated = _setup_maybe_update(
        monkeypatch, ct_github, ct_helpers, source_is_target=False,
        target_filenames={"T": "test_parser_clause_06_01.cpp"},
        commit_url="https://github.com/org/repo/commit/abc",
    )
    assert (
        "[Moved to test_parser_clause_06_01.cpp]"
        "(https://github.com/org/repo/commit/abc)"
    ) in updated[0]


def test_build_action_remark_with_commit_url(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns markdown link when commit_url is provided."""
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    result = ct_github.build_action_remark(
        t, source_is_target=False, target_filename="foo.cpp",
        commit_url="https://github.com/org/repo/commit/abc123",
    )
    assert result == (
        "[Moved to foo.cpp]"
        "(https://github.com/org/repo/commit/abc123)"
    )


def test_build_action_remark_no_commit_url(
    ct_github: ModuleType, ct_helpers: ModuleType,
) -> None:
    """Returns plain text when commit_url is empty."""
    t = ct_helpers.make_test_block("T", prefix="test_parser_", clause="6.1")
    result = ct_github.build_action_remark(
        t, source_is_target=False, target_filename="foo.cpp",
        commit_url="",
    )
    assert result == "Moved to foo.cpp"
