"""Unit tests for GitHub integration functions in classify_test."""

import subprocess
import sys
from types import SimpleNamespace
from unittest.mock import MagicMock

import pytest

import classify_test
from classify_test._github import (
    _validate_issue_args,
    build_issue_comment,
    maybe_post_issue_comment,
    post_issue_comment,
)
from helpers import make_test_block as _tb

_parse_args = getattr(classify_test, "_parse_args")


# ---- _parse_args (issue/organization/repo) ---------------------------------


def test_parse_args_issue(monkeypatch):
    """Parses --issue flag as integer."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T", "--issue", "42"],
    )
    assert _parse_args().issue == 42


def test_parse_args_issue_default(monkeypatch):
    """--issue defaults to None."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T"],
    )
    assert _parse_args().issue is None


def test_parse_args_organization(monkeypatch):
    """Parses --organization flag."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T",
         "--organization", "myorg"],
    )
    assert _parse_args().organization == "myorg"


def test_parse_args_organization_default(monkeypatch):
    """--organization defaults to None."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T"],
    )
    assert _parse_args().organization is None


def test_parse_args_repo(monkeypatch):
    """Parses --repo flag."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T",
         "--repo", "myrepo"],
    )
    assert _parse_args().repo == "myrepo"


def test_parse_args_repo_default(monkeypatch):
    """--repo defaults to None."""
    monkeypatch.setattr(
        sys, "argv",
        ["prog", "--file", "f.cpp", "--output-dir", "/out",
         "--lrm", "/lrm.txt", "--test", "T"],
    )
    assert _parse_args().repo is None


# ---- build_issue_comment ---------------------------------------------------


def test_build_issue_comment_includes_header():
    """Comment includes a markdown header."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    assert "###" in build_issue_comment([t])


def test_build_issue_comment_includes_test_name():
    """Comment includes the test name with parentheses."""
    t = _tb("MyTest", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    assert "MyTest()" in build_issue_comment([t])


def test_build_issue_comment_includes_clause():
    """Comment includes the formatted clause."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    assert "\u00a76.1" in build_issue_comment([t])


def test_build_issue_comment_includes_rationale():
    """Comment includes the rationale text."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "Important reason"
    assert "Important reason" in build_issue_comment([t])


def test_build_issue_comment_no_rationale_omits_indent():
    """No indented rationale line when rationale is empty."""
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = ""
    comment = build_issue_comment([t])
    assert not any(line.startswith("  -") for line in comment.splitlines())


def test_build_issue_comment_non_lrm_clause():
    """Non-LRM clause displays as Non-LRM TAG."""
    t = _tb("T", prefix="test_non_lrm_", clause="non-lrm:aig")
    t.rationale = "r"
    assert "Non-LRM AIG" in build_issue_comment([t])


def test_build_issue_comment_multiple_tests():
    """Comment includes all tests when given multiple."""
    t1 = _tb("Alpha", prefix="test_parser_", clause="6.1")
    t1.rationale = "r1"
    t2 = _tb("Beta", prefix="test_lexer_", clause="5.3")
    t2.rationale = "r2"
    comment = build_issue_comment([t1, t2])
    assert "Alpha()" in comment and "Beta()" in comment


# ---- post_issue_comment ----------------------------------------------------


def _capture_gh_cmd(monkeypatch):
    """Run post_issue_comment and return the captured subprocess command."""
    captured = []
    mock_result = MagicMock()
    mock_result.returncode = 0
    mock_result.stdout = ""
    mock_result.stderr = ""

    def capture_run(cmd, **_kwargs):
        captured.extend(cmd)
        return mock_result

    monkeypatch.setattr(subprocess, "run", capture_run)
    post_issue_comment("myorg", "myrepo", 42, "test body")
    return captured


def test_post_issue_comment_calls_gh(monkeypatch):
    """Calls gh CLI for issue commenting."""
    cmd = _capture_gh_cmd(monkeypatch)
    assert cmd[0] == "gh"


def test_post_issue_comment_includes_repo(monkeypatch):
    """Command includes --repo org/repo."""
    cmd = _capture_gh_cmd(monkeypatch)
    idx = cmd.index("--repo")
    assert cmd[idx + 1] == "myorg/myrepo"


def test_post_issue_comment_includes_issue_number(monkeypatch):
    """Command includes the issue number."""
    cmd = _capture_gh_cmd(monkeypatch)
    assert "42" in cmd


def test_post_issue_comment_includes_body(monkeypatch):
    """Command includes --body with the comment text."""
    cmd = _capture_gh_cmd(monkeypatch)
    idx = cmd.index("--body")
    assert cmd[idx + 1] == "test body"


def test_post_issue_comment_failure_exits(monkeypatch):
    """Exits on non-zero return code."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "auth error"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    with pytest.raises(SystemExit):
        post_issue_comment("org", "repo", 42, "body")


def test_post_issue_comment_failure_message(monkeypatch, capsys):
    """Error message mentions the issue number."""
    mock_result = MagicMock()
    mock_result.returncode = 1
    mock_result.stdout = ""
    mock_result.stderr = "auth error"
    monkeypatch.setattr(
        subprocess, "run", lambda *_a, **_kw: mock_result,
    )
    try:
        post_issue_comment("org", "repo", 99, "body")
    except SystemExit:
        pass
    assert "99" in capsys.readouterr().err


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


# ---- maybe_post_issue_comment ----------------------------------------------


def test_maybe_post_no_issue_does_nothing(monkeypatch):
    """No posting when --issue is not set."""
    posted = []
    monkeypatch.setattr(
        "classify_test._github.post_issue_comment",
        lambda org, repo, issue, body: posted.append(True),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    maybe_post_issue_comment(_issue_args(), [t])
    assert not posted


def test_maybe_post_with_issue_calls_post(monkeypatch):
    """Posts when --issue is set."""
    posted = []
    monkeypatch.setattr(
        "classify_test._github.post_issue_comment",
        lambda org, repo, issue, body: posted.append(True),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=42, organization="org", repo="repo")
    maybe_post_issue_comment(args, [t])
    assert len(posted) == 1


def test_maybe_post_passes_correct_org(monkeypatch):
    """Passes the organization to post_issue_comment."""
    posted = []
    monkeypatch.setattr(
        "classify_test._github.post_issue_comment",
        lambda org, repo, issue, body: posted.append(org),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=42, organization="myorg", repo="repo")
    maybe_post_issue_comment(args, [t])
    assert posted[0] == "myorg"


def test_maybe_post_passes_correct_repo(monkeypatch):
    """Passes the repo to post_issue_comment."""
    posted = []
    monkeypatch.setattr(
        "classify_test._github.post_issue_comment",
        lambda org, repo, issue, body: posted.append(repo),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=42, organization="org", repo="myrepo")
    maybe_post_issue_comment(args, [t])
    assert posted[0] == "myrepo"


def test_maybe_post_passes_correct_issue(monkeypatch):
    """Passes the issue number to post_issue_comment."""
    posted = []
    monkeypatch.setattr(
        "classify_test._github.post_issue_comment",
        lambda org, repo, issue, body: posted.append(issue),
    )
    t = _tb("T", prefix="test_parser_", clause="6.1")
    t.rationale = "r"
    args = _issue_args(issue=99, organization="org", repo="repo")
    maybe_post_issue_comment(args, [t])
    assert posted[0] == 99
