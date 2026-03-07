"""Unit tests for run-flow functions in classify_file."""

import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

from lib.python.test_fixtures import capture_help_output
from lib.python.test_fixtures.subprocess_stubs import spy_subprocess_run


# ---- Shared helpers --------------------------------------------------------


_BASE_ARGV = [
    "prog", "--file", "f.cpp",
    "--output-dir", "/out",
    "--lrm", "/lrm.txt",
    "--issue", "99",
    "--organization", "testorg",
    "--repo", "testrepo",
    "--max-lines", "1000",
]


def _make_args(**overrides):
    """Build a SimpleNamespace with all required args."""
    defaults = {
        "file": "/path/to/test.cpp",
        "output_dir": "/out",
        "lrm": "/lrm.txt",
        "issue": 99,
        "create_issue": False,
        "organization": "testorg",
        "repo": "testrepo",
        "dry_run": False,
        "no_commit": False,
        "max_lines": 1000,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


def _make_run_args(tmp_path, **overrides):
    """Build args for _run with a real test file."""
    defaults = {
        "file": str(tmp_path / "test_input.cpp"),
        "output_dir": str(tmp_path),
        "lrm": str(tmp_path / "lrm.txt"),
        "issue": 99,
        "create_issue": False,
        "organization": "testorg",
        "repo": "testrepo",
        "dry_run": False,
        "no_commit": False,
        "max_lines": 1000,
    }
    defaults.update(overrides)
    return SimpleNamespace(**defaults)


# ---- _parse_args -----------------------------------------------------------


def test_parse_args_file(monkeypatch, cf):
    """Parses --file flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().file == "f.cpp"


def test_parse_args_output_dir(monkeypatch, cf):
    """Parses --output-dir flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().output_dir == "/out"


def test_parse_args_lrm(monkeypatch, cf):
    """Parses --lrm flag."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().lrm == "/lrm.txt"


def test_parse_args_prog_name(monkeypatch, cf, capsys):
    """Usage line shows 'classify_file' as program name."""
    assert "classify_file" in capture_help_output(
        getattr(cf, "_parse_args"), monkeypatch, capsys,
    )


def test_parse_args_issue(monkeypatch, cf):
    """Parses --issue as integer."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--issue", "42"],
    )
    assert getattr(cf, "_parse_args")().issue == 42


def test_parse_args_create_issue(monkeypatch, cf):
    """Parses --create-issue flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--issue" and v != "--issue"]
    monkeypatch.setattr(
        sys, "argv", [*argv, "--create-issue"],
    )
    assert getattr(cf, "_parse_args")().create_issue is True


def test_parse_args_create_issue_default_false(monkeypatch, cf):
    """Defaults --create-issue to False when --issue is given."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().create_issue is False


def test_parse_args_neither_issue_flag_rejects(monkeypatch, cf):
    """Rejects when neither --issue nor --create-issue is given."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--issue" and v != "--issue"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_both_issue_flags_reject(monkeypatch, cf):
    """Rejects when both --issue and --create-issue are given."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--create-issue"],
    )
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_organization(monkeypatch, cf):
    """Parses --organization flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--organization", "myorg"],
    )
    assert getattr(cf, "_parse_args")().organization == "myorg"


def test_parse_args_organization_required(monkeypatch, cf):
    """Rejects missing --organization flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--organization"
            and v != "--organization"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_repo(monkeypatch, cf):
    """Parses --repo flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--repo", "myrepo"],
    )
    assert getattr(cf, "_parse_args")().repo == "myrepo"


def test_parse_args_repo_required(monkeypatch, cf):
    """Rejects missing --repo flag."""
    argv = [v for i, v in enumerate(_BASE_ARGV)
            if _BASE_ARGV[max(0, i - 1)] != "--repo"
            and v != "--repo"]
    monkeypatch.setattr(sys, "argv", argv)
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_dry_run(monkeypatch, cf):
    """Parses --dry-run flag."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--dry-run"],
    )
    assert getattr(cf, "_parse_args")().dry_run is True


def test_parse_args_dry_run_default(monkeypatch, cf):
    """Defaults --dry-run to False."""
    monkeypatch.setattr(sys, "argv", _BASE_ARGV)
    assert getattr(cf, "_parse_args")().dry_run is False



def test_parse_args_max_lines(monkeypatch, cf):
    """Parses --max-lines as integer."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--max-lines", "500"],
    )
    assert getattr(cf, "_parse_args")().max_lines == 500


def _argv_without_flag(base, flag):
    """Return *base* with *flag* and its value removed."""
    return [v for i, v in enumerate(base)
            if flag not in (base[max(0, i - 1)], v)]


def test_parse_args_max_lines_required(monkeypatch, cf):
    """Rejects missing --max-lines flag."""
    monkeypatch.setattr(
        sys, "argv", _argv_without_flag(_BASE_ARGV, "--max-lines"),
    )
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


def test_parse_args_no_test_flag(monkeypatch, cf):
    """Rejects the --test flag since classify_file does not accept it."""
    monkeypatch.setattr(
        sys, "argv", [*_BASE_ARGV, "--test", "T"],
    )
    with pytest.raises(SystemExit):
        getattr(cf, "_parse_args")()


# ---- _build_command --------------------------------------------------------


def test_build_command_basic(cf):
    """Command starts with python -m classify_test."""
    cmd = getattr(cf, "_build_command")(_make_args(), "T")
    assert cmd[:3] == [sys.executable, "-m", "classify_test"]


def test_build_command_file_flag(cf):
    """Command includes --file with correct value."""
    cmd = getattr(cf, "_build_command")(_make_args(file="/a/b.cpp"), "T")
    assert cmd[cmd.index("--file") + 1] == "/a/b.cpp"


def test_build_command_output_dir_flag(cf):
    """Command includes --output-dir with correct value."""
    cmd = getattr(cf, "_build_command")(_make_args(output_dir="/out"), "T")
    assert cmd[cmd.index("--output-dir") + 1] == "/out"


def test_build_command_lrm_flag(cf):
    """Command includes --lrm with correct value."""
    cmd = getattr(cf, "_build_command")(_make_args(lrm="/lrm.txt"), "T")
    assert cmd[cmd.index("--lrm") + 1] == "/lrm.txt"


def test_build_command_test_flag(cf):
    """Command includes --test with the given test name."""
    cmd = getattr(cf, "_build_command")(_make_args(), "FooBar")
    assert cmd[cmd.index("--test") + 1] == "FooBar"


def test_build_command_issue_included(cf):
    """Command includes --issue with correct value."""
    cmd = getattr(cf, "_build_command")(_make_args(issue=42), "T")
    assert cmd[cmd.index("--issue") + 1] == "42"


def test_build_command_organization_included(cf):
    """Command includes --organization."""
    cmd = getattr(cf, "_build_command")(_make_args(), "T")
    assert cmd[cmd.index("--organization") + 1] == "testorg"


def test_build_command_repo_included(cf):
    """Command includes --repo."""
    cmd = getattr(cf, "_build_command")(_make_args(), "T")
    assert cmd[cmd.index("--repo") + 1] == "testrepo"


def test_build_command_dry_run_included(cf):
    """Command includes --dry-run when set."""
    cmd = getattr(cf, "_build_command")(_make_args(dry_run=True), "T")
    assert "--dry-run" in cmd


def test_build_command_dry_run_omitted(cf):
    """Command omits --dry-run when not set."""
    cmd = getattr(cf, "_build_command")(_make_args(), "T")
    assert "--dry-run" not in cmd


def test_build_command_no_commit_included(cf):
    """Command includes --no-commit when set."""
    cmd = getattr(cf, "_build_command")(_make_args(no_commit=True), "T")
    assert "--no-commit" in cmd


def test_build_command_no_commit_omitted(cf):
    """Command omits --no-commit when not set."""
    cmd = getattr(cf, "_build_command")(_make_args(), "T")
    assert "--no-commit" not in cmd


def test_build_command_max_lines_included(cf):
    """Command includes --max-lines."""
    cmd = getattr(cf, "_build_command")(_make_args(), "T")
    assert cmd[cmd.index("--max-lines") + 1] == "1000"


def test_build_command_max_lines_value(cf):
    """Command passes --max-lines with correct string value."""
    cmd = getattr(cf, "_build_command")(_make_args(max_lines=500), "T")
    assert cmd[cmd.index("--max-lines") + 1] == "500"


# ---- run_classify_test -----------------------------------------------------


def test_run_classify_test_returns_true_on_success(monkeypatch, cf, cf_helpers):
    """Returns True when subprocess exits with 0."""
    cf_helpers.stub_subprocess_success(monkeypatch)
    assert cf.run_classify_test(
        _make_args(), "T", 1, 1,
    ) is True


def test_run_classify_test_returns_false_on_failure(monkeypatch, cf, cf_helpers):
    """Returns False when subprocess exits with non-zero."""
    cf_helpers.stub_subprocess_failure(monkeypatch)
    assert cf.run_classify_test(
        _make_args(), "T", 1, 1,
    ) is False


def test_run_classify_test_prints_progress(monkeypatch, cf, cf_helpers, capsys):
    """Prints progress line with index and name."""
    cf_helpers.stub_subprocess_success(monkeypatch)
    cf.run_classify_test(_make_args(), "Alpha", 3, 10)
    assert "Processing test 3/10: Alpha\n" in capsys.readouterr().out


def test_run_classify_test_passes_test_name(monkeypatch, cf, cf_helpers):
    """Subprocess receives --test with the correct name."""
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf.run_classify_test(_make_args(), "FooBar", 1, 1)
    assert captured[0][captured[0].index("--test") + 1] == "FooBar"


def test_run_classify_test_does_not_capture_output(monkeypatch, cf):
    """Subprocess inherits stdout/stderr (no capture_output)."""
    kwargs_log = spy_subprocess_run(monkeypatch)
    cf.run_classify_test(_make_args(), "T", 1, 1)
    assert "capture_output" not in kwargs_log[0]


# ---- build_issue_body ------------------------------------------------------


def test_build_issue_body_table_header(cf):
    """Body contains the table header row."""
    assert "| Test | Status | Remarks |" in cf.build_issue_body(
        ["A", "B", "C"],
    )


def test_build_issue_body_rows(cf):
    """Body contains table rows for each test name."""
    body = cf.build_issue_body(["Alpha", "Beta"])
    assert "| Alpha | Unreviewed | |" in body


def test_build_issue_body_single_test(cf):
    """Body works correctly with a single test."""
    assert "| Only | Unreviewed | |" in cf.build_issue_body(["Only"])


def test_build_issue_body_no_summary_heading(cf):
    """Body does not contain Summary heading."""
    assert "## Summary" not in cf.build_issue_body(["A"])


def test_build_issue_body_no_tests_heading(cf):
    """Body does not contain Tests heading."""
    assert "## Tests" not in cf.build_issue_body(["A"])


# ---- create_issue ----------------------------------------------------------


def test_create_issue_calls_gh_api_post(monkeypatch, cf, cf_helpers):
    """Invokes gh api with POST method and correct endpoint."""
    captured = cf_helpers.stub_create_issue(monkeypatch, 42)
    cf.create_issue(
        _make_args(file="/p/test_foo.cpp"), ["A"],
    )
    assert "-X" in captured[0]["cmd"]


def test_create_issue_returns_number(monkeypatch, cf, cf_helpers):
    """Returns the issue number from the API response."""
    cf_helpers.stub_create_issue(monkeypatch, 77)
    result = cf.create_issue(
        _make_args(file="/p/test_foo.cpp"), ["A"],
    )
    assert result == 77


def test_create_issue_prints_confirmation(monkeypatch, cf, cf_helpers, capsys):
    """Prints confirmation with the created issue number."""
    cf_helpers.stub_create_issue(monkeypatch, 42)
    cf.create_issue(
        _make_args(file="/p/test_foo.cpp"), ["A"],
    )
    assert "Created issue #42" in capsys.readouterr().out


def test_create_issue_exits_on_failure(monkeypatch, cf, cf_helpers):
    """Exits when gh api returns non-zero."""
    cf_helpers.stub_subprocess_failure(monkeypatch)
    with pytest.raises(SystemExit):
        cf.create_issue(
            _make_args(file="/p/test_foo.cpp"), ["A"],
        )


# ---- _run ------------------------------------------------------------------


def test_run_file_not_found(tmp_path, cf):
    """Returns cleanly when input file does not exist."""
    args = _make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
        create_issue=True, issue=None,
    )
    assert getattr(cf, "_run")(args) is None


def test_run_missing_file_prints_not_found(tmp_path, cf, capsys):
    """Missing file prints 'not found' message to stdout."""
    getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
        create_issue=True, issue=None,
    ))
    assert "not found" in capsys.readouterr().out


def test_run_missing_file_with_issue_closes_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Missing file + --issue → close_issue called."""
    log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
    ))
    assert len(log) == 1


def test_run_missing_file_with_issue_returns(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Missing file + --issue → returns without SystemExit."""
    cf_helpers.stub_close_issue(monkeypatch)
    assert getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
    )) is None


def test_run_missing_file_with_create_issue_returns(tmp_path, cf):
    """Missing file + --create-issue → returns without SystemExit."""
    assert getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
        create_issue=True, issue=None,
    )) is None


def test_run_no_tests_with_issue_deletes_file(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue → file is deleted."""
    f = cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert not f.exists()


def test_run_no_tests_with_issue_closes_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue → close_issue called."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(log) == 1


def test_run_no_tests_with_issue_returns(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue → returns without SystemExit."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_close_issue(monkeypatch)
    assert getattr(cf, "_run")(_make_run_args(tmp_path)) is None


def test_run_no_tests_with_create_issue_deletes_file(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --create-issue → file is deleted."""
    f = cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, create_issue=True, issue=None,
    ))
    assert not f.exists()


def test_run_no_tests_with_create_issue_returns(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --create-issue → returns without SystemExit."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    assert getattr(cf, "_run")(_make_run_args(
        tmp_path, create_issue=True, issue=None,
    )) is None


def test_run_no_tests_prints_deleting(
    tmp_path, capsys, monkeypatch, cf, cf_helpers,
):
    """Empty file → stdout explains why file is being deleted."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert "because it contains no tests" in capsys.readouterr().out


def test_run_no_tests_prints_deleted(
    tmp_path, capsys, monkeypatch, cf, cf_helpers,
):
    """Empty file → stdout contains 'Deleted'."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert "Deleted" in capsys.readouterr().out


def test_run_no_tests_with_issue_commits_deletion(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue → commit_and_push called with deleted filepath."""
    cf_helpers.make_test_file(tmp_path, "")
    log = []
    monkeypatch.setattr(
        cf, "commit_and_push",
        lambda changed, deleted, msg: log.append((changed, deleted, msg)),
    )
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(log) == 1


def _run_empty_file_skip_commit(tmp_path, monkeypatch, cf, cf_helpers, **kw):
    """Shared setup: empty file with commit_and_push stubbed out."""
    cf_helpers.make_test_file(tmp_path, "")
    log = []
    monkeypatch.setattr(
        cf, "commit_and_push",
        lambda changed, deleted, msg: log.append(1),
    )
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path, **kw))
    return log


def test_run_no_tests_with_issue_dry_run_skips_commit(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue + --dry-run → commit_and_push not called."""
    log = _run_empty_file_skip_commit(
        tmp_path, monkeypatch, cf, cf_helpers, dry_run=True,
    )
    assert len(log) == 0


def test_run_no_tests_with_issue_no_commit_skips_commit(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Empty file + --issue + --no-commit → commit_and_push not called."""
    log = _run_empty_file_skip_commit(
        tmp_path, monkeypatch, cf, cf_helpers, no_commit=True,
    )
    assert len(log) == 0


def test_run_all_succeed(tmp_path, monkeypatch, cf, cf_helpers):
    """Does not exit when all tests succeed."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    cf_helpers.make_test_file(tmp_path, body)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(captured) == 2


def test_run_some_fail_exits(tmp_path, monkeypatch, cf, cf_helpers):
    """Exits when any test fails."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\n"
    cf_helpers.make_test_file(tmp_path, body)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_mixed(monkeypatch, {"B"})
    with pytest.raises(SystemExit):
        getattr(cf, "_run")(_make_run_args(tmp_path))


def test_run_stops_after_failure(tmp_path, monkeypatch, cf, cf_helpers):
    """Stops immediately when a test fails."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\nTEST(S, C) {\n}\n"
    cf_helpers.make_test_file(tmp_path, body)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    captured = cf_helpers.stub_subprocess_mixed(monkeypatch, {"A"})
    try:
        getattr(cf, "_run")(_make_run_args(tmp_path))
    except SystemExit:
        pass
    assert len(captured) == 1


def test_run_invokes_per_test(tmp_path, monkeypatch, cf, cf_helpers):
    """Invokes classify_test once per test name."""
    body = "TEST(S, A) {\n}\nTEST(S, B) {\n}\nTEST(S, C) {\n}\n"
    cf_helpers.make_test_file(tmp_path, body)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(captured) == 3


def test_run_closes_issue_on_success(tmp_path, monkeypatch, cf, cf_helpers):
    """Closes issue when all tests succeed."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_success(monkeypatch)
    log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(log) == 1


def test_run_skips_close_on_failure(tmp_path, monkeypatch, cf, cf_helpers):
    """Does not close issue when tests fail."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_failure(monkeypatch)
    log = cf_helpers.stub_close_issue(monkeypatch)
    try:
        getattr(cf, "_run")(_make_run_args(tmp_path))
    except SystemExit:
        pass
    assert len(log) == 0


def test_run_skips_close_on_dry_run(tmp_path, monkeypatch, cf, cf_helpers):
    """Does not close issue in dry-run mode."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_success(monkeypatch)
    log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path, dry_run=True))
    assert len(log) == 0


def test_run_close_reason_all_classified(
    tmp_path, monkeypatch, cf, cf_helpers, capsys,
):
    """Closes with 'all tests have been classified' on success."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_success(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert "because all tests have been classified" \
           in capsys.readouterr().out


def test_run_close_reason_no_tests(
    tmp_path, monkeypatch, cf, cf_helpers, capsys,
):
    """Closes with 'the file has no tests' when file is empty."""
    cf_helpers.make_test_file(tmp_path, "")
    monkeypatch.setattr(cf, "commit_and_push", lambda *a: None)
    cf_helpers.stub_subprocess_success(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert "because the file has no tests" in capsys.readouterr().out


def test_run_close_reason_file_missing(
    tmp_path, monkeypatch, cf, cf_helpers, capsys,
):
    """Closes with 'the source file no longer exists' when missing."""
    cf_helpers.stub_subprocess_success(monkeypatch)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, file=str(tmp_path / "missing.cpp"),
    ))
    assert "because the source file no longer exists" \
           in capsys.readouterr().out


def _stub_create_and_run(
    cf, cf_helpers, tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch, **run_overrides: object,
) -> tuple[list[bool], list[list[str]]]:
    """Stub create_issue, subprocess, and close_issue; run pipeline."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    create_log: list[bool] = []
    def fake_create(_a: object, _n: object) -> int:
        create_log.append(True)
        return 42

    monkeypatch.setattr(cf, "create_issue", fake_create)
    cf_helpers.stub_sync_issue_rows(monkeypatch)
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path, **run_overrides))
    return create_log, captured


def test_run_creates_issue_when_flag_set(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Calls create_issue when --create-issue is set."""
    create_log, _ = _stub_create_and_run(
        cf, cf_helpers, tmp_path, monkeypatch,
        issue=None, create_issue=True,
    )
    assert len(create_log) == 1


def test_run_sets_issue_from_creation(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Subprocess commands use the issue number from create_issue."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    monkeypatch.setattr(cf, "create_issue", lambda _a, _n: 77)
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, issue=None, create_issue=True,
    ))
    assert captured[0][captured[0].index("--issue") + 1] == "77"


def test_run_skips_create_when_issue_given(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Does not call create_issue when --issue is provided."""
    create_log, _ = _stub_create_and_run(
        cf, cf_helpers, tmp_path, monkeypatch,
    )
    assert len(create_log) == 0


# ---- main ------------------------------------------------------------------


def test_main_calls_run(monkeypatch, cf):
    """Calls _run with parsed args."""
    ran = []
    monkeypatch.setattr(cf, "_run", lambda args: ran.append(True))
    monkeypatch.setattr(cf, "_parse_args", _make_args)
    cf.main()
    assert ran == [True]


def test_main_enables_line_buffering(monkeypatch, cf):
    """Reconfigures stdout to line-buffered mode."""
    configured = []
    original = sys.stdout.reconfigure

    def mock_reconfigure(**kwargs):
        configured.append(kwargs)
        return original(**kwargs)

    monkeypatch.setattr(sys.stdout, "reconfigure", mock_reconfigure)
    monkeypatch.setattr(cf, "_run", lambda _: None)
    monkeypatch.setattr(cf, "_parse_args", _make_args)
    cf.main()
    assert any(k.get("line_buffering") for k in configured)


# ---- sync_issue_rows -------------------------------------------------------


def _stub_github(monkeypatch, cf, body):
    """Stub fetch_issue_body and capture update_issue_body calls."""
    monkeypatch.setattr(
        cf, "fetch_issue_body",
        lambda _o, _r, _i: body,
    )
    updates: list[str] = []
    monkeypatch.setattr(
        cf, "update_issue_body",
        lambda _o, _r, _i, b: updates.append(b),
    )
    return updates


def test_sync_issue_rows_all_unreviewed_no_update(monkeypatch, cf):
    """Does not call update when all rows are already Unreviewed."""
    body = "| Alpha | Unreviewed | |\n| Beta | Unreviewed | |\n"
    updates = _stub_github(monkeypatch, cf, body)
    cf.sync_issue_rows(_make_args(), ["Alpha", "Beta"])
    assert len(updates) == 0


def test_sync_issue_rows_all_unreviewed_returns_empty(monkeypatch, cf):
    """Returns empty set when all rows are Unreviewed."""
    body = "| Alpha | Unreviewed | |\n| Beta | Unreviewed | |\n"
    _stub_github(monkeypatch, cf, body)
    assert cf.sync_issue_rows(_make_args(), ["Alpha", "Beta"]) == set()


def test_sync_issue_rows_adds_missing_row(monkeypatch, cf):
    """Adds an Unreviewed row for a missing test."""
    body = "| Alpha | Unreviewed | |\n"
    updates = _stub_github(monkeypatch, cf, body)
    cf.sync_issue_rows(_make_args(), ["Alpha", "Beta"])
    assert "| Beta | Unreviewed | |" in updates[0]


def test_sync_issue_rows_missing_returns_empty(monkeypatch, cf):
    """Returns empty set when only missing tests are added."""
    body = "| Alpha | Unreviewed | |\n"
    _stub_github(monkeypatch, cf, body)
    assert cf.sync_issue_rows(_make_args(), ["Alpha", "Beta"]) == set()


def test_sync_issue_rows_preserves_other_reviewed(monkeypatch, cf):
    """Leaves reviewed rows for tests not in test_names."""
    body = (
        "| Other | Reviewed but kept in the same file | |\n"
        "| Alpha | Unreviewed | |\n"
    )
    updates = _stub_github(monkeypatch, cf, body)
    cf.sync_issue_rows(_make_args(), ["Alpha"])
    assert len(updates) == 0


def test_sync_issue_rows_returns_reviewed(monkeypatch, cf):
    """Returns reviewed test names."""
    body = (
        "| Alpha | Reviewed but kept in the same file | |\n"
        "| Beta | Unreviewed | |\n"
    )
    _stub_github(monkeypatch, cf, body)
    result = cf.sync_issue_rows(_make_args(), ["Alpha", "Beta"])
    assert result == {"Alpha"}


def test_sync_issue_rows_returns_moved(monkeypatch, cf):
    """Returns moved test names."""
    body = (
        "| Alpha | Reviewed but moved to another file | target.cpp |\n"
        "| Beta | Unreviewed | |\n"
    )
    _stub_github(monkeypatch, cf, body)
    result = cf.sync_issue_rows(_make_args(), ["Alpha", "Beta"])
    assert result == {"Alpha"}


def test_sync_issue_rows_mixed_returns_reviewed(monkeypatch, cf):
    """Returns reviewed names when mixed with missing tests."""
    body = "| Alpha | Reviewed but kept in the same file | |\n"
    _stub_github(monkeypatch, cf, body)
    result = cf.sync_issue_rows(
        _make_args(), ["Alpha", "Beta"],
    )
    assert result == {"Alpha"}


def test_sync_issue_rows_mixed_adds_missing(monkeypatch, cf):
    """Adds missing test row when mixed with reviewed tests."""
    body = "| Alpha | Reviewed but kept in the same file | |\n"
    updates = _stub_github(monkeypatch, cf, body)
    cf.sync_issue_rows(_make_args(), ["Alpha", "Beta"])
    assert "| Beta | Unreviewed | |" in updates[0]


# ---- _run + sync_issue_rows ------------------------------------------------


def test_run_calls_sync_issue_rows_with_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Calls sync_issue_rows when --issue is provided."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    log = cf_helpers.stub_sync_issue_rows(monkeypatch)
    cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    assert len(log) == 1


def test_run_skips_sync_issue_rows_with_create_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Does not call sync_issue_rows when --create-issue is used."""
    cf_helpers.make_test_file(tmp_path, "TEST(S, A) {\n}\n")
    log = cf_helpers.stub_sync_issue_rows(monkeypatch)
    monkeypatch.setattr(cf, "create_issue", lambda _a, _n: 42)
    cf_helpers.stub_subprocess_success(monkeypatch)
    cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(
        tmp_path, issue=None, create_issue=True,
    ))
    assert len(log) == 0


def _run_with_reviewed(tmp_path, monkeypatch, cf, cf_helpers, *,
                       body, reviewed):
    """Run _run() with sync_issue_rows returning *reviewed*."""
    cf_helpers.make_test_file(tmp_path, body)
    monkeypatch.setattr(
        cf, "sync_issue_rows", lambda _a, _n: reviewed,
    )
    captured = cf_helpers.stub_subprocess_success(monkeypatch)
    log = cf_helpers.stub_close_issue(monkeypatch)
    getattr(cf, "_run")(_make_run_args(tmp_path))
    return captured, log


def test_run_skips_reviewed_tests_count(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Only invokes classify_test for unreviewed tests."""
    captured, _ = _run_with_reviewed(
        tmp_path, monkeypatch, cf, cf_helpers,
        body="TEST(S, A) {\n}\nTEST(S, B) {\n}\n", reviewed={"A"},
    )
    assert len(captured) == 1


def test_run_skips_reviewed_tests_name(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Invokes classify_test for the unreviewed test only."""
    captured, _ = _run_with_reviewed(
        tmp_path, monkeypatch, cf, cf_helpers,
        body="TEST(S, A) {\n}\nTEST(S, B) {\n}\n", reviewed={"A"},
    )
    assert "B" in " ".join(captured[0])


def test_run_all_reviewed_skips_classify(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Does not invoke classify_test when all tests are reviewed."""
    captured, _ = _run_with_reviewed(
        tmp_path, monkeypatch, cf, cf_helpers,
        body="TEST(S, A) {\n}\n", reviewed={"A"},
    )
    assert len(captured) == 0


def test_run_all_reviewed_closes_issue(
    tmp_path, monkeypatch, cf, cf_helpers,
):
    """Closes issue when all tests are already reviewed."""
    _, log = _run_with_reviewed(
        tmp_path, monkeypatch, cf, cf_helpers,
        body="TEST(S, A) {\n}\n", reviewed={"A"},
    )
    assert len(log) == 1
